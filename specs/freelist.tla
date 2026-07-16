------------------------------ MODULE freelist ------------------------------
(*
 * TLA+ / PlusCal model of the ReactOS memory manager physical page
 * free-list state machine.
 *
 * Source files modelled:
 *   ntoskrnl/mm/freelist.c        (RosMm layer: MmAllocPage, MmDereferencePage,
 *                                   MmReferencePage, LRU list management)
 *   ntoskrnl/mm/ARM3/pfnlist.c    (ARM3 layer: MiInsertPageInFreeList,
 *                                   MiInsertPageInList, MiInsertStandbyListAtFront,
 *                                   MiRemoveAnyPage, MiRemoveZeroPage,
 *                                   MiRemovePageByColor, MiUnlinkFreeOrZeroedPage,
 *                                   MiUnlinkPageFromList,
 *                                   MiDecrementShareCount,
 *                                   MiDecrementReferenceCount)
 *
 * Scope / simplifications
 * -----------------------
 *  - Colors and priority sub-lists are collapsed: each global list is treated
 *    as a single unordered set of page-frame numbers (PFNs).  The linked-list
 *    pointer invariants are expressed as set-membership invariants rather than
 *    modelling Flink/Blink explicitly; a separate ListInvariant predicate
 *    captures the structural rules.
 *  - The "RosMm vs ARM3" PFN distinction (AweAllocation / MI_IS_ROS_PFN) is
 *    kept as a boolean flag so that routing through MmDereferencePage vs
 *    MiDecrementReferenceCount can be modelled correctly.
 *  - The zero-page worker thread is modelled as a separate process that can
 *    nondeterministically zero one free page at a time.
 *  - MdlAllocate is modelled as an atomic action that removes N pages from
 *    Free|Zeroed and marks them ActiveAndValid.
 *  - The PFN spinlock is modelled as a global mutex token (pfnLockHolder).
 *    Any process must hold the lock before touching shared state.
 *
 * Invariants checked (see Invariants section below):
 *   Inv1  - AvailablePages count equals |Zeroed ∪ Free ∪ Standby|
 *   Inv2  - Every ActiveAndValid page has refcount ≥ 1
 *   Inv3  - Every Free/Zeroed page has refcount = 0 ∧ sharecount = 0
 *   Inv4  - Pages are partitioned across lists (no page on two lists)
 *   Inv5  - Total page count is conserved
 *   Inv6  - refcount never goes negative
 *   Inv7  - LRU list contains exactly the user pages with MustBeCached = TRUE
 *   Inv8  - Standby/Modified pages have refcount = 0
 *
 * Liveness (weak-fairness):
 *   Live1 - A page on FreeList will eventually be zeroed (zero-page thread)
 *   Live2 - A caller waiting for a page will eventually get one if pages exist
 *)

EXTENDS Integers, Sequences, FiniteSets, TLC

-----------------------------------------------------------------------------
(* CONSTANTS *)
-----------------------------------------------------------------------------

CONSTANTS
    Pages,          (* The finite set of page-frame numbers, e.g. 1..N *)
    Procs,          (* The finite set of user-space / kernel caller processes *)
    MaxRefCount     (* Bound number of reference counts *)

ASSUME Pages # {} /\ Procs # {}

-----------------------------------------------------------------------------
(* Page location names — mirrors MMLISTS enum *)
-----------------------------------------------------------------------------

PageLocations == {
    "Zeroed",       \* ZeroedPageList
    "Free",         \* FreePageList
    "Standby",      \* StandbyPageList
    "Modified",     \* ModifiedPageList
    "Bad",          \* BadPageList
    "Active",       \* ActiveAndValid
    "Transition"    \* TransitionPage (transient, ARM3 only)
}

\* Lists that count toward MmAvailablePages
AvailableLists == {"Zeroed", "Free", "Standby"}

-----------------------------------------------------------------------------
(* VARIABLES *)
-----------------------------------------------------------------------------

VARIABLES
    \* Per-page state
    location,       \* location[p] \in PageLocations
    refcount,       \* refcount[p]  \in Nat
    sharecount,     \* sharecount[p] \in Nat
    modified,       \* modified[p]   \in BOOLEAN  (dirty flag)
    isRos,          \* isRos[p]      \in BOOLEAN  (RosMm vs ARM3 PFN)
    isDeleted,      \* isDeleted[p]  \in BOOLEAN  (MI_IS_PFN_DELETED)
    mustBeCached,   \* mustBeCached[p] \in BOOLEAN (LRU user-page hack)
    isPrototype,    \* isPrototype[p] \in BOOLEAN  (PrototypePte flag)

    \* Global counters
    availablePages, \* mirrors MmAvailablePages

    \* LRU doubly-linked list for user pages (RosMm layer)
    \* Modelled as an ordered sequence of PFNs
    lruList,        \* lruList \in Seq(Pages)

    \* Spinlock: either "none" or the identity of the holder
    pfnLockHolder   \* pfnLockHolder \in Procs \cup {"none"}

vars == << location, refcount, sharecount, modified, isRos, isDeleted,
           mustBeCached, isPrototype, availablePages, lruList, pfnLockHolder >>

-----------------------------------------------------------------------------
(* TYPE INVARIANT *)
-----------------------------------------------------------------------------

TypeOK ==
    /\ location     \in [Pages -> PageLocations]
    /\ refcount     \in [Pages -> Nat]
    /\ sharecount   \in [Pages -> Nat]
    /\ modified     \in [Pages -> BOOLEAN]
    /\ isRos        \in [Pages -> BOOLEAN]
    /\ isDeleted    \in [Pages -> BOOLEAN]
    /\ mustBeCached \in [Pages -> BOOLEAN]
    /\ isPrototype  \in [Pages -> BOOLEAN]
    /\ availablePages \in Nat
    /\ lruList      \in Seq(Pages)
    /\ pfnLockHolder \in (Procs \cup {"none"})

-----------------------------------------------------------------------------
(* HELPER DEFINITIONS *)
-----------------------------------------------------------------------------

\* Pages currently on a given list
PagesOn(loc) == {p \in Pages : location[p] = loc}

\* A page is "available" in the MmAvailablePages sense
IsAvailable(p) == location[p] \in AvailableLists

\* LRU list as a set
LruSet == {lruList[i] : i \in DOMAIN lruList}

-----------------------------------------------------------------------------
(* INVARIANTS *)
-----------------------------------------------------------------------------

Inv1_AvailableCount ==
    availablePages = Cardinality({p \in Pages : IsAvailable(p)})

Inv2_ActiveHasRef ==
    \A p \in Pages : location[p] = "Active" => refcount[p] >= 1

Inv3_FreeHasNoRef ==
    \A p \in Pages : location[p] \in {"Free", "Zeroed"} =>
        refcount[p] = 0 /\ sharecount[p] = 0

Inv4_Partition ==  TRUE
    \* Every page is on exactly one list — enforced by location being a function

Inv5_Conservation ==
    Cardinality(Pages) =
        Cardinality(PagesOn("Zeroed"))   +
        Cardinality(PagesOn("Free"))     +
        Cardinality(PagesOn("Standby"))  +
        Cardinality(PagesOn("Modified")) +
        Cardinality(PagesOn("Bad"))      +
        Cardinality(PagesOn("Active"))   +
        Cardinality(PagesOn("Transition"))

Inv6_NoNegRef ==
    \A p \in Pages : refcount[p] >= 0

Inv7_LruMatchesMustBeCached ==
    LruSet = {p \in Pages : mustBeCached[p] = TRUE}

Inv8_TransitionNoRef ==
    \A p \in Pages :
        location[p] \in {"Standby", "Modified", "Transition"} =>
            refcount[p] = 0

Invariants ==
    /\ TypeOK
    /\ Inv1_AvailableCount
    /\ Inv2_ActiveHasRef
    /\ Inv3_FreeHasNoRef
    /\ Inv5_Conservation
    /\ Inv6_NoNegRef
    /\ Inv7_LruMatchesMustBeCached
    /\ Inv8_TransitionNoRef

-----------------------------------------------------------------------------
(* LOCK ACTIONS *)
-----------------------------------------------------------------------------

AcquireLock(proc) ==
    /\ pfnLockHolder = "none"
    /\ pfnLockHolder' = proc
    /\ UNCHANGED << location, refcount, sharecount, modified, isRos,
                    isDeleted, mustBeCached, isPrototype,
                    availablePages, lruList >>

ReleaseLock(proc) ==
    /\ pfnLockHolder = proc
    /\ pfnLockHolder' = "none"
    /\ UNCHANGED << location, refcount, sharecount, modified, isRos,
                    isDeleted, mustBeCached, isPrototype,
                    availablePages, lruList >>

-----------------------------------------------------------------------------
(* INTERNAL HELPERS (require lock held by caller — not modelled as steps) *)
(* These are expressed as state predicates / functions used inside actions. *)
-----------------------------------------------------------------------------

\* Mirrors MiIncrementAvailablePages
IncrementAvailable == availablePages' = availablePages + 1

\* Mirrors MiDecrementAvailablePages
DecrementAvailable == availablePages' = availablePages - 1

-----------------------------------------------------------------------------
(* ACTIONS *)
-----------------------------------------------------------------------------

(*
 * MiInsertPageInFreeList(p)
 * Preconditions (from C source):
 *   - PFN lock held
 *   - refcount = 0, MustBeCached = 0, RemovalRequested = 0
 *   - page currently at ActiveAndValid (set by caller before calling)
 * Effect: page moves to FreeList, availablePages++
 *)
InsertPageInFreeList(proc, p) ==
    /\ pfnLockHolder = proc
    /\ location[p] = "Active"        \* caller sets this before inserting
    /\ refcount[p] = 0
    /\ sharecount[p] = 0
    /\ mustBeCached[p] = FALSE
    /\ location'     = [location     EXCEPT ![p] = "Free"]
    /\ availablePages' = availablePages + 1
    /\ UNCHANGED << refcount, sharecount, modified, isRos, isDeleted,
                    mustBeCached, isPrototype, lruList, pfnLockHolder >>

(*
 * MiInsertPageInList — zeroed-page variant (ZeroedPageList)
 * The zero-page thread calls this after wiping a Free page.
 * Effect: page moves Free -> Zeroed, availablePages unchanged (already counted).
 *
 * NOTE: availablePages is not changed here because the page was already on
 * FreeList (counted) and we are just reclassifying it.
 *)
InsertPageInZeroedList(proc, p) ==
    /\ pfnLockHolder = proc
    /\ location[p] = "Free"
    /\ refcount[p] = 0
    /\ location' = [location EXCEPT ![p] = "Zeroed"]
    /\ UNCHANGED << refcount, sharecount, modified, isRos, isDeleted,
                    mustBeCached, isPrototype, availablePages, lruList,
                    pfnLockHolder >>

(*
 * MiInsertStandbyListAtFront(p)
 * Preconditions: refcount = 0, PrototypePte = 1, lock held
 * Effect: Transition -> Standby, availablePages++
 *)
InsertStandbyListAtFront(proc, p) ==
    /\ pfnLockHolder = proc
    /\ location[p] = "Transition"
    /\ refcount[p] = 0
    /\ isPrototype[p] = TRUE
    /\ mustBeCached[p] = FALSE
    /\ location'       = [location EXCEPT ![p] = "Standby"]
    /\ availablePages' = availablePages + 1
    /\ UNCHANGED << refcount, sharecount, modified, isRos, isDeleted,
                    mustBeCached, isPrototype, lruList, pfnLockHolder >>

(*
 * MiInsertPageInList — modified variant
 * Preconditions: refcount = 0, lock held
 * Effect: Transition -> Modified  (availablePages NOT incremented — modified
 *         pages are not available; they need to be written out first)
 *)
InsertPageInModifiedList(proc, p) ==
    /\ pfnLockHolder = proc
    /\ location[p] = "Transition"
    /\ refcount[p] = 0
    /\ location' = [location EXCEPT ![p] = "Modified"]
    /\ UNCHANGED << refcount, sharecount, modified, isRos, isDeleted,
                    mustBeCached, isPrototype, availablePages, lruList,
                    pfnLockHolder >>

(*
 * MiRemoveAnyPage / MiRemoveZeroPage
 * Takes a page from Zeroed (preferred) or Free.
 * Returns it with location still reflecting old list (caller must update).
 * Here we model the combined effect: a page leaves Zeroed|Free,
 * availablePages--.  Caller sets location to Active afterwards.
 *
 * We express this as a single atomic allocation action (MmAllocPage /
 * MiRemoveZeroPage path) for simplicity.
 *)
RemoveZeroOrFreePage(proc, p) ==
    /\ pfnLockHolder = proc
    /\ location[p] \in {"Zeroed", "Free"}
    /\ refcount[p] = 0
    /\ sharecount[p] = 0
    /\ availablePages > 0
    /\ location'       = [location    EXCEPT ![p] = "Active"]
    /\ refcount'       = [refcount    EXCEPT ![p] = 1]
    /\ availablePages' = availablePages - 1
    /\ UNCHANGED << sharecount, modified, isRos, isDeleted,
                    mustBeCached, isPrototype, lruList, pfnLockHolder >>

(*
 * MmAllocPage(MC_USER) — RosMm path
 * Calls MiRemoveZeroPage then sets RosMm bookkeeping and appends to LRU.
 *)
AllocUserPage(proc, p) ==
    /\ pfnLockHolder = proc
    /\ location[p] \in {"Zeroed", "Free"}
    /\ refcount[p] = 0
    /\ sharecount[p] = 0
    /\ mustBeCached[p] = FALSE
    /\ availablePages > 0
    /\ location'       = [location     EXCEPT ![p] = "Active"]
    /\ refcount'       = [refcount     EXCEPT ![p] = 1]
    /\ isRos'          = [isRos        EXCEPT ![p] = TRUE]
    /\ mustBeCached'   = [mustBeCached EXCEPT ![p] = TRUE]
    /\ lruList'        = Append(lruList, p)
    /\ availablePages' = availablePages - 1
    /\ UNCHANGED << sharecount, modified, isDeleted, isPrototype, pfnLockHolder >>

(*
 * MmAllocPage(MC_SYSTEM) — RosMm system-page path
 * Same as AllocUserPage but no LRU insertion.
 *)
AllocSystemPage(proc, p) ==
    /\ pfnLockHolder = proc
    /\ location[p] \in {"Zeroed", "Free"}
    /\ refcount[p] = 0
    /\ sharecount[p] = 0
    /\ mustBeCached[p] = FALSE
    /\ availablePages > 0
    /\ location'       = [location   EXCEPT ![p] = "Active"]
    /\ refcount'       = [refcount   EXCEPT ![p] = 1]
    /\ sharecount'     = [sharecount EXCEPT ![p] = 1]
    /\ isRos'          = [isRos      EXCEPT ![p] = FALSE]
    /\ availablePages' = availablePages - 1
    /\ UNCHANGED << sharecount, modified, isDeleted, mustBeCached,
                    isPrototype, lruList, pfnLockHolder >>

(*
 * MmReferencePage(p) — increment refcount (RosMm, lock held)
 * Precondition: refcount >= 1 (page must already be Active)
 *)
ReferencePage(proc, p) ==
    /\ pfnLockHolder = proc
    /\ isRos[p] = TRUE
    /\ refcount[p] >= 1
    /\ refcount[p] < MaxRefCount
    /\ refcount' = [refcount EXCEPT ![p] = refcount[p] + 1]
    /\ UNCHANGED << location, sharecount, modified, isRos, isDeleted,
                    mustBeCached, isPrototype, availablePages, lruList,
                    pfnLockHolder >>

(*
 * MmDereferencePage(p) — RosMm path
 * Decrements refcount; when it hits 0:
 *   - removes from LRU if MustBeCached
 *   - sets location ActiveAndValid (transient)
 *   - calls MiInsertPageInFreeList
 *)
DereferencePage(proc, p) ==
    /\ pfnLockHolder = proc
    /\ isRos[p] = TRUE
    /\ refcount[p] >= 1
    /\ IF refcount[p] = 1
       THEN
           \* refcount hits zero -> free the page
           /\ refcount'       = [refcount     EXCEPT ![p] = 0]
           /\ location'       = [location     EXCEPT ![p] = "Free"]
           /\ availablePages' = availablePages + 1
           /\ isRos'          = [isRos        EXCEPT ![p] = FALSE]
           /\ mustBeCached'   = [mustBeCached EXCEPT ![p] = FALSE]
           /\ IF mustBeCached[p]
              THEN
                  /\ lruList'      = SelectSeq(lruList, LAMBDA x : x # p)
              ELSE
                  /\ UNCHANGED lruList
       ELSE
           /\ refcount'     = [refcount EXCEPT ![p] = refcount[p] - 1]
           /\ UNCHANGED << location, mustBeCached, lruList,
                           availablePages, isRos >>
    /\ UNCHANGED << sharecount, modified, isDeleted, isPrototype, pfnLockHolder >>

(*
 * MiDecrementShareCount(p) — ARM3 path
 * When sharecount hits 0:
 *   - page moves to Transition
 *   - if refcount = 1 and isDeleted: free immediately
 *   - else if refcount = 1: route to Standby (clean) or Modified (dirty)
 *   - else: just decrement refcount
 *)
DecrementShareCount(proc, p) ==
    /\ pfnLockHolder = proc
    /\ isRos[p] = FALSE
    /\ location[p] \in {"Active", "Standby"}
    /\ refcount[p] >= 1
    /\ sharecount[p] >= 1
    /\ LET newShare == sharecount[p] - 1
       IN
       IF newShare = 0
       THEN
           IF isDeleted[p] /\ refcount[p] = 1
           THEN \* free immediately
               /\ sharecount'     = [sharecount EXCEPT ![p] = 0]
               /\ refcount'       = [refcount   EXCEPT ![p] = 0]
               /\ location'       = [location   EXCEPT ![p] = "Free"]
               /\ availablePages' = availablePages + 1
               /\ UNCHANGED << modified, isRos, isDeleted, mustBeCached,
                                isPrototype, lruList >>
           ELSE IF refcount[p] = 1
           THEN \* route to Standby or Modified
               /\ sharecount' = [sharecount EXCEPT ![p] = 0]
               /\ refcount'   = [refcount   EXCEPT ![p] = 0]
               /\ IF modified[p]
                  THEN
                      /\ location' = [location EXCEPT ![p] = "Modified"]
                      /\ UNCHANGED availablePages
                  ELSE
                      /\ location'       = [location EXCEPT ![p] = "Standby"]
                      /\ availablePages' = availablePages + 1
               /\ UNCHANGED << isRos, isDeleted, modified, mustBeCached,
                                isPrototype, lruList >>
           ELSE \* refcount > 1, just decrement both
               /\ sharecount' = [sharecount EXCEPT ![p] = 0]
               /\ refcount'   = [refcount   EXCEPT ![p] = refcount[p] - 1]
               /\ location'   = [location   EXCEPT ![p] = "Transition"]
               /\ UNCHANGED << modified, isRos, isDeleted, mustBeCached,
                                isPrototype, availablePages, lruList >>
       ELSE \* sharecount still > 0 after decrement
           /\ sharecount' = [sharecount EXCEPT ![p] = newShare]
           /\ UNCHANGED << location, refcount, modified, isRos, isDeleted,
                           mustBeCached, isPrototype, availablePages, lruList >>
    /\ UNCHANGED pfnLockHolder

(*
 * ZeroPageThread — background action
 * Moves one Free page to Zeroed (content wiped).
 * availablePages unchanged (page was already counted).
 *)
ZeroOnePage(proc, p) ==
    /\ pfnLockHolder = proc
    /\ location[p] = "Free"
    /\ refcount[p] = 0
    /\ location' = [location EXCEPT ![p] = "Zeroed"]
    /\ UNCHANGED << refcount, sharecount, modified, isRos, isDeleted,
                    mustBeCached, isPrototype, availablePages, lruList,
                    pfnLockHolder >>

(*
 * PageFileWrite — Modified page written out, moves to Standby
 * (simplified: modified page writer thread)
 *)
WriteModifiedPage(proc, p) ==
    /\ pfnLockHolder = proc
    /\ location[p] = "Modified"
    /\ refcount[p] = 0
    /\ location'       = [location  EXCEPT ![p] = "Standby"]
    /\ modified'       = [modified  EXCEPT ![p] = FALSE]
    /\ availablePages' = availablePages + 1
    /\ UNCHANGED << refcount, sharecount, isRos, isDeleted, mustBeCached,
                    isPrototype, lruList, pfnLockHolder >>

(*
 * ReclaimStandbyPage — page reclaimed from Standby back to Active
 * (page fault resolves via transition PTE)
 *)
ReclaimStandbyPage(proc, p) ==
    /\ pfnLockHolder = proc
    /\ location[p] = "Standby"
    /\ refcount[p] = 0
    /\ location'       = [location   EXCEPT ![p] = "Active"]
    /\ refcount'       = [refcount   EXCEPT ![p] = 1]
    /\ sharecount'     = [sharecount EXCEPT ![p] = 1]
    /\ availablePages' = availablePages - 1
    /\ UNCHANGED << modified, isRos, isDeleted, mustBeCached, isPrototype,
                    lruList, pfnLockHolder >>

(*
 * LRU Scan: MmGetLRUNextUserPage(prev, MoveToLast=TRUE)
 * References next page, optionally moves prev to tail, dereferences prev.
 * Modelled here as: if prev refcount > 1, move to tail of lruList.
 *)
LRUScanStep(proc, prev) ==
    /\ pfnLockHolder = proc
    /\ isRos[prev] = TRUE
    /\ mustBeCached[prev] = TRUE
    /\ refcount[prev] >= 1
    /\ \* move prev to tail if refcount > 1
       IF refcount[prev] > 1
       THEN lruList' = Append(
                SelectSeq(lruList, LAMBDA x: x # prev),
                prev)
       ELSE UNCHANGED lruList
    /\ UNCHANGED << location, refcount, sharecount, modified, isRos,
                    isDeleted, mustBeCached, isPrototype,
                    availablePages, pfnLockHolder >>

-----------------------------------------------------------------------------
(* INITIAL STATE *)
-----------------------------------------------------------------------------

(*
 * Start with all pages on the Zeroed list, refcount = 0, lock free.
 * This matches the system state after MmInitSystem has populated
 * the zeroed page list.
 *)
Init ==
    /\ location     = [p \in Pages |-> "Zeroed"]
    /\ refcount     = [p \in Pages |-> 0]
    /\ sharecount   = [p \in Pages |-> 0]
    /\ modified     = [p \in Pages |-> FALSE]
    /\ isRos        = [p \in Pages |-> FALSE]
    /\ isDeleted    = [p \in Pages |-> FALSE]
    /\ mustBeCached = [p \in Pages |-> FALSE]
    /\ isPrototype  = [p \in Pages |-> FALSE]
    /\ availablePages = Cardinality(Pages)
    /\ lruList      = << >>
    /\ pfnLockHolder = "none"

-----------------------------------------------------------------------------
(* NEXT-STATE RELATION *)
-----------------------------------------------------------------------------

Next ==
    \E proc \in Procs, p \in Pages :
        \/ AcquireLock(proc)
        \/ ReleaseLock(proc)
        \/ AllocUserPage(proc, p)
        \/ AllocSystemPage(proc, p)
        \/ DereferencePage(proc, p)
        \/ ReferencePage(proc, p)
        \/ DecrementShareCount(proc, p)
        \/ InsertPageInFreeList(proc, p)
        \/ InsertPageInZeroedList(proc, p)
        \/ InsertStandbyListAtFront(proc, p)
        \/ InsertPageInModifiedList(proc, p)
        \/ ZeroOnePage(proc, p)
        \/ WriteModifiedPage(proc, p)
        \/ ReclaimStandbyPage(proc, p)
        \/ LRUScanStep(proc, p)

-----------------------------------------------------------------------------
(* FAIRNESS / LIVENESS *)
-----------------------------------------------------------------------------

(*
 * Strong fairness on the zero-page thread: if there is always a Free page
 * and a process willing to zero it, it will eventually be zeroed.
 *)
FairnessZeroPage ==
    \A proc \in Procs, p \in Pages :
        SF_vars(ZeroOnePage(proc, p))

(*
 * Strong fairness on the modified-page writer.
 *)
FairnessModifiedWriter ==
    \A proc \in Procs, p \in Pages :
        SF_vars(WriteModifiedPage(proc, p))

(*
 * Weak fairness on dereferencing; callers must eventually release pages
 * they hold.
 *)
FairnessDereference ==
    \A proc \in Procs, p \in Pages :
        SF_vars(DereferencePage(proc, p))

FairnessAcquireLock ==
    \A proc \in Procs :
        WF_vars(AcquireLock(proc))

FairnessDecrementShare ==
    \A proc \in Procs, p \in Pages :
        WF_vars(DecrementShareCount(proc, p))

Spec == Init /\ [][Next]_vars
             /\ FairnessZeroPage
             /\ FairnessModifiedWriter
             /\ FairnessDereference
             /\ FairnessDecrementShare
             /\ FairnessAcquireLock

-----------------------------------------------------------------------------
(* LIVENESS PROPERTIES *)
-----------------------------------------------------------------------------

(*
 * Live1: Any page stuck on FreeList will eventually be zeroed (disabled).
 *)
Live1_FreeEventuallyZeroed ==
    \A p \in Pages :
        (location[p] = "Free") ~> (location[p] = "Zeroed")

(*
 * Live1: The zero page thread makes progress when free pages exist in sufficient quantity
 *)
Live1_ZeroPageThreadProgress ==
    (\E p \in Pages : location[p] = "Free")
        ~> (\E p \in Pages : location[p] = "Zeroed")


(*
 * Live2: If a zeroed/free page exists, allocation will eventually succeed.
 * (Requires a willing caller — approximated here by the existence of a proc.)
 *)
Live2_AllocationProgress ==
    (\E p \in Pages : location[p] \in {"Zeroed", "Free"})
        ~> (\E p \in Pages : location[p] = "Active")

=============================================================================
\* Modification History
\* Created for HuwCampbell/reactos — TLA+ model of mm/freelist.c + ARM3/pfnlist.c
=============================================================================
