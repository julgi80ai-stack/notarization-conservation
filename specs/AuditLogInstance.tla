------------------------- MODULE AuditLogInstance -------------------------
(***************************************************************************)
(* Phase 3.1 (L2-breadth): a SECOND, independent member of the abstract     *)
(* label-independent notarization class (Notarization.tla) -- a             *)
(* hash-chained append-only AUDIT LOG (Certificate Transparency /           *)
(* Schneier-Kelsey forward-integrity style).                               *)
(*                                                                         *)
(* The point of this module is to turn the paper's "breadth claim" into a    *)
(* breadth THEOREM: the class is inhabited by at least two structurally      *)
(* unrelated systems (Morpheus's three-surface governance pipeline AND a    *)
(* generic tamper-evident log), so the impossibility is a class law, not a  *)
(* one-robot artifact.                                                      *)
(*                                                                         *)
(* Domain reading:                                                         *)
(*   Entries  log records (events appended to the append-only log)          *)
(*   Subjects subject-identity / personal-data keys (the corr labels)       *)
(*   NoSubj   "no key" marker (an erased / unkeyed record) = Bot            *)
(*   subj     the actual labeling  Entries -> Subjects \cup {NoSubj}        *)
(*   height   the hash-chain position of a record (prev-hash depth)         *)
(*   Logged   the committed / finalized frontier = the action-log frontier G *)
(*                                                                         *)
(* Two re-linking surfaces:                                                 *)
(*   "Chain"   position link: record x precedes/seals record y when         *)
(*             height[x] =< height[y].  Reads height, NOT subj  =>  LI.      *)
(*   "Subject" key-equality link: shared non-erased subject.  Reads subj    *)
(*             =>  NOT LI (the unique key-dependent surface here).           *)
(*                                                                         *)
(* Bounds: NONE.  Entries, Subjects arbitrary (possibly infinite).          *)
(***************************************************************************)
EXTENDS Naturals, TLAPS

CONSTANTS Entries, Subjects, NoSubj, Logged, subj, height

ASSUME NoSubjFresh == NoSubj \notin Subjects
ASSUME LoggedInE   == Logged \subseteq Entries
ASSUME SubjType    == subj   \in [Entries -> Subjects \cup {NoSubj}]
ASSUME HeightType  == height \in [Entries -> Nat]
ASSUME EntriesNE   == Entries  # {}
ASSUME SubjectsNE  == Subjects # {}

----------------------------------------------------------------------------
AuditSurfaces == {"Chain", "Subject"}

\* Both surfaces range over all appended records.
AuditMem(S) == Entries

\* Surface relation UNDER a labeling l.
\*   Chain   : position link, height-ordered.  l is IGNORED  =>  label-indep.
\*   Subject : shared non-erased subject key.  l is READ      =>  label-dep.
AuditRel(S, l) ==
   CASE S = "Chain"   -> { p \in AuditMem("Chain") \X AuditMem("Chain") :
                             height[p[1]] =< height[p[2]] }
     [] S = "Subject" -> { p \in AuditMem("Subject") \X AuditMem("Subject") :
                             l[p[1]] = l[p[2]] /\ l[p[1]] # NoSubj }

----------------------------------------------------------------------------
\* The instance.  Named (A!) to avoid clashing with anything.
A == INSTANCE Notarization
       WITH E   <- Entries,   L   <- Subjects,  Bot <- NoSubj,
            Surfaces <- AuditSurfaces,
            Mem <- AuditMem,   Rel <- AuditRel,
            G   <- Logged,     lbl <- subj

----------------------------------------------------------------------------
(***************************************************************************)
(* SURFACE CLASSIFICATION.  The structural fact that makes a tamper-evident *)
(* log a member of the class: the chain is label-independent, the subject    *)
(* index is not.                                                            *)
(***************************************************************************)
THEOREM Chain_LabelIndep == A!LabelIndep("Chain")
  BY DEF A!LabelIndep, AuditRel

\* The subject index genuinely READS the label: two labelings differ.
THEOREM Subject_NotLabelIndep == ~ A!LabelIndep("Subject")
  <1> PICK s0 \in Subjects : TRUE BY SubjectsNE
  <1> DEFINE l1 == [e \in Entries |-> s0]
             l2 == [e \in Entries |-> NoSubj]
  <1>0. s0 # NoSubj BY NoSubjFresh
  <1>1. l1 \in A!Labelings /\ l2 \in A!Labelings
    BY DEF A!Labelings
  <1>2. PICK x \in Entries : TRUE BY EntriesNE
  <1>3. <<x, x>> \in AuditRel("Subject", l1)
    BY <1>2, <1>0 DEF AuditRel, AuditMem
  <1>4. <<x, x>> \notin AuditRel("Subject", l2)
    BY <1>2 DEF AuditRel, AuditMem
  <1>5. AuditRel("Subject", l1) # AuditRel("Subject", l2)
    BY <1>3, <1>4
  <1>6. QED BY <1>1, <1>5 DEF A!LabelIndep

----------------------------------------------------------------------------
(***************************************************************************)
(* IMPOSSIBILITY in audit-log language.  A record r appended at or after a   *)
(* committed entry g is chain-linked to g; g is in the frontier, so r is in  *)
(* the closure -- r is NOT separated.  In words: in a total-accountability   *)
(* tamper-evident log, no appended record can be "non-established" (kept     *)
(* outside the established/attributed set), because the chain re-links it.   *)
(***************************************************************************)
THEOREM AppendCannotSeparate ==
  ASSUME NEW g \in Logged, NEW r \in Entries, height[g] =< height[r]
  PROVE  ~ A!Sep(r)
  <1>1. g \in Entries BY LoggedInE
  <1>2. g \in AuditMem("Chain") /\ r \in AuditMem("Chain")
    BY <1>1 DEF AuditMem
  <1>3. <<g, r>> \in AuditRel("Chain", subj)
    BY <1>2 DEF AuditRel
  <1>4. "Chain" \in AuditSurfaces BY DEF AuditSurfaces
  <1>5. r \in A!Reach
    <2> SUFFICES ASSUME NEW X \in SUBSET Entries, Logged \subseteq X,
                        A!ClosedUnder(X)
                 PROVE  r \in X
        BY DEF A!Reach
    <2>1. g \in X BY <1>1
    <2>2. A!Edge(g, r) BY <1>3, <1>4 DEF A!Edge
    <2>3. QED BY <2>1, <2>2, <1>1 DEF A!ClosedUnder
  <1>6. QED BY <1>5 DEF A!Sep

----------------------------------------------------------------------------
(***************************************************************************)
(* THE RIGHT-TO-BE-FORGOTTEN CONFLICT, MACHINE-PROVEN.                       *)
(* Erasing record r's subject key (Strip -> NoSubj) does NOT remove the      *)
(* chain link, because the chain is label-independent (reads height, not the *)
(* subject).  So the erased record stays reachable from the committed        *)
(* frontier: GDPR-style erasure is futile against an immutable hash chain.   *)
(* This is the abstract DecisiveLI / KeyDropFailsOnLI, concretely.           *)
(***************************************************************************)
THEOREM ErasureFutile ==
  ASSUME NEW g \in Logged, NEW r \in Entries, height[g] =< height[r]
  PROVE  <<g, r>> \in AuditRel("Chain", A!Strip(subj, r))
  <1>1. g \in Entries BY LoggedInE
  <1>2. g \in AuditMem("Chain") /\ r \in AuditMem("Chain")
    BY <1>1 DEF AuditMem
  \* Chain's relation syntactically ignores its labeling argument, so the
  \* stripped labeling yields exactly the same height-ordered set.
  <1>3. QED BY <1>2 DEF AuditRel

==========================================================================
