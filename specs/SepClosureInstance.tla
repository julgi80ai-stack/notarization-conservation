----------------------- MODULE SepClosureInstance -----------------------
(***************************************************************************)
(* Phase 2.5 / 2.6: Morpheus (SepClosureTwoMachines) as an INSTANCE of the  *)
(* abstract notarization class (Notarization.tla).                         *)
(*                                                                         *)
(* The abstract frame is STATIC (fixed G, lbl, Rel; Reach = closure) while  *)
(* the TLC model is DYNAMIC (emitted/linked grow under Next).  A CONSTANT    *)
(* cannot be substituted by a state-dependent expression, so we take an      *)
(* arbitrary STATIC SNAPSHOT `Emitted` (a constant set of events) and        *)
(* instantiate the class over it.  The surface relations are exactly the     *)
(* threat operations J1/J2/J4 frozen at that snapshot.                      *)
(*                                                                         *)
(* Deliverables:                                                           *)
(*   2.5  the substitution discharges the abstract ASSUMEs (instance        *)
(*        obligations) AND classifies the surfaces:                        *)
(*           LabelIndep("J1"), LabelIndep("J2"), ~LabelIndep("J4").         *)
(*        => Morpheus IS a member of the class; J4 is the unique            *)
(*           key-equality (label-DEPENDENT) surface.                       *)
(*   2.6  inhabitation: a non-degenerate witness so the class theorems are  *)
(*        not vacuous on this instance.                                     *)
(***************************************************************************)
EXTENDS SepClosureTwoMachines, TLAPS

\* An arbitrary static snapshot of the bus history, plus non-degeneracy.
CONSTANT Emitted
ASSUME EmittedType  == Emitted \subseteq EventIds
ASSUME CorrNonEmpty == CorrIDs # {}
ASSUME EventsExist  == EventIds # {}

----------------------------------------------------------------------------
\* Static re-statement of the sealing-pipeline membership over the snapshot.
PipeS(e) == e \in Emitted
            /\ (Kind(e) = "ACTION" \/ (Kind(e) = "REFLEX" /\ Machine = "ACCT"))

MorphSurfaces == {"J1", "J2", "J4"}

\* Surface membership.  J1/J2 live on the sealing pipeline; J4 (pure key
\* traversal) is surface-independent, so every event is a potential member.
MorphMem(S) == CASE S = "J2" -> { e \in EventIds : PipeS(e) }
                 [] S = "J1" -> { e \in EventIds : PipeS(e) }
                 [] S = "J4" -> EventIds

\* Surface relation UNDER a labeling l.  J1/J2 do not read l (co-membership
\* on the pipeline); J4 reads l (shared non-NONE key).  The "x already in the
\* frontier" guard of the TLC joins is absorbed into the abstract closure
\* Reach, so the relations here are the raw co-link relations.
MorphRel(S, l) ==
   CASE S = "J2" -> IF EnableByTime
                     THEN MorphMem("J2") \X MorphMem("J2") ELSE {}
     [] S = "J1" -> IF EnableByPosition
                     THEN MorphMem("J1") \X MorphMem("J1") ELSE {}
     [] S = "J4" -> { p \in MorphMem("J4") \X MorphMem("J4") :
                        l[p[1]] = l[p[2]] /\ l[p[1]] # NONE }

\* The actual labeling and action-log frontier of the snapshot.
MorphLbl == [ e \in EventIds |-> CorrAssign(e) ]
MorphG   == Emitted \cap Actions

----------------------------------------------------------------------------
\* The instance.  Named (N!) to avoid clashing with Morpheus's own `Sep`.
N == INSTANCE Notarization
       WITH E   <- EventIds,  L   <- CorrIDs,    Bot <- NONE,
            Surfaces <- MorphSurfaces,
            Mem <- MorphMem,   Rel <- MorphRel,
            G   <- MorphG,     lbl <- MorphLbl

----------------------------------------------------------------------------
\* Helper: ACorr is a genuine (non-NONE) correlation key.
LEMMA ACorrGood == ACorr \in CorrIDs /\ ACorr # NONE
  <1>1. ACorr \in CorrIDs BY CorrNonEmpty DEF ACorr
  <1>2. QED BY <1>1, NoneNotCorr

\* CorrAssign always lands in CorrIDs \cup {NONE}.
LEMMA CorrAssignType ==
  ASSUME NEW e \in EventIds PROVE CorrAssign(e) \in CorrIDs \cup {NONE}
  BY ACorrGood DEF CorrAssign

LEMMA MorphLblType == MorphLbl \in [EventIds -> CorrIDs \cup {NONE}]
  BY CorrAssignType DEF MorphLbl

----------------------------------------------------------------------------
(***************************************************************************)
(* 2.5  SURFACE CLASSIFICATION.  This is the structural fact that makes      *)
(* Morpheus a member of the abstract class.                                 *)
(***************************************************************************)
THEOREM J2_LabelIndep == N!LabelIndep("J2")
  BY DEF N!LabelIndep, MorphRel

THEOREM J1_LabelIndep == N!LabelIndep("J1")
  BY DEF N!LabelIndep, MorphRel

\* J4 genuinely READS the label: two labelings yield different relations.
THEOREM J4_NotLabelIndep == ~ N!LabelIndep("J4")
  <1> DEFINE l1 == [e \in EventIds |-> ACorr]
             l2 == [e \in EventIds |-> NONE]
  <1>1. l1 \in N!Labelings /\ l2 \in N!Labelings
    BY ACorrGood DEF N!Labelings
  <1>2. PICK x \in EventIds : TRUE BY EventsExist
  <1>3. <<x, x>> \in MorphRel("J4", l1)
    BY <1>2, ACorrGood DEF MorphRel, MorphMem
  <1>4. <<x, x>> \notin MorphRel("J4", l2)
    BY <1>2, NoneNotCorr DEF MorphRel, MorphMem
  <1>5. MorphRel("J4", l1) # MorphRel("J4", l2)
    BY <1>3, <1>4
  <1>6. QED BY <1>1, <1>5 DEF N!LabelIndep

----------------------------------------------------------------------------
(***************************************************************************)
(* 2.6  INHABITATION / class-applies-to-instance.  A non-degenerate ACCT     *)
(* snapshot: an action a and reflex r both sealed on the hash chain (J1).    *)
(* The abstract impossibility then fires -- r is NOT separated -- and, by    *)
(* the decisive lemma, stripping r's correlation key does NOT help (J1 is    *)
(* label-independent).  This is exactly the paper's point that the          *)
(* accountability vertex cannot achieve NE even by dropping the key.         *)
(***************************************************************************)
THEOREM AcctCannotSeparate ==
  ASSUME Machine = "ACCT", EnableByPosition = TRUE,
         NEW a \in Actions, NEW r \in Reflexes,
         a \in Emitted, r \in Emitted
  PROVE  ~ N!Sep(r)
  <1>1. a \in MorphG BY DEF MorphG
  <1>2. r \in EventIds BY DEF EventIds
  <1>3. "J1" \in MorphSurfaces BY DEF MorphSurfaces
  <1>4. a \in MorphMem("J1") /\ r \in MorphMem("J1")
    \* a is an ACTION on the pipeline; r is a REFLEX on the pipeline under ACCT
    BY DisjointKinds DEF MorphMem, PipeS, Kind, EventIds
  <1>5. <<a, r>> \in MorphRel("J1", MorphLbl)
    BY <1>4 DEF MorphRel
  \* The abstract impossibility, instantiated: a is in the frontier, a--r is a
  \* J1 edge, so r is in the closure Reach -- i.e. NOT separated.  (Same one
  \* step as N!ColocBreaksSep, re-derived through the instance's own Reach.)
  <1>6. r \in N!Reach
    <2> SUFFICES ASSUME NEW X \in SUBSET EventIds, MorphG \subseteq X,
                        N!ClosedUnder(X)
                 PROVE  r \in X
        BY <1>2 DEF N!Reach
    <2>1. a \in X BY <1>1
    <2>2. N!Edge(a, r) BY <1>3, <1>5 DEF N!Edge
    <2>3. a \in EventIds /\ r \in EventIds BY <1>2 DEF EventIds
    <2>4. QED BY <2>1, <2>2, <2>3 DEF N!ClosedUnder
  <1>7. QED BY <1>6 DEF N!Sep

\* And stripping r's key is futile on the label-independent surface J1.
THEOREM AcctKeyStripFutile ==
  ASSUME Machine = "ACCT", EnableByPosition = TRUE,
         NEW a \in Actions, NEW r \in Reflexes,
         a \in Emitted, r \in Emitted
  PROVE  <<a, r>> \in MorphRel("J1", N!Strip(MorphLbl, r))
  \* J1's relation syntactically ignores its label argument -- this IS J1's
  \* label-independence, concretely: dropping r's key (Strip) cannot change it.
  \* So the co-location -- and thus the failure to separate -- survives.
  <1>1. a \in MorphMem("J1") /\ r \in MorphMem("J1")
    BY DisjointKinds DEF MorphMem, PipeS, Kind, EventIds
  <1>2. QED BY <1>1 DEF MorphRel

==========================================================================
