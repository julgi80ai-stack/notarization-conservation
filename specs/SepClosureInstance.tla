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
(*                                                                         *)
(* M3 (wiring): INSTANCE Synthesis (the whole law inherited), abstract      *)
(* ASSUMEs discharged (the Inst_ lemmas), impossibility proved BY           *)
(* ColocBreaksSep, key-strip futility BY the inherited DecisiveLI,          *)
(* Dichotomy discharged, and the §7.4 dividend row computed                 *)
(* (Morph_LeastExit; Morph_ZeroPrice added in M5-c).                        *)
(*                                                                         *)
(* M5-b (J1/J2 de-duplication): an earlier revision modelled BOTH pipeline  *)
(* surfaces as the full product over pipeline co-membership, making         *)
(* Rel("J1", l) and Rel("J2", l) literally the same set -- so the price 2   *)
(* in Morph_LeastExit counted ONE structure under two names.  J1 is now     *)
(* what the hash chain actually stores: position ADJACENCY (a prev-event    *)
(* pointer, exactly the M4 move on AuditLogInstance's Chain).  J2 (the      *)
(* corr-agnostic store: time-range / event-id co-presence) keeps the        *)
(* co-membership product.  The two relations are now provably DISTINCT      *)
(* (J1_J2_Distinct), so the governance price 2 is a real 2.                 *)
(***************************************************************************)
EXTENDS SepClosureTwoMachines, TLAPS

\* An arbitrary static snapshot of the bus history, plus non-degeneracy.
CONSTANT Emitted
ASSUME EmittedType  == Emitted \subseteq EventIds
ASSUME CorrNonEmpty == CorrIDs # {}
ASSUME EventsExist  == EventIds # {}

\* The chain-position structure of the snapshot: each event's immediate
\* chain predecessor (NoPrev for a genesis / unchained event).  This is
\* what the hash chain stores; transitive linkage is the closure's job.
CONSTANTS prevEv, NoPrev
ASSUME PrevEvType  == prevEv \in [EventIds -> EventIds \cup {NoPrev}]
ASSUME NoPrevFresh == NoPrev \notin EventIds

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

\* Surface relation UNDER a labeling l.  J2 = co-presence in the
\* corr-agnostic store (time-range / event-id: any two pipeline members
\* co-locate); J1 = chain-position ADJACENCY (y's prev-pointer names x --
\* what the chain stores; M5-b, the same move as AuditLogInstance's Chain).
\* Neither reads l.  J4 reads l (shared non-NONE key).  The "x already in
\* the frontier" guard of the TLC joins is absorbed into the abstract
\* closure Reach, so the relations here are the raw co-link relations.
MorphRel(S, l) ==
   CASE S = "J2" -> IF EnableByTime
                     THEN MorphMem("J2") \X MorphMem("J2") ELSE {}
     [] S = "J1" -> IF EnableByPosition
                     THEN { p \in MorphMem("J1") \X MorphMem("J1") :
                              prevEv[p[2]] = p[1] }
                     ELSE {}
     [] S = "J4" -> { p \in MorphMem("J4") \X MorphMem("J4") :
                        l[p[1]] = l[p[2]] /\ l[p[1]] # NONE }

\* The actual labeling and action-log frontier of the snapshot.
MorphLbl == [ e \in EventIds |-> CorrAssign(e) ]
MorphG   == Emitted \cap Actions

\* Non-vacuity: the snapshot has committed at least one action; otherwise
\* Reach = {} and every event separates for free.
ASSUME MorphGNE == MorphG # {}

----------------------------------------------------------------------------
\* The instance.  Named (N!) to avoid clashing with Morpheus's own `Sep`.
\* Synthesis EXTENDS Antagonism EXTENDS Notarization, so N! carries the
\* entire law, theorems included.
N == INSTANCE Synthesis
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
(* DISCHARGE THE ABSTRACT ASSUMEs (the "proof duty" of paper §10).          *)
(***************************************************************************)
LEMMA Inst_BotNotLabel == NONE \notin CorrIDs
  BY NoneNotCorr

LEMMA Inst_G_inE == MorphG \subseteq EventIds
  BY EmittedType DEF MorphG

LEMMA Inst_LblType == MorphLbl \in N!Labelings
  BY MorphLblType DEF N!Labelings

LEMMA Inst_MemType == \A S \in MorphSurfaces : MorphMem(S) \subseteq EventIds
  <1> SUFFICES ASSUME NEW S \in MorphSurfaces
               PROVE  MorphMem(S) \subseteq EventIds
      OBVIOUS
  <1>1. CASE S = "J1" BY <1>1 DEF MorphMem
  <1>2. CASE S = "J2" BY <1>2 DEF MorphMem
  <1>3. CASE S = "J4" BY <1>3 DEF MorphMem
  <1>4. QED BY <1>1, <1>2, <1>3 DEF MorphSurfaces

LEMMA Inst_RelType ==
  \A S \in MorphSurfaces, l \in N!Labelings :
     MorphRel(S, l) \subseteq MorphMem(S) \X MorphMem(S)
  <1> SUFFICES ASSUME NEW S \in MorphSurfaces, NEW l \in N!Labelings
               PROVE  MorphRel(S, l) \subseteq MorphMem(S) \X MorphMem(S)
      OBVIOUS
  <1>1. CASE S = "J1" BY <1>1 DEF MorphRel, MorphMem
  <1>2. CASE S = "J2" BY <1>2 DEF MorphRel, MorphMem
  <1>3. CASE S = "J4" BY <1>3 DEF MorphRel, MorphMem
  <1>4. QED BY <1>1, <1>2, <1>3 DEF MorphSurfaces

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

\* The two label-independent surfaces are genuinely DISTINCT relations
\* (M5-b): any two pipeline members x, y with y's prev-pointer NOT naming x
\* co-locate on the store (J2) but not on the chain (J1).  So the price 2
\* of Morph_LeastExit counts two different structures, not one under two
\* names.
THEOREM J1_J2_Distinct ==
  ASSUME EnableByPosition = TRUE, EnableByTime = TRUE,
         NEW x \in EventIds, NEW y \in EventIds,
         PipeS(x), PipeS(y), prevEv[y] # x
  PROVE  MorphRel("J1", MorphLbl) # MorphRel("J2", MorphLbl)
  <1>1. x \in MorphMem("J2") /\ y \in MorphMem("J2")
    BY DEF MorphMem
  <1>2. <<x, y>> \in MorphRel("J2", MorphLbl)
    BY <1>1 DEF MorphRel
  <1>3. <<x, y>> \notin MorphRel("J1", MorphLbl)
    BY DEF MorphRel, MorphMem
  <1>4. QED BY <1>2, <1>3

----------------------------------------------------------------------------
(***************************************************************************)
(* 2.6  INHABITATION / class-applies-to-instance.  A non-degenerate ACCT     *)
(* snapshot: a reflex r sealed on the hash chain (J1) at the position        *)
(* immediately after a committed action a (r's prev-pointer names a).        *)
(* The abstract impossibility then fires -- r is NOT separated -- and, by    *)
(* the decisive lemma, stripping r's correlation key does NOT help (J1 is    *)
(* label-independent).  This is exactly the paper's point that the          *)
(* accountability vertex cannot achieve NE even by dropping the key.         *)
(* (Deeper chain positions are re-linked hop by hop by the closure.)         *)
(***************************************************************************)
THEOREM AcctCannotSeparate ==
  ASSUME Machine = "ACCT", EnableByPosition = TRUE,
         NEW a \in Actions, NEW r \in Reflexes,
         a \in Emitted, r \in Emitted, prevEv[r] = a
  PROVE  ~ N!Sep(r)
  <1>1. a \in MorphG BY DEF MorphG
  <1>2. r \in EventIds BY DEF EventIds
  <1>3. "J1" \in MorphSurfaces BY DEF MorphSurfaces
  <1>4. a \in MorphMem("J1") /\ r \in MorphMem("J1")
    \* a is an ACTION on the pipeline; r is a REFLEX on the pipeline under ACCT
    BY DisjointKinds DEF MorphMem, PipeS, Kind, EventIds
  <1>5. <<a, r>> \in MorphRel("J1", MorphLbl)
    BY <1>4 DEF MorphRel
  \* The abstract impossibility, INHERITED: a is in the frontier, a--r is a
  \* J1 edge, so N!ColocBreaksSep applies directly -- no local re-derivation
  \* of the closure.
  <1>6. QED BY <1>1, <1>2, <1>3, <1>5, Inst_BotNotLabel, Inst_G_inE,
           Inst_LblType, Inst_MemType, Inst_RelType, N!ColocBreaksSep

\* And stripping r's key is futile on the label-independent surface J1 --
\* via the INHERITED Lemma 1 (DecisiveLI): J1's relation never reads the
\* label, so the stripped labeling yields the SAME relation, link included.
THEOREM AcctKeyStripFutile ==
  ASSUME Machine = "ACCT", EnableByPosition = TRUE,
         NEW a \in Actions, NEW r \in Reflexes,
         a \in Emitted, r \in Emitted, prevEv[r] = a
  PROVE  <<a, r>> \in MorphRel("J1", N!Strip(MorphLbl, r))
  <1>0. r \in EventIds BY DEF EventIds
  <1>1. a \in MorphMem("J1") /\ r \in MorphMem("J1")
    BY DisjointKinds DEF MorphMem, PipeS, Kind, EventIds
  <1>2. <<a, r>> \in MorphRel("J1", MorphLbl) BY <1>1 DEF MorphRel
  <1>3. N!LabelIndep("J1") BY DEF N!LabelIndep, MorphRel
  <1>4. "J1" \in MorphSurfaces BY DEF MorphSurfaces
  <1>5. MorphRel("J1", MorphLbl) = MorphRel("J1", N!Strip(MorphLbl, r))
    BY <1>0, <1>3, <1>4, Inst_BotNotLabel, Inst_G_inE, Inst_LblType,
       Inst_MemType, Inst_RelType, N!DecisiveLI
  <1>6. QED BY <1>2, <1>5

----------------------------------------------------------------------------
(***************************************************************************)
(* DISCHARGE THE KEY-TYPE SPLIT (§7.1), machine-checked for this instance.  *)
(***************************************************************************)
LEMMA AllBotIsBot ==
  ASSUME NEW x \in EventIds PROVE N!AllBot[x] = NONE
  BY DEF N!AllBot

THEOREM Morph_Dichotomy == N!Dichotomy
  <1> SUFFICES ASSUME NEW S \in MorphSurfaces
               PROVE  N!LabelIndep(S) \/ MorphRel(S, N!AllBot) = {}
      BY DEF N!Dichotomy
  <1>1. CASE S = "J1"
    <2>1. N!LabelIndep("J1") BY DEF N!LabelIndep, MorphRel
    <2>2. QED BY <1>1, <2>1
  <1>2. CASE S = "J2"
    <2>1. N!LabelIndep("J2") BY DEF N!LabelIndep, MorphRel
    <2>2. QED BY <1>2, <2>1
  <1>3. CASE S = "J4"
    <2>1. MorphRel("J4", N!AllBot) = {}
      <3> SUFFICES ASSUME NEW p \in MorphRel("J4", N!AllBot) PROVE FALSE
          OBVIOUS
      <3>1. p \in EventIds \X EventIds BY DEF MorphRel, MorphMem
      <3>2. p[1] \in EventIds BY <3>1
      <3>3. N!AllBot[p[1]] # NONE BY DEF MorphRel, MorphMem
      <3>4. QED BY <3>2, <3>3, AllBotIsBot
    <2>2. QED BY <1>3, <2>1
  <1>4. QED BY <1>1, <1>2, <1>3 DEF MorphSurfaces

----------------------------------------------------------------------------
(***************************************************************************)
(* THE §7.4 DIVIDEND ROW, AS A THEOREM.                                     *)
(* "Governance | key-strip futile | exit the sealing pipeline, keep the     *)
(*  parent-key surface"  --  computed, not asserted: at the accountability  *)
(*  vertex (both corr-agnostic sealing surfaces on), the least exit set of  *)
(*  a sealed reflex is EXACTLY the pipeline {J1, J2}; the latent key        *)
(*  traverser J4 costs nothing (it vanishes under the maximal key-drop).    *)
(*  Proposition 1's "exit the pipeline AND drop the key", at per-effect     *)
(*  grain.  Since M5-b the two surfaces are DISTINCT relations              *)
(*  (J1_J2_Distinct): the price 2 counts two real structures.               *)
(***************************************************************************)
THEOREM Morph_LeastExit ==
  ASSUME Machine = "ACCT", EnableByPosition = TRUE, EnableByTime = TRUE,
         NEW a \in Actions, NEW r \in Reflexes,
         a \in Emitted, r \in Emitted, prevEv[r] = a
  PROVE  N!HandlesMinus(N!AllBot, r) = {"J1", "J2"}
  <1>0. r \in EventIds BY DEF EventIds
  <1>1. a \in MorphG BY DEF MorphG
  <1>2. a \in N!ReachExc(N!AllBot, r)
    BY <1>1, Inst_BotNotLabel, Inst_G_inE, Inst_LblType,
       Inst_MemType, Inst_RelType, N!G_sub_ReachExc
  <1>3. a \in MorphMem("J1") /\ r \in MorphMem("J1")
    BY DisjointKinds DEF MorphMem, PipeS, Kind, EventIds
  <1>4. "J1" \in N!HandlesMinus(N!AllBot, r)
    <2>1. <<a, r>> \in MorphRel("J1", N!AllBot) BY <1>3 DEF MorphRel
    <2>2. QED BY <1>2, <2>1 DEF N!HandlesMinus, MorphSurfaces
  <1>5. "J2" \in N!HandlesMinus(N!AllBot, r)
    <2>1. a \in MorphMem("J2") /\ r \in MorphMem("J2")
      BY DisjointKinds DEF MorphMem, PipeS, Kind, EventIds
    <2>2. <<a, r>> \in MorphRel("J2", N!AllBot) BY <2>1 DEF MorphRel
    <2>3. QED BY <1>2, <2>2 DEF N!HandlesMinus, MorphSurfaces
  <1>6. "J4" \notin N!HandlesMinus(N!AllBot, r)
    <2> SUFFICES ASSUME "J4" \in N!HandlesMinus(N!AllBot, r) PROVE FALSE
        OBVIOUS
    <2>1. PICK x \in N!ReachExc(N!AllBot, r) :
            <<x, r>> \in MorphRel("J4", N!AllBot)
        BY DEF N!HandlesMinus
    <2>2. x \in EventIds
      BY <2>1, Inst_BotNotLabel, Inst_G_inE, Inst_LblType,
         Inst_MemType, Inst_RelType, N!ReachExc_inE
    <2>3. N!AllBot[x] # NONE BY <2>1 DEF MorphRel, MorphMem
    <2>4. QED BY <2>2, <2>3, AllBotIsBot
  <1>7. N!HandlesMinus(N!AllBot, r) \subseteq MorphSurfaces
    BY DEF N!HandlesMinus
  <1>8. QED BY <1>4, <1>5, <1>6, <1>7 DEF MorphSurfaces

----------------------------------------------------------------------------
(***************************************************************************)
(* And the zero-price half -- the GOVERNANCE row of the dividend table,     *)
(* literally.  An effect kept OFF the sealing pipeline (the pre-action      *)
(* region: not stored, not chained) has ZERO exit price once the keys are   *)
(* dropped: J1/J2 cannot pin a non-member, and J4 vanishes under the        *)
(* maximal key-drop.  Non-establishment is purchased by pipeline-exit +     *)
(* key-drop and nothing else is owed -- the design dividend of the          *)
(* governance vertex, computed, not asserted.  (Complementing               *)
(* Morph_LeastExit, which prices the ACCT vertex at the full pipeline.)     *)
(***************************************************************************)
THEOREM Morph_ZeroPrice ==
  ASSUME NEW r \in EventIds, ~ PipeS(r)
  PROVE  N!HandlesMinus(N!AllBot, r) = {}
  <1> SUFFICES ASSUME NEW S \in N!HandlesMinus(N!AllBot, r) PROVE FALSE
      OBVIOUS
  <1>1. S \in MorphSurfaces BY DEF N!HandlesMinus
  <1>2. PICK x \in N!ReachExc(N!AllBot, r) :
          <<x, r>> \in MorphRel(S, N!AllBot)
      BY DEF N!HandlesMinus
  <1>3. x \in EventIds
    BY <1>2, Inst_BotNotLabel, Inst_G_inE, Inst_LblType,
       Inst_MemType, Inst_RelType, N!ReachExc_inE
  <1>4. CASE S = "J1"
    <2>1. r \in MorphMem("J1") BY <1>2, <1>4 DEF MorphRel
    <2>2. QED BY <2>1 DEF MorphMem
  <1>5. CASE S = "J2"
    <2>1. r \in MorphMem("J2") BY <1>2, <1>5 DEF MorphRel
    <2>2. QED BY <2>1 DEF MorphMem
  <1>6. CASE S = "J4"
    <2>1. N!AllBot[x] # NONE BY <1>2, <1>6 DEF MorphRel, MorphMem
    <2>2. QED BY <1>3, <2>1, AllBotIsBot
  <1>7. QED BY <1>1, <1>4, <1>5, <1>6 DEF MorphSurfaces

==========================================================================
