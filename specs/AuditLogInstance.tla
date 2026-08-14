------------------------- MODULE AuditLogInstance -------------------------
(***************************************************************************)
(* Phase 3.1 (L2-breadth): a SECOND, independent member of the abstract     *)
(* label-independent notarization class (Notarization.tla) -- a             *)
(* hash-chained append-only AUDIT LOG (Certificate Transparency /           *)
(* Schneier-Kelsey forward-integrity style).                               *)
(*                                                                         *)
(* The point of this module is to turn the paper's "breadth claim" into a    *)
(* breadth THEOREM: the class is inhabited by at least two structurally      *)
(* unrelated systems (the audited three-surface governance pipeline AND a  *)
(* generic tamper-evident log), so the impossibility is a class law, not a  *)
(* one-robot artifact.                                                      *)
(*                                                                         *)
(* Domain reading:                                                         *)
(*   Entries  log records (events appended to the append-only log)          *)
(*   Subjects subject-identity / personal-data keys (the corr labels)       *)
(*   NoSubj   "no key" marker (an erased / unkeyed record) = Bot            *)
(*   subj     the actual labeling  Entries -> Subjects \cup {NoSubj}        *)
(*   prev     the prev-hash pointer: the IMMEDIATE predecessor a record     *)
(*            commits to (NoPrev for a genesis / unchained record)          *)
(*   Logged   the committed / finalized frontier = the action-log frontier G *)
(*                                                                         *)
(* Two re-linking surfaces:                                                 *)
(*   "Chain"   adjacency link: record x seals record y when y's prev-hash   *)
(*             points at x (prev[y] = x) -- exactly what a hash chain       *)
(*             stores.  Reads prev, NOT subj  =>  LI.                       *)
(*             M4 NOTE: an earlier revision modelled "Chain" as the height   *)
(*             ORDER (height[x] =< height[y]).  That relation links every    *)
(*             committed record to every later one in ONE step, so the      *)
(*             closure never has to walk the chain, and none of the paper's *)
(*             non-trivial distinctions (Sealed/SealedLI, Reach/ReachLI,    *)
(*             price </= I) were observable on any instance.  The adjacency  *)
(*             relation is the faithful model -- a record stores ONLY its    *)
(*             predecessor's hash; transitive linkage is the CLOSURE's job   *)
(*             -- and it realizes those distinctions (AuditLogWitness.tla).  *)
(*   "Subject" key-equality link: shared non-erased subject.  Reads subj    *)
(*             =>  NOT LI (the unique key-dependent surface here).           *)
(*                                                                         *)
(* M3 (wiring): INSTANCE Synthesis (the whole law inherited), abstract      *)
(* ASSUMEs discharged (the Inst_ lemmas), impossibility proved BY           *)
(* ColocBreaksSep, erasure futility BY the inherited DecisiveLI, Dichotomy  *)
(* discharged, and the dividend row computed (Audit_LeastExit).             *)
(*                                                                         *)
(* Bounds: NONE.  Entries, Subjects arbitrary (possibly infinite).          *)
(***************************************************************************)
EXTENDS TLAPS

CONSTANTS Entries, Subjects, NoSubj, NoPrev, Logged, subj, prev

ASSUME NoSubjFresh == NoSubj \notin Subjects
ASSUME NoPrevFresh == NoPrev \notin Entries
ASSUME LoggedInE   == Logged \subseteq Entries
ASSUME SubjType    == subj   \in [Entries -> Subjects \cup {NoSubj}]
ASSUME PrevType    == prev   \in [Entries -> Entries \cup {NoPrev}]
ASSUME EntriesNE   == Entries  # {}
ASSUME SubjectsNE  == Subjects # {}
ASSUME LoggedNE    == Logged   # {}   \* non-vacuity: the log has committed
                                      \* something; otherwise Reach = {} and
                                      \* every record separates for free

----------------------------------------------------------------------------
AuditSurfaces == {"Chain", "Subject"}

\* Both surfaces range over all appended records.
AuditMem(S) == Entries

\* Surface relation UNDER a labeling l.
\*   Chain   : prev-hash adjacency.  l is IGNORED  =>  label-indep.
\*   Subject : shared non-erased subject key.  l is READ  =>  label-dep.
AuditRel(S, l) ==
   CASE S = "Chain"   -> { p \in AuditMem("Chain") \X AuditMem("Chain") :
                             prev[p[2]] = p[1] }
     [] S = "Subject" -> { p \in AuditMem("Subject") \X AuditMem("Subject") :
                             l[p[1]] = l[p[2]] /\ l[p[1]] # NoSubj }

----------------------------------------------------------------------------
\* The instance.  Named (A!) to avoid clashing with anything.  Synthesis
\* EXTENDS Antagonism EXTENDS Notarization, so A! carries the entire law,
\* theorems included.
A == INSTANCE Synthesis
       WITH E   <- Entries,   L   <- Subjects,  Bot <- NoSubj,
            Surfaces <- AuditSurfaces,
            Mem <- AuditMem,   Rel <- AuditRel,
            G   <- Logged,     lbl <- subj

----------------------------------------------------------------------------
(***************************************************************************)
(* DISCHARGE THE ABSTRACT ASSUMEs (the "proof duty" every instance owes).   *)
(***************************************************************************)
LEMMA Inst_BotNotLabel == NoSubj \notin Subjects
  BY NoSubjFresh

LEMMA Inst_G_inE == Logged \subseteq Entries
  BY LoggedInE

LEMMA Inst_LblType == subj \in A!Labelings
  BY SubjType DEF A!Labelings

LEMMA Inst_MemType == \A S \in AuditSurfaces : AuditMem(S) \subseteq Entries
  BY DEF AuditMem

LEMMA Inst_RelType ==
  \A S \in AuditSurfaces, l \in A!Labelings :
     AuditRel(S, l) \subseteq AuditMem(S) \X AuditMem(S)
  <1> SUFFICES ASSUME NEW S \in AuditSurfaces, NEW l \in A!Labelings
               PROVE  AuditRel(S, l) \subseteq AuditMem(S) \X AuditMem(S)
      OBVIOUS
  <1>1. CASE S = "Chain" BY <1>1 DEF AuditRel, AuditMem
  <1>2. CASE S = "Subject" BY <1>2 DEF AuditRel, AuditMem
  <1>3. QED BY <1>1, <1>2 DEF AuditSurfaces

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
(* IMPOSSIBILITY in audit-log language, INHERITED.  A record r whose         *)
(* prev-hash points at a committed entry g is chain-linked to g; g is in     *)
(* the frontier, so r is in the closure -- r is NOT separated.  In words:    *)
(* in a total-accountability tamper-evident log, no appended record can be   *)
(* "non-established" (kept outside the established/attributed set), because  *)
(* the chain re-links it.  (Deeper records are re-linked hop by hop: the     *)
(* closure walks the chain -- see AuditLogWitness.tla for a 2-hop path.)     *)
(* No local re-derivation of the closure: the abstract ColocBreaksSep is     *)
(* applied directly.                                                         *)
(***************************************************************************)
THEOREM AppendCannotSeparate ==
  ASSUME NEW g \in Logged, NEW r \in Entries, prev[r] = g
  PROVE  ~ A!Sep(r)
  <1>1. g \in Entries BY LoggedInE
  <1>2. <<g, r>> \in AuditRel("Chain", subj)
    BY <1>1 DEF AuditRel, AuditMem
  <1>3. "Chain" \in AuditSurfaces BY DEF AuditSurfaces
  <1>4. QED BY <1>2, <1>3, Inst_BotNotLabel, Inst_G_inE, Inst_LblType,
           Inst_MemType, Inst_RelType, A!ColocBreaksSep

----------------------------------------------------------------------------
(***************************************************************************)
(* THE RIGHT-TO-BE-FORGOTTEN CONFLICT, MACHINE-PROVEN.                       *)
(* Erasing record r's subject key (Strip -> NoSubj) does NOT remove the      *)
(* chain link, because the chain is label-independent (reads prev-hash, not  *)
(* the subject).  So the erased record stays reachable from the committed    *)
(* frontier: GDPR-style erasure is futile against an immutable hash chain.   *)
(* Via the INHERITED Lemma 1 (DecisiveLI), not re-derived.                   *)
(***************************************************************************)
THEOREM ErasureFutile ==
  ASSUME NEW g \in Logged, NEW r \in Entries, prev[r] = g
  PROVE  <<g, r>> \in AuditRel("Chain", A!Strip(subj, r))
  <1>1. g \in Entries BY LoggedInE
  <1>2. <<g, r>> \in AuditRel("Chain", subj)
    BY <1>1 DEF AuditRel, AuditMem
  <1>3. A!LabelIndep("Chain") BY DEF A!LabelIndep, AuditRel
  <1>4. "Chain" \in AuditSurfaces BY DEF AuditSurfaces
  <1>5. AuditRel("Chain", subj) = AuditRel("Chain", A!Strip(subj, r))
    BY <1>3, <1>4, Inst_BotNotLabel, Inst_G_inE, Inst_LblType,
       Inst_MemType, Inst_RelType, A!DecisiveLI
  <1>6. QED BY <1>2, <1>5

----------------------------------------------------------------------------
(***************************************************************************)
(* DISCHARGE THE KEY-TYPE SPLIT (Dichotomy) for this instance.              *)
(***************************************************************************)
LEMMA AllBotIsBot ==
  ASSUME NEW x \in Entries PROVE A!AllBot[x] = NoSubj
  BY DEF A!AllBot

THEOREM Audit_Dichotomy == A!Dichotomy
  <1> SUFFICES ASSUME NEW S \in AuditSurfaces
               PROVE  A!LabelIndep(S) \/ AuditRel(S, A!AllBot) = {}
      BY DEF A!Dichotomy
  <1>1. CASE S = "Chain"
    <2>1. A!LabelIndep("Chain") BY DEF A!LabelIndep, AuditRel
    <2>2. QED BY <1>1, <2>1
  <1>2. CASE S = "Subject"
    <2>1. AuditRel("Subject", A!AllBot) = {}
      <3> SUFFICES ASSUME NEW p \in AuditRel("Subject", A!AllBot) PROVE FALSE
          OBVIOUS
      <3>1. p \in Entries \X Entries BY DEF AuditRel, AuditMem
      <3>2. p[1] \in Entries BY <3>1
      <3>3. A!AllBot[p[1]] # NoSubj BY DEF AuditRel, AuditMem
      <3>4. QED BY <3>2, <3>3, AllBotIsBot
    <2>2. QED BY <1>2, <2>1
  <1>3. QED BY <1>1, <1>2 DEF AuditSurfaces

----------------------------------------------------------------------------
(***************************************************************************)
(* THE DIVIDEND ROW, AS A THEOREM (Audit_LeastExit).                        *)
(* "Erasure (RTBF) | key-erasure futile | exit the chain surface (unhook     *)
(*  the record's prev-link), keep the subject index"  --  computed, not      *)
(*  asserted: under the maximal key-drop the ONLY surviving pin on a         *)
(*  chained record is its prev-hash adjacency.                              *)
(***************************************************************************)
THEOREM Audit_LeastExit ==
  ASSUME NEW g \in Logged, NEW r \in Entries, prev[r] = g
  PROVE  A!HandlesMinus(A!AllBot, r) = {"Chain"}
  <1>1. "Chain" \in A!HandlesMinus(A!AllBot, r)
    <2>1. g \in Entries BY LoggedInE
    <2>2. g \in A!ReachExc(A!AllBot, r)
      BY Inst_BotNotLabel, Inst_G_inE, Inst_LblType,
         Inst_MemType, Inst_RelType, A!G_sub_ReachExc
    <2>3. <<g, r>> \in AuditRel("Chain", A!AllBot)
      BY <2>1 DEF AuditRel, AuditMem
    <2>4. QED BY <2>2, <2>3 DEF A!HandlesMinus, AuditSurfaces
  <1>2. "Subject" \notin A!HandlesMinus(A!AllBot, r)
    <2> SUFFICES ASSUME "Subject" \in A!HandlesMinus(A!AllBot, r) PROVE FALSE
        OBVIOUS
    <2>1. PICK x \in A!ReachExc(A!AllBot, r) :
            <<x, r>> \in AuditRel("Subject", A!AllBot)
        BY DEF A!HandlesMinus
    <2>2. x \in Entries
      BY <2>1, Inst_BotNotLabel, Inst_G_inE, Inst_LblType,
         Inst_MemType, Inst_RelType, A!ReachExc_inE
    <2>3. A!AllBot[x] # NoSubj BY <2>1 DEF AuditRel, AuditMem
    <2>4. QED BY <2>2, <2>3, AllBotIsBot
  <1>3. A!HandlesMinus(A!AllBot, r) \subseteq AuditSurfaces
    BY DEF A!HandlesMinus
  <1>4. QED BY <1>1, <1>2, <1>3 DEF AuditSurfaces

(* And the zero-price half: a GENESIS record -- one whose prev-pointer      *)
(* names nothing, i.e. a record that never entered the chain linkage --     *)
(* separates for free once the keys are dropped: the Chain surface cannot   *)
(* pin an entry with no predecessor pointer into the chain, and the         *)
(* Subject surface vanishes at the all-Bot labelling.  ZeroPriceIffUnsealed *)
(* in domain dress: "keep personal data off-chain" practice as a theorem.   *)
(* The verbatim symmetric of Den_ZeroPrice.  (M9-S1)                        *)
THEOREM Audit_ZeroPrice ==
  ASSUME NEW e \in Entries, prev[e] = NoPrev
  PROVE  A!HandlesMinus(A!AllBot, e) = {}
  <1> SUFFICES ASSUME NEW S \in A!HandlesMinus(A!AllBot, e) PROVE FALSE
      OBVIOUS
  <1>1. S \in AuditSurfaces BY DEF A!HandlesMinus
  <1>2. PICK x \in A!ReachExc(A!AllBot, e) :
          <<x, e>> \in AuditRel(S, A!AllBot)
      BY DEF A!HandlesMinus
  <1>3. x \in Entries
    BY <1>2, Inst_BotNotLabel, Inst_G_inE, Inst_LblType,
       Inst_MemType, Inst_RelType, A!ReachExc_inE
  <1>4. CASE S = "Chain"
    <2>1. prev[e] = x BY <1>2, <1>4 DEF AuditRel, AuditMem
    <2>2. QED BY <1>3, <2>1, NoPrevFresh
  <1>5. CASE S = "Subject"
    <2>1. A!AllBot[x] # NoSubj BY <1>2, <1>5 DEF AuditRel, AuditMem
    <2>2. QED BY <1>3, <2>1, AllBotIsBot
  <1>6. QED BY <1>1, <1>4, <1>5 DEF AuditSurfaces

----------------------------------------------------------------------------
(***************************************************************************)
(* TOTAL ACCOUNTABILITY FAILS AT THE GENESIS.  (M9-S2)                      *)
(* A genesis record -- prev[e] = NoPrev -- has no Chain in-edge at all      *)
(* (nothing's predecessor pointer can name it as the SOURCE of its own      *)
(* pin: a Chain pin on e requires prev[e] to BE an entry), and Subject is   *)
(* not label-independent, so e has NO label-independent pin: e is never     *)
(* Sealed, hence TA is false in ANY configuration containing a genesis.     *)
(* Since a finite prev-structure with no genesis must contain a prev-cycle  *)
(* -- which a real hash chain excludes -- total accountability is           *)
(* unsatisfiable in every finite acyclic audit log.  The class-level        *)
(* counterpart (TA IS satisfiable, at the price of a root self-pin: the     *)
(* trust-anchor convention) is TLC-checked in TAWitness.tla.                *)
(***************************************************************************)
THEOREM Audit_GenesisUnsealed ==
  ASSUME NEW e \in Entries, prev[e] = NoPrev
  PROVE  ~A!Sealed(e) /\ ~A!TA
  <1>1. ~A!Sealed(e)
    <2> SUFFICES ASSUME A!Sealed(e) PROVE FALSE
        OBVIOUS
    <2>1. PICK S \in AuditSurfaces : A!LabelIndep(S) /\ A!Pins(S, e)
      BY DEF A!Sealed, A!Handles
    <2>2. CASE S = "Chain"
      <3>1. PICK g \in A!Reach : <<g, e>> \in AuditRel("Chain", subj)
        BY <2>1, <2>2 DEF A!Pins
      <3>2. g \in Entries BY <3>1 DEF AuditRel, AuditMem
      <3>3. prev[e] = g BY <3>1 DEF AuditRel, AuditMem
      <3>4. QED BY <3>2, <3>3, NoPrevFresh
    <2>3. CASE S = "Subject"
      BY <2>1, <2>3, Subject_NotLabelIndep
    <2>4. QED BY <2>1, <2>2, <2>3 DEF AuditSurfaces
  <1>2. QED BY <1>1 DEF A!TA

==========================================================================
