------------------------ MODULE DeniabilityInstance ------------------------
(***************************************************************************)
(* ACA-L2  Phase 6.0/6.3: NON-REPUDIATION vs DENIABILITY as an INSTANCE of   *)
(* the label-independent notarization class (Notarization.tla).             *)
(*                                                                         *)
(* The riskiest unification candidate.  Touchstone question: does the        *)
(* crypto messaging trade-off (non-repudiation XOR deniability, OTR) really  *)
(* instantiate the conservation framework, or does its "transferability to a *)
(* third party" dimension escape the relational Reach?                      *)
(*                                                                         *)
(* Modelling commitment (stated for scrutiny, pillar A):                     *)
(*   Msgs       authentication events (transcript entries)                  *)
(*   Authors    identity labels (the correlation key); NoAuth = ⊥           *)
(*   author     the authorship binding  Msgs -> Authors ∪ {NoAuth}          *)
(*   signed     does m carry a PUBLICLY-VERIFIABLE signature artifact?       *)
(*   Attributed the THIRD-PARTY-established author-attribution frontier (G)   *)
(*              -- the epistemic position of a judge.                       *)
(*                                                                         *)
(* Two re-linking surfaces (third-party verification procedures):           *)
(*   "Sig"  publicly-verifiable, TRANSFERABLE signature binding.  A third    *)
(*          party re-links any signed message to the author frontier         *)
(*          REGARDLESS of any repudiation -- it does NOT read the author      *)
(*          label  =>  LabelIndep  (the analogue of the position link).      *)
(*   "Mac"  receiver-forgeable symmetric binding.  Re-links only by shared    *)
(*          identity (key-equality); reads the label  =>  NOT LabelIndep      *)
(*          (non-transferable -- the deniability mechanism).                 *)
(*                                                                         *)
(* Claim under test: non-repudiation = Sealed (a label-independent           *)
(* transferable pin); deniability = Separable; the conservation law's        *)
(* impossibility then IS  non-repudiation ⊥ deniability, and a signature      *)
(* cannot be repudiated away (RepudiationFutileOnSig) exactly as a chained    *)
(* record cannot be erased away (AuditLogInstance.ErasureFutile).            *)
(*                                                                         *)
(* M3 (wiring): the instance now INSTANCEs Synthesis -- which EXTENDS        *)
(* Antagonism EXTENDS Notarization -- so the WHOLE law is inherited, not      *)
(* just its definitions.  The five abstract ASSUMEs of Notarization are      *)
(* DISCHARGED as the Inst_ lemmas, the impossibility is proved BY the        *)
(* abstract theorem (ColocBreaksSep) instead of being re-derived locally,    *)
(* the key-type split (Dichotomy) is discharged, and the §7.4 dividend row   *)
(* is computed as a theorem (Den_LeastExit / Den_ZeroPrice).                 *)
(***************************************************************************)
EXTENDS Naturals, TLAPS

CONSTANTS Msgs, Authors, NoAuth, Attributed, author, signed

ASSUME NoAuthFresh == NoAuth \notin Authors
ASSUME AttrInE     == Attributed \subseteq Msgs
ASSUME AuthorType  == author \in [Msgs -> Authors \cup {NoAuth}]
ASSUME SignedType  == signed \in [Msgs -> BOOLEAN]
ASSUME MsgsNE      == Msgs    # {}
ASSUME AuthorsNE   == Authors # {}
ASSUME AttrNE      == Attributed # {}   \* non-vacuity: the judge has
                                        \* established SOMETHING; otherwise
                                        \* Reach = {} and every message
                                        \* separates for free

----------------------------------------------------------------------------
DenSurfaces == {"Sig", "Mac"}
DenMem(S)   == Msgs

\* Surface relation UNDER a labeling l.
\*   Sig : transferable signature -- links to any signed message; IGNORES l  => LI.
\*   Mac : shared-identity binding -- reads l (shared non-NoAuth author) => NOT LI.
DenRel(S, l) ==
   CASE S = "Sig" -> { p \in DenMem("Sig") \X DenMem("Sig") : signed[p[2]] }
     [] S = "Mac" -> { p \in DenMem("Mac") \X DenMem("Mac") :
                         l[p[1]] = l[p[2]] /\ l[p[1]] # NoAuth }

----------------------------------------------------------------------------
\* The instance.  Named (D!) to avoid clashes.  Synthesis EXTENDS Antagonism
\* EXTENDS Notarization, so D! carries the entire law, theorems included.
D == INSTANCE Synthesis
       WITH E   <- Msgs,       L   <- Authors,  Bot <- NoAuth,
            Surfaces <- DenSurfaces,
            Mem <- DenMem,      Rel <- DenRel,
            G   <- Attributed,  lbl <- author

----------------------------------------------------------------------------
(***************************************************************************)
(* DISCHARGE THE ABSTRACT ASSUMEs.  TLAPS attaches the instantiated         *)
(* assumptions of Notarization as HYPOTHESES of every inherited theorem,    *)
(* so they must be proved before any abstract theorem can be applied.       *)
(* This is the "proof duty" of paper §10.                                   *)
(***************************************************************************)
LEMMA Inst_BotNotLabel == NoAuth \notin Authors
  BY NoAuthFresh

LEMMA Inst_G_inE == Attributed \subseteq Msgs
  BY AttrInE

LEMMA Inst_LblType == author \in D!Labelings
  BY AuthorType DEF D!Labelings

LEMMA Inst_MemType == \A S \in DenSurfaces : DenMem(S) \subseteq Msgs
  BY DEF DenMem

LEMMA Inst_RelType ==
  \A S \in DenSurfaces, l \in D!Labelings :
     DenRel(S, l) \subseteq DenMem(S) \X DenMem(S)
  <1> SUFFICES ASSUME NEW S \in DenSurfaces, NEW l \in D!Labelings
               PROVE  DenRel(S, l) \subseteq DenMem(S) \X DenMem(S)
      OBVIOUS
  <1>1. CASE S = "Sig" BY <1>1 DEF DenRel, DenMem
  <1>2. CASE S = "Mac" BY <1>2 DEF DenRel, DenMem
  <1>3. QED BY <1>1, <1>2 DEF DenSurfaces

----------------------------------------------------------------------------
(***************************************************************************)
(* SURFACE CLASSIFICATION -- the structural fact making the crypto messaging *)
(* trade-off a member of the class.                                         *)
(***************************************************************************)
THEOREM Sig_LabelIndep == D!LabelIndep("Sig")
  BY DEF D!LabelIndep, DenRel

\* The MAC binding genuinely READS the label: two labelings differ.
THEOREM Mac_NotLabelIndep == ~ D!LabelIndep("Mac")
  <1> PICK a0 \in Authors : TRUE BY AuthorsNE
  <1> DEFINE l1 == [m \in Msgs |-> a0]
             l2 == [m \in Msgs |-> NoAuth]
  <1>0. a0 # NoAuth BY NoAuthFresh
  <1>1. l1 \in D!Labelings /\ l2 \in D!Labelings
    BY DEF D!Labelings
  <1>2. PICK x \in Msgs : TRUE BY MsgsNE
  <1>3. <<x, x>> \in DenRel("Mac", l1)
    BY <1>2, <1>0 DEF DenRel, DenMem
  <1>4. <<x, x>> \notin DenRel("Mac", l2)
    BY <1>2 DEF DenRel, DenMem
  <1>5. DenRel("Mac", l1) # DenRel("Mac", l2)
    BY <1>3, <1>4
  <1>6. QED BY <1>1, <1>5 DEF D!LabelIndep

----------------------------------------------------------------------------
(***************************************************************************)
(* IMPOSSIBILITY in crypto-messaging language, INHERITED.  A SIGNED message  *)
(* reachable from an attributed sender is NOT separable -- non-repudiation   *)
(* holds, the message is NOT deniable.  No local re-derivation of the        *)
(* closure: the abstract theorem ColocBreaksSep is applied directly.         *)
(***************************************************************************)
THEOREM NonRepudiationPins ==
  ASSUME NEW g \in Attributed, NEW m \in Msgs, signed[m]
  PROVE  ~ D!Sep(m)
  <1>1. g \in Msgs BY AttrInE
  <1>2. <<g, m>> \in DenRel("Sig", author)
    BY <1>1 DEF DenRel, DenMem
  <1>3. "Sig" \in DenSurfaces BY DEF DenSurfaces
  <1>4. QED BY <1>2, <1>3, Inst_BotNotLabel, Inst_G_inE, Inst_LblType,
           Inst_MemType, Inst_RelType, D!ColocBreaksSep

----------------------------------------------------------------------------
(***************************************************************************)
(* THE SIGNATURE-DEFEATS-REPUDIATION THEOREM (the deniability analogue of     *)
(* AuditLogInstance.ErasureFutile), via the INHERITED Lemma 1 (DecisiveLI).  *)
(* Repudiating -- stripping the message's author label (author[m] := NoAuth) *)
(* -- does NOT remove the Sig link, because Sig is label-independent (it      *)
(* reads the signature artifact, not the author label).  So a signed message *)
(* stays reachable from the attributed frontier: non-repudiation SURVIVES     *)
(* the sender's denial.                                                      *)
(***************************************************************************)
THEOREM RepudiationFutileOnSig ==
  ASSUME NEW g \in Attributed, NEW m \in Msgs, signed[m]
  PROVE  <<g, m>> \in DenRel("Sig", D!Strip(author, m))
  <1>1. g \in Msgs BY AttrInE
  <1>2. <<g, m>> \in DenRel("Sig", author) BY <1>1 DEF DenRel, DenMem
  <1>3. D!LabelIndep("Sig") BY DEF D!LabelIndep, DenRel
  <1>4. "Sig" \in DenSurfaces BY DEF DenSurfaces
  <1>5. DenRel("Sig", author) = DenRel("Sig", D!Strip(author, m))
    BY <1>3, <1>4, Inst_BotNotLabel, Inst_G_inE, Inst_LblType,
       Inst_MemType, Inst_RelType, D!DecisiveLI
  <1>6. QED BY <1>2, <1>5

----------------------------------------------------------------------------
(***************************************************************************)
(* DISCHARGE THE KEY-TYPE SPLIT.  §7.1's "all four instances satisfy the    *)
(* split", machine-checked for this instance.                               *)
(***************************************************************************)
LEMMA AllBotIsBot ==
  ASSUME NEW x \in Msgs PROVE D!AllBot[x] = NoAuth
  BY DEF D!AllBot

THEOREM Den_Dichotomy == D!Dichotomy
  <1> SUFFICES ASSUME NEW S \in DenSurfaces
               PROVE  D!LabelIndep(S) \/ DenRel(S, D!AllBot) = {}
      BY DEF D!Dichotomy
  <1>1. CASE S = "Sig"
    <2>1. D!LabelIndep("Sig") BY DEF D!LabelIndep, DenRel
    <2>2. QED BY <1>1, <2>1
  <1>2. CASE S = "Mac"
    <2>1. DenRel("Mac", D!AllBot) = {}
      <3> SUFFICES ASSUME NEW p \in DenRel("Mac", D!AllBot) PROVE FALSE
          OBVIOUS
      <3>1. p \in Msgs \X Msgs BY DEF DenRel, DenMem
      <3>2. p[1] \in Msgs BY <3>1
      <3>3. D!AllBot[p[1]] # NoAuth BY DEF DenRel, DenMem
      <3>4. QED BY <3>2, <3>3, AllBotIsBot
    <2>2. QED BY <1>2, <2>1
  <1>3. QED BY <1>1, <1>2 DEF DenSurfaces

----------------------------------------------------------------------------
(***************************************************************************)
(* THE §7.4 DIVIDEND ROW, AS A THEOREM.                                     *)
(* "Deniability | relabel phase futile | exit the transferable-signature    *)
(*  surfaces, keep MACs"  --  computed, not asserted.                       *)
(***************************************************************************)
THEOREM Den_LeastExit ==
  ASSUME NEW m \in Msgs, m \notin Attributed, signed[m]
  PROVE  D!HandlesMinus(D!AllBot, m) = {"Sig"}
  <1>1. "Sig" \in D!HandlesMinus(D!AllBot, m)
    <2>1. PICK g \in Attributed : TRUE BY AttrNE
    <2>2. g \in Msgs BY <2>1, AttrInE
    <2>3. g \in D!ReachExc(D!AllBot, m)
      BY <2>1, Inst_BotNotLabel, Inst_G_inE, Inst_LblType,
         Inst_MemType, Inst_RelType, D!G_sub_ReachExc
    <2>4. <<g, m>> \in DenRel("Sig", D!AllBot) BY <2>2 DEF DenRel, DenMem
    <2>5. QED BY <2>3, <2>4 DEF D!HandlesMinus, DenSurfaces
  <1>2. "Mac" \notin D!HandlesMinus(D!AllBot, m)
    <2> SUFFICES ASSUME "Mac" \in D!HandlesMinus(D!AllBot, m) PROVE FALSE
        OBVIOUS
    <2>1. PICK x \in D!ReachExc(D!AllBot, m) :
            <<x, m>> \in DenRel("Mac", D!AllBot)
        BY DEF D!HandlesMinus
    <2>2. x \in Msgs
      BY <2>1, Inst_BotNotLabel, Inst_G_inE, Inst_LblType,
         Inst_MemType, Inst_RelType, D!ReachExc_inE
    <2>3. D!AllBot[x] # NoAuth BY <2>1 DEF DenRel, DenMem
    <2>4. QED BY <2>2, <2>3, AllBotIsBot
  <1>3. D!HandlesMinus(D!AllBot, m) \subseteq DenSurfaces
    BY DEF D!HandlesMinus
  <1>4. QED BY <1>1, <1>2, <1>3 DEF DenSurfaces

(* And the zero-price half: an unsigned message separates for free --      *)
(* Corollary 3 in domain dress, i.e. OTR's design decision as a theorem.   *)
THEOREM Den_ZeroPrice ==
  ASSUME NEW m \in Msgs, ~signed[m]
  PROVE  D!HandlesMinus(D!AllBot, m) = {}
  <1> SUFFICES ASSUME NEW S \in D!HandlesMinus(D!AllBot, m) PROVE FALSE
      OBVIOUS
  <1>1. S \in DenSurfaces BY DEF D!HandlesMinus
  <1>2. PICK x \in D!ReachExc(D!AllBot, m) :
          <<x, m>> \in DenRel(S, D!AllBot)
      BY DEF D!HandlesMinus
  <1>3. x \in Msgs
    BY <1>2, Inst_BotNotLabel, Inst_G_inE, Inst_LblType,
       Inst_MemType, Inst_RelType, D!ReachExc_inE
  <1>4. CASE S = "Sig"
    BY <1>2, <1>4 DEF DenRel, DenMem
  <1>5. CASE S = "Mac"
    <2>1. D!AllBot[x] # NoAuth BY <1>2, <1>5 DEF DenRel, DenMem
    <2>2. QED BY <1>3, <2>1, AllBotIsBot
  <1>6. QED BY <1>1, <1>4, <1>5 DEF DenSurfaces

============================================================================
