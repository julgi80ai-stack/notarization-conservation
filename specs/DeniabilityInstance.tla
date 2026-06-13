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
(***************************************************************************)
EXTENDS Naturals, TLAPS

CONSTANTS Msgs, Authors, NoAuth, Attributed, author, signed

ASSUME NoAuthFresh == NoAuth \notin Authors
ASSUME AttrInE     == Attributed \subseteq Msgs
ASSUME AuthorType  == author \in [Msgs -> Authors \cup {NoAuth}]
ASSUME SignedType  == signed \in [Msgs -> BOOLEAN]
ASSUME MsgsNE      == Msgs    # {}
ASSUME AuthorsNE   == Authors # {}

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
\* The instance.  Named (D!) to avoid clashes.
D == INSTANCE Notarization
       WITH E   <- Msgs,       L   <- Authors,  Bot <- NoAuth,
            Surfaces <- DenSurfaces,
            Mem <- DenMem,      Rel <- DenRel,
            G   <- Attributed,  lbl <- author

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
(* IMPOSSIBILITY in crypto-messaging language.  A SIGNED message reachable   *)
(* from an attributed sender is NOT separable -- non-repudiation holds, the   *)
(* message is NOT deniable.  (Sealed by the transferable signature pin.)     *)
(***************************************************************************)
THEOREM NonRepudiationPins ==
  ASSUME NEW g \in Attributed, NEW m \in Msgs, signed[m]
  PROVE  ~ D!Sep(m)
  <1>1. g \in Msgs BY AttrInE
  <1>2. g \in DenMem("Sig") /\ m \in DenMem("Sig") BY <1>1 DEF DenMem
  <1>3. <<g, m>> \in DenRel("Sig", author) BY <1>2 DEF DenRel
  <1>4. "Sig" \in DenSurfaces BY DEF DenSurfaces
  <1>5. m \in D!Reach
    <2> SUFFICES ASSUME NEW X \in SUBSET Msgs, Attributed \subseteq X,
                        D!ClosedUnder(X)
                 PROVE  m \in X
        BY DEF D!Reach
    <2>1. g \in X BY <1>1
    <2>2. D!Edge(g, m) BY <1>3, <1>4 DEF D!Edge
    <2>3. QED BY <2>1, <2>2, <1>1 DEF D!ClosedUnder
  <1>6. QED BY <1>5 DEF D!Sep

----------------------------------------------------------------------------
(***************************************************************************)
(* THE SIGNATURE-DEFEATS-REPUDIATION THEOREM (the deniability analogue of     *)
(* AuditLogInstance.ErasureFutile).                                          *)
(* Repudiating -- stripping the message's author label (author[m] := NoAuth) *)
(* -- does NOT remove the Sig link, because Sig is label-independent (it      *)
(* reads the signature artifact, not the author label).  So a signed message *)
(* stays reachable from the attributed frontier: non-repudiation SURVIVES     *)
(* the sender's denial.  This is the abstract DecisiveLI, concretely.        *)
(***************************************************************************)
THEOREM RepudiationFutileOnSig ==
  ASSUME NEW g \in Attributed, NEW m \in Msgs, signed[m]
  PROVE  <<g, m>> \in DenRel("Sig", D!Strip(author, m))
  <1>1. g \in Msgs BY AttrInE
  <1>2. g \in DenMem("Sig") /\ m \in DenMem("Sig") BY <1>1 DEF DenMem
  <1>3. QED BY <1>2 DEF DenRel

============================================================================
