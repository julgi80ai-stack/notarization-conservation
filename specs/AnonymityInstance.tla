------------------------- MODULE AnonymityInstance -------------------------
(***************************************************************************)
(* ACA-L2  Phase 6.2: ANONYMITY vs ACCOUNTABILITY as an INSTANCE of the      *)
(* label-independent notarization class (Notarization.tla).                 *)
(*                                                                         *)
(* The blockchain/ledger trade-off: strong accountability (every tx pinned   *)
(* to an identity) vs strong anonymity (a tx unlinkable to identity).        *)
(*                                                                         *)
(* Modelling commitment (for scrutiny, pillar A):                            *)
(*   Txs        transactions (events)                                       *)
(*   Idents     real-world identities (the correlation key); NoId = ⊥        *)
(*   ident      the identity binding  Txs -> Idents ∪ {NoId}                 *)
(*   flowlinked is the tx exposed by transaction-graph / clustering flow?    *)
(*   Deanon     the de-anonymised (identity-attributed) frontier (G)         *)
(*                                                                         *)
(* Two re-linking surfaces:                                                 *)
(*   "Graph" transaction-graph / address-clustering analysis.  Re-links a    *)
(*           flow-exposed tx to the identity frontier by FLOW STRUCTURE,      *)
(*           IGNORING the pseudonym/anonymity label  =>  LabelIndep.         *)
(*   "Pseud" pseudonym-equality link.  Reads the identity label             *)
(*           =>  NOT LabelIndep (defeated by a fresh pseudonym).             *)
(*                                                                         *)
(* Claim under test: accountability = Sealed (a label-independent flow pin); *)
(* anonymity = Separable; the conservation impossibility IS anonymity ⊥      *)
(* accountability, and a FRESH PSEUDONYM (stripping the identity label)       *)
(* does NOT defeat graph clustering (ClusteringFutile) -- exactly the        *)
(* signature-defeats-repudiation / chain-defeats-erasure shape.             *)
(***************************************************************************)
EXTENDS Naturals, TLAPS

CONSTANTS Txs, Idents, NoId, Deanon, ident, flowlinked

ASSUME NoIdFresh  == NoId \notin Idents
ASSUME DeanonInE  == Deanon \subseteq Txs
ASSUME IdentType  == ident \in [Txs -> Idents \cup {NoId}]
ASSUME FlowType   == flowlinked \in [Txs -> BOOLEAN]
ASSUME TxsNE      == Txs    # {}
ASSUME IdentsNE   == Idents # {}

----------------------------------------------------------------------------
AnonSurfaces == {"Graph", "Pseud"}
AnonMem(S)   == Txs

AnonRel(S, l) ==
   CASE S = "Graph" -> { p \in AnonMem("Graph") \X AnonMem("Graph") : flowlinked[p[2]] }
     [] S = "Pseud" -> { p \in AnonMem("Pseud") \X AnonMem("Pseud") :
                           l[p[1]] = l[p[2]] /\ l[p[1]] # NoId }

----------------------------------------------------------------------------
A == INSTANCE Notarization
       WITH E   <- Txs,      L   <- Idents,  Bot <- NoId,
            Surfaces <- AnonSurfaces,
            Mem <- AnonMem,   Rel <- AnonRel,
            G   <- Deanon,    lbl <- ident

----------------------------------------------------------------------------
THEOREM Graph_LabelIndep == A!LabelIndep("Graph")
  BY DEF A!LabelIndep, AnonRel

THEOREM Pseud_NotLabelIndep == ~ A!LabelIndep("Pseud")
  <1> PICK i0 \in Idents : TRUE BY IdentsNE
  <1> DEFINE l1 == [t \in Txs |-> i0]
             l2 == [t \in Txs |-> NoId]
  <1>0. i0 # NoId BY NoIdFresh
  <1>1. l1 \in A!Labelings /\ l2 \in A!Labelings BY DEF A!Labelings
  <1>2. PICK x \in Txs : TRUE BY TxsNE
  <1>3. <<x, x>> \in AnonRel("Pseud", l1) BY <1>2, <1>0 DEF AnonRel, AnonMem
  <1>4. <<x, x>> \notin AnonRel("Pseud", l2) BY <1>2 DEF AnonRel, AnonMem
  <1>5. AnonRel("Pseud", l1) # AnonRel("Pseud", l2) BY <1>3, <1>4
  <1>6. QED BY <1>1, <1>5 DEF A!LabelIndep

----------------------------------------------------------------------------
(* A flow-exposed tx reachable from a de-anonymised tx is NOT separable --   *)
(* accountability holds, the tx is NOT anonymous.                           *)
THEOREM AccountabilityPins ==
  ASSUME NEW g \in Deanon, NEW t \in Txs, flowlinked[t]
  PROVE  ~ A!Sep(t)
  <1>1. g \in Txs BY DeanonInE
  <1>2. g \in AnonMem("Graph") /\ t \in AnonMem("Graph") BY <1>1 DEF AnonMem
  <1>3. <<g, t>> \in AnonRel("Graph", ident) BY <1>2 DEF AnonRel
  <1>4. "Graph" \in AnonSurfaces BY DEF AnonSurfaces
  <1>5. t \in A!Reach
    <2> SUFFICES ASSUME NEW X \in SUBSET Txs, Deanon \subseteq X, A!ClosedUnder(X)
                 PROVE  t \in X
        BY DEF A!Reach
    <2>1. g \in X BY <1>1
    <2>2. A!Edge(g, t) BY <1>3, <1>4 DEF A!Edge
    <2>3. QED BY <2>1, <2>2, <1>1 DEF A!ClosedUnder
  <1>6. QED BY <1>5 DEF A!Sep

----------------------------------------------------------------------------
(* A FRESH PSEUDONYM (stripping the identity label) does NOT remove the       *)
(* graph link, because clustering is label-independent (reads flow, not the  *)
(* pseudonym).  Anonymity-by-relabelling fails against graph analysis -- the  *)
(* clustering analogue of ErasureFutile / RepudiationFutileOnSig.            *)
THEOREM ClusteringFutile ==
  ASSUME NEW g \in Deanon, NEW t \in Txs, flowlinked[t]
  PROVE  <<g, t>> \in AnonRel("Graph", A!Strip(ident, t))
  <1>1. g \in Txs BY DeanonInE
  <1>2. g \in AnonMem("Graph") /\ t \in AnonMem("Graph") BY <1>1 DEF AnonMem
  <1>3. QED BY <1>2 DEF AnonRel

============================================================================
