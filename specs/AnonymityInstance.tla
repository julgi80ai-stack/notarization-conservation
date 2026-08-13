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
(*   inputs     the SPEND STRUCTURE: inputs[t] is the SET of transactions    *)
(*              whose outputs t consumes (empty for a coinbase / unspent-    *)
(*              -from tx).  A SET, not a pointer: a transaction may spend    *)
(*              MANY inputs at once, and that is precisely the datum chain   *)
(*              analysis exploits.                                          *)
(*   Deanon     the de-anonymised (identity-attributed) frontier (G)         *)
(*                                                                         *)
(* Two re-linking surfaces:                                                 *)
(*   "Graph" transaction-graph / address-clustering analysis.  ADJACENCY:    *)
(*           tx x re-links tx t when t SPENDS x  (x \in inputs[t]) -- the    *)
(*           multi-input heuristic of chain analysis, which reads the spend  *)
(*           edges and IGNORES the pseudonym/anonymity label => LabelIndep.  *)
(*           D-4(b) NOTE: an earlier revision modelled "Graph" as the        *)
(*           CYLINDER  { p : flowlinked[p[2]] } -- every tx linked to every  *)
(*           flow-exposed tx in ONE step, with the source coordinate p[1]    *)
(*           unread.  That relation takes the CONCLUSION of chain analysis   *)
(*           (is t deanonymisable?) as a primitive input flag, so the        *)
(*           analysis the paper prices was not in the model at all, and the  *)
(*           surface was a token-for-token copy of DeniabilityInstance's     *)
(*           "Sig".  The spend adjacency is the faithful model -- a tx       *)
(*           records ONLY which outputs it consumes; transitive clustering   *)
(*           is the CLOSURE's job -- and, unlike a prev-hash POINTER, it is  *)
(*           many-to-many: inputs[t] is a SET, so the linkage a single tx    *)
(*           induces is a join, not a chain step.                           *)
(*   "Pseud" pseudonym-equality link.  Reads the identity label             *)
(*           =>  NOT LabelIndep (defeated by a fresh pseudonym).             *)
(*                                                                         *)
(* Claim under test: accountability = Sealed (a label-independent flow pin); *)
(* anonymity = Separable; the conservation impossibility IS anonymity ⊥      *)
(* accountability, and a FRESH PSEUDONYM (stripping the identity label)       *)
(* does NOT defeat graph clustering (ClusteringFutile) -- exactly the        *)
(* signature-defeats-repudiation / chain-defeats-erasure shape.             *)
(*                                                                         *)
(* M3 (wiring): INSTANCE Synthesis (the whole law inherited), abstract       *)
(* ASSUMEs discharged (the Inst_ lemmas), impossibility proved BY            *)
(* ColocBreaksSep, Dichotomy discharged, and the §7.4 dividend row computed  *)
(* (Anon_LeastExit; Anon_ZeroPrice added in M5-c).                          *)
(***************************************************************************)
EXTENDS Naturals, TLAPS

CONSTANTS Txs, Idents, NoId, Deanon, ident, inputs

ASSUME NoIdFresh  == NoId \notin Idents
ASSUME DeanonInE  == Deanon \subseteq Txs
ASSUME IdentType  == ident \in [Txs -> Idents \cup {NoId}]
ASSUME InputsType == inputs \in [Txs -> SUBSET Txs]
ASSUME TxsNE      == Txs    # {}
ASSUME IdentsNE   == Idents # {}
ASSUME DeanonNE   == Deanon # {}   \* non-vacuity: something has been
                                   \* de-anonymised; otherwise Reach = {}
                                   \* and every tx separates for free

----------------------------------------------------------------------------
AnonSurfaces == {"Graph", "Pseud"}
AnonMem(S)   == Txs

\* Surface relation UNDER a labeling l.
\*   Graph : multi-input spend adjacency -- p[1] is one of the inputs p[2]
\*           consumes.  l is IGNORED  =>  label-indep.  MANY-TO-MANY: a tx
\*           joins ALL of its inputs, so this is not a predecessor function.
\*   Pseud : shared non-fresh pseudonym.  l is READ  =>  label-dep.
AnonRel(S, l) ==
   CASE S = "Graph" -> { p \in AnonMem("Graph") \X AnonMem("Graph") :
                           p[1] \in inputs[p[2]] }
     [] S = "Pseud" -> { p \in AnonMem("Pseud") \X AnonMem("Pseud") :
                           l[p[1]] = l[p[2]] /\ l[p[1]] # NoId }

----------------------------------------------------------------------------
\* The instance.  Synthesis EXTENDS Antagonism EXTENDS Notarization, so A!
\* carries the entire law, theorems included.
A == INSTANCE Synthesis
       WITH E   <- Txs,      L   <- Idents,  Bot <- NoId,
            Surfaces <- AnonSurfaces,
            Mem <- AnonMem,   Rel <- AnonRel,
            G   <- Deanon,    lbl <- ident

----------------------------------------------------------------------------
(***************************************************************************)
(* DISCHARGE THE ABSTRACT ASSUMEs (the "proof duty" of paper §10).          *)
(***************************************************************************)
LEMMA Inst_BotNotLabel == NoId \notin Idents
  BY NoIdFresh

LEMMA Inst_G_inE == Deanon \subseteq Txs
  BY DeanonInE

LEMMA Inst_LblType == ident \in A!Labelings
  BY IdentType DEF A!Labelings

LEMMA Inst_MemType == \A S \in AnonSurfaces : AnonMem(S) \subseteq Txs
  BY DEF AnonMem

LEMMA Inst_RelType ==
  \A S \in AnonSurfaces, l \in A!Labelings :
     AnonRel(S, l) \subseteq AnonMem(S) \X AnonMem(S)
  <1> SUFFICES ASSUME NEW S \in AnonSurfaces, NEW l \in A!Labelings
               PROVE  AnonRel(S, l) \subseteq AnonMem(S) \X AnonMem(S)
      OBVIOUS
  <1>1. CASE S = "Graph" BY <1>1 DEF AnonRel, AnonMem
  <1>2. CASE S = "Pseud" BY <1>2 DEF AnonRel, AnonMem
  <1>3. QED BY <1>1, <1>2 DEF AnonSurfaces

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
(* A tx that SPENDS a de-anonymised tx is NOT separable -- accountability   *)
(* holds, the tx is NOT anonymous.  INHERITED: proved BY the abstract        *)
(* ColocBreaksSep, not re-derived.  (Deeper txs are re-linked hop by hop:    *)
(* the closure walks the spend graph -- see AnonymityWitness.tla for a       *)
(* 2-hop path through a multi-input join.)                                  *)
THEOREM AccountabilityPins ==
  ASSUME NEW g \in Deanon, NEW t \in Txs, g \in inputs[t]
  PROVE  ~ A!Sep(t)
  <1>1. g \in Txs BY DeanonInE
  <1>2. <<g, t>> \in AnonRel("Graph", ident) BY <1>1 DEF AnonRel, AnonMem
  <1>3. "Graph" \in AnonSurfaces BY DEF AnonSurfaces
  <1>4. QED BY <1>2, <1>3, Inst_BotNotLabel, Inst_G_inE, Inst_LblType,
           Inst_MemType, Inst_RelType, A!ColocBreaksSep

----------------------------------------------------------------------------
(* A FRESH PSEUDONYM (stripping the identity label) does NOT remove the       *)
(* spend link, because clustering is label-independent (reads the spend      *)
(* edges, not the pseudonym).  Via the INHERITED Lemma 1 (DecisiveLI) -- the *)
(* clustering analogue of ErasureFutile / RepudiationFutileOnSig.            *)
THEOREM ClusteringFutile ==
  ASSUME NEW g \in Deanon, NEW t \in Txs, g \in inputs[t]
  PROVE  <<g, t>> \in AnonRel("Graph", A!Strip(ident, t))
  <1>1. g \in Txs BY DeanonInE
  <1>2. <<g, t>> \in AnonRel("Graph", ident) BY <1>1 DEF AnonRel, AnonMem
  <1>3. A!LabelIndep("Graph") BY DEF A!LabelIndep, AnonRel
  <1>4. "Graph" \in AnonSurfaces BY DEF AnonSurfaces
  <1>5. AnonRel("Graph", ident) = AnonRel("Graph", A!Strip(ident, t))
    BY <1>3, <1>4, Inst_BotNotLabel, Inst_G_inE, Inst_LblType,
       Inst_MemType, Inst_RelType, A!DecisiveLI
  <1>6. QED BY <1>2, <1>5

----------------------------------------------------------------------------
(***************************************************************************)
(* DISCHARGE THE KEY-TYPE SPLIT (§7.1), machine-checked for this instance.  *)
(***************************************************************************)
LEMMA AllBotIsBot ==
  ASSUME NEW x \in Txs PROVE A!AllBot[x] = NoId
  BY DEF A!AllBot

THEOREM Anon_Dichotomy == A!Dichotomy
  <1> SUFFICES ASSUME NEW S \in AnonSurfaces
               PROVE  A!LabelIndep(S) \/ AnonRel(S, A!AllBot) = {}
      BY DEF A!Dichotomy
  <1>1. CASE S = "Graph"
    <2>1. A!LabelIndep("Graph") BY DEF A!LabelIndep, AnonRel
    <2>2. QED BY <1>1, <2>1
  <1>2. CASE S = "Pseud"
    <2>1. AnonRel("Pseud", A!AllBot) = {}
      <3> SUFFICES ASSUME NEW p \in AnonRel("Pseud", A!AllBot) PROVE FALSE
          OBVIOUS
      <3>1. p \in Txs \X Txs BY DEF AnonRel, AnonMem
      <3>2. p[1] \in Txs BY <3>1
      <3>3. A!AllBot[p[1]] # NoId BY DEF AnonRel, AnonMem
      <3>4. QED BY <3>2, <3>3, AllBotIsBot
    <2>2. QED BY <1>2, <2>1
  <1>3. QED BY <1>1, <1>2 DEF AnonSurfaces

----------------------------------------------------------------------------
(***************************************************************************)
(* THE §7.4 DIVIDEND ROW, AS A THEOREM.                                     *)
(* "Anonymity | pseudonym rotation futile | exit the flow-analysis           *)
(*  surfaces, keep pseudonym links"  --  computed, not asserted.            *)
(***************************************************************************)
THEOREM Anon_LeastExit ==
  ASSUME NEW g \in Deanon, NEW t \in Txs, t \notin Deanon, g \in inputs[t]
  PROVE  A!HandlesMinus(A!AllBot, t) = {"Graph"}
  <1>1. "Graph" \in A!HandlesMinus(A!AllBot, t)
    <2>1. g \in Txs BY DeanonInE
    <2>2. g \in A!ReachExc(A!AllBot, t)
      BY Inst_BotNotLabel, Inst_G_inE, Inst_LblType,
         Inst_MemType, Inst_RelType, A!G_sub_ReachExc
    <2>3. <<g, t>> \in AnonRel("Graph", A!AllBot) BY <2>1 DEF AnonRel, AnonMem
    <2>4. QED BY <2>2, <2>3 DEF A!HandlesMinus, AnonSurfaces
  <1>2. "Pseud" \notin A!HandlesMinus(A!AllBot, t)
    <2> SUFFICES ASSUME "Pseud" \in A!HandlesMinus(A!AllBot, t) PROVE FALSE
        OBVIOUS
    <2>1. PICK x \in A!ReachExc(A!AllBot, t) :
            <<x, t>> \in AnonRel("Pseud", A!AllBot)
        BY DEF A!HandlesMinus
    <2>2. x \in Txs
      BY <2>1, Inst_BotNotLabel, Inst_G_inE, Inst_LblType,
         Inst_MemType, Inst_RelType, A!ReachExc_inE
    <2>3. A!AllBot[x] # NoId BY <2>1 DEF AnonRel, AnonMem
    <2>4. QED BY <2>2, <2>3, AllBotIsBot
  <1>3. A!HandlesMinus(A!AllBot, t) \subseteq AnonSurfaces
    BY DEF A!HandlesMinus
  <1>4. QED BY <1>1, <1>2, <1>3 DEF AnonSurfaces

(* And the zero-price half: a tx that SPENDS NOTHING -- inputs[t] = {},    *)
(* i.e. a coinbase / newly-minted tx that never entered the spend graph -- *)
(* separates for free once the pseudonyms are dropped: the Graph surface   *)
(* cannot pin a tx with no inputs, and the Pseud surface vanishes at the   *)
(* all-Bot labelling.  Corollary 3 in domain dress: the privacy-coin       *)
(* design decision (keep the tx off the flow-analysis surface) as a        *)
(* theorem.  The verbatim symmetric of Den_ZeroPrice / Audit_ZeroPrice.    *)
THEOREM Anon_ZeroPrice ==
  ASSUME NEW t \in Txs, inputs[t] = {}
  PROVE  A!HandlesMinus(A!AllBot, t) = {}
  <1> SUFFICES ASSUME NEW S \in A!HandlesMinus(A!AllBot, t) PROVE FALSE
      OBVIOUS
  <1>1. S \in AnonSurfaces BY DEF A!HandlesMinus
  <1>2. PICK x \in A!ReachExc(A!AllBot, t) :
          <<x, t>> \in AnonRel(S, A!AllBot)
      BY DEF A!HandlesMinus
  <1>3. x \in Txs
    BY <1>2, Inst_BotNotLabel, Inst_G_inE, Inst_LblType,
       Inst_MemType, Inst_RelType, A!ReachExc_inE
  <1>4. CASE S = "Graph"
    <2>1. x \in inputs[t] BY <1>2, <1>4 DEF AnonRel, AnonMem
    <2>2. QED BY <2>1
  <1>5. CASE S = "Pseud"
    <2>1. A!AllBot[x] # NoId BY <1>2, <1>5 DEF AnonRel, AnonMem
    <2>2. QED BY <1>3, <2>1, AllBotIsBot
  <1>6. QED BY <1>1, <1>4, <1>5 DEF AnonSurfaces

============================================================================
