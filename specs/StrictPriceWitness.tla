------------------------- MODULE StrictPriceWitness -------------------------
(***************************************************************************)
(* M9-S3 witness: PriceWithinIntegrity IS A GENUINE UPPER BOUND, NOT AN    *)
(* EQUALITY IN DISGUISE.                                                   *)
(*                                                                         *)
(* In the rest of the artifact every strict PriceWithinIntegrity inclusion *)
(*      HandlesMinus(AllBot, r)  \subseteq  Handles(r)                     *)
(* is the degenerate 0 < 1, and the one element with I = 2 (PriceWitness's *)
(* s) has price exactly 2 -- so nothing witnessed that PriceWithinIntegrity *)
(* (the BOUND) and FreshExactness (the EQUALITY, for sinks) differ.        *)
(*                                                                         *)
(* This model separates them at I = 2:                                     *)
(*                                                                         *)
(*      g0 --P--> r          P pins r directly from the frontier           *)
(*      r  --T--> z          z is reachable ONLY THROUGH r                 *)
(*      z  --Q--> r          Q pins r only from z                          *)
(*                                                                         *)
(*   Handles(r)             = {P, Q}     I(r) = 2                          *)
(*   HandlesMinus(AllBot,r) = {P}        price = 1  <  2                   *)
(*                                                                         *)
(* Q's pin evaporates in the r-deleted closure because its source z is    *)
(* fed by r itself -- a seal partly financed by the sealed record.  And r  *)
(* is NOT a sink (it emits r --T--> z), so FreshExactness fails to apply,  *)
(* which is exactly why the equality may fail while the bound holds: the   *)
(* least exit set is {P} alone -- exiting P separates r even though the    *)
(* seal counts two surfaces.                                               *)
(*                                                                         *)
(* All surfaces ignore the labelling, so LabelIndep holds for each and    *)
(* Dichotomy is immediate; G # {} (non-vacuity).                           *)
(*                                                                         *)
(* Definitions copied VERBATIM from Notarization.tla / Antagonism.tla /    *)
(* Synthesis.tla (the PriceWitness.tla pattern); only the CONSTANTS are    *)
(* concrete.  Faithfulness is by syntactic identity.                       *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

E   == {"g0", "r", "z"}
G   == {"g0"}
Bot == "_"
L   == {"k"}
Surfaces == {"P", "Q", "T"}
lbl == [e \in E |-> Bot]
Mem(S) == E
Rel(S, l) ==
  CASE S = "P" -> {<<"g0", "r">>}
    [] S = "Q" -> {<<"z", "r">>}
    [] S = "T" -> {<<"r", "z">>}

Labelings == [E -> L \cup {Bot}]

\* ---- Notarization.tla, verbatim ----
LabelIndep(S)  == \A l1, l2 \in Labelings : Rel(S, l1) = Rel(S, l2)
Edge(x, y)     == \E S \in Surfaces : <<x, y>> \in Rel(S, lbl)
ClosedUnder(X) == \A x, y \in E : (x \in X /\ Edge(x, y)) => y \in X
Reach == { e \in E : \A X \in SUBSET E :
                       (G \subseteq X /\ ClosedUnder(X)) => e \in X }
Sep(r) == r \notin Reach

\* ---- Antagonism.tla, verbatim ----
Pins(S, e)   == \E g \in Reach : <<g, e>> \in Rel(S, lbl)
Handles(e)   == { S \in Surfaces : LabelIndep(S) /\ Pins(S, e) }
Sealed(e)    == Handles(e) # {}
Separable(e) == e \notin Reach

\* ---- Synthesis.tla, verbatim ----
AllBot == [e \in E |-> Bot]
EdgeAt(l, x, y) == \E S \in Surfaces : <<x, y>> \in Rel(S, l)
ClosedExc(l, r, X) ==
  \A x, y \in E : (x \in X /\ EdgeAt(l, x, y) /\ x # r /\ y # r) => y \in X
ReachExc(l, r) == { e \in E : \A X \in SUBSET E :
                      (G \subseteq X /\ ClosedExc(l, r, X)) => e \in X }
HandlesMinus(l, r) ==
  { S \in Surfaces : \E x \in ReachExc(l, r) : <<x, r>> \in Rel(S, l) }
Dichotomy == \A S \in Surfaces : LabelIndep(S) \/ Rel(S, AllBot) = {}
Sink(r) == \A S \in Surfaces, y \in E : <<r, y>> \notin Rel(S, lbl)

----------------------------------------------------------------------------
VARIABLE t
Init == t = 0
Next == UNCHANGED t
Spec == Init /\ [][Next]_t

Witness ==
  \* ---- the structure is a legal, non-degenerate class member ------------
  /\ Dichotomy
  /\ LabelIndep("P") /\ LabelIndep("Q") /\ LabelIndep("T")
  /\ Reach = {"g0", "r", "z"}

  \* ---- I(r) = 2, carried by two DISTINCT relations ----------------------
  /\ Handles("r") = {"P", "Q"}
  /\ Cardinality(Handles("r")) = 2
  /\ Rel("P", lbl) # Rel("Q", lbl)

  \* ---- the bound is STRICT at I = 2: price 1 < 2 ------------------------
  /\ HandlesMinus(AllBot, "r") = {"P"}
  /\ Cardinality(HandlesMinus(AllBot, "r")) = 1
  /\ HandlesMinus(AllBot, "r") \subseteq Handles("r")
  /\ HandlesMinus(AllBot, "r") # Handles("r")

  \* ---- WHY: Q's pin source is reachable only through r ------------------
  /\ "z" \in Reach
  /\ "z" \notin ReachExc(AllBot, "r")

  \* ---- and r is outside FreshExactness's hypothesis: not a sink ---------
  /\ ~Sink("r")

  \* ---- sanity: the published theorems hold here -------------------------
  /\ \A e \in E : HandlesMinus(AllBot, e) \subseteq Handles(e)  \* PriceWithinIntegrity
  /\ \A e \in E : ~(Sealed(e) /\ Separable(e))                  \* NoSealedSeparable

============================================================================
