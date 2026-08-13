-------------------------- MODULE AnonymityWitness --------------------------
(***************************************************************************)
(* D-4(b) witness: the Anonymity instance REALIZES the paper's non-trivial *)
(* distinctions -- on a 4-transaction spend graph with a MULTI-INPUT JOIN  *)
(* and a 2-HOP closure path                                                *)
(*                                                                         *)
(*      g0 --Pseud--> x --Graph--> r  <--Graph-- y                         *)
(*                                                                         *)
(*   g0  a de-anonymised transaction (the frontier G), pseudonym "k"       *)
(*   x   a transaction reusing g0's pseudonym; it spends nothing           *)
(*   y   a transaction with a FRESH pseudonym, co-spent with x by r        *)
(*   r   a transaction with a FRESH pseudonym (lbl = Bot) that spends      *)
(*       BOTH x and y in one transaction:  inputs["r"] = {"x", "y"}        *)
(*                                                                         *)
(* This is chain analysis's MULTI-INPUT HEURISTIC as a structure, not as   *)
(* an oracle: r joins two inputs, one of which is pseudonym-linked to the  *)
(* de-anonymised frontier, and the closure -- not a primitive              *)
(* "is-deanonymisable" flag -- carries the attribution across the join.    *)
(*                                                                         *)
(* What TLC checks:                                                        *)
(*   0. MULTI-INPUT, not a predecessor pointer: r has TWO DISTINCT Graph   *)
(*      in-edges.  No relation of the shape { p : f[p[2]] = p[1] } for a   *)
(*      function f can do this -- so "Graph" is structurally unlike        *)
(*      AuditLogInstance's "Chain", and (reading no coordinate-free flag)  *)
(*      unlike DeniabilityInstance's "Sig".                                *)
(*   1. a reach path of length 2, crossing a label-DEPENDENT edge first:   *)
(*      r is reachable, but neither surface alone reaches it.              *)
(*   2. Sealed(r) /\ ~SealedLI(r): the pin on r comes from the full        *)
(*      closure, not the LI closure -- Sealed and SealedLI come apart.     *)
(*   3. Reach # ReachLI(lbl): the two closures separate.                   *)
(*   4. price < integrity: HandlesMinus(AllBot, r) = {} is a STRICT        *)
(*      subset of Handles(r) = {"Graph"} -- separation can be cheaper      *)
(*      than I(r) (consistently: r is a sink and ~SealedLI(r), so          *)
(*      ZeroPriceIffUnsealed gives price 0).                               *)
(*   5. clustering futility, live: r's pseudonym is ALREADY fresh          *)
(*      (lbl["r"] = Bot) and r is still clustered into the closure.        *)
(*   6. the join is load-bearing: y itself is NOT reachable, so the pin    *)
(*      on r travels through x -- the co-spend, not either input alone.    *)
(*                                                                         *)
(* All definitions are copied VERBATIM from Notarization.tla /             *)
(* Antagonism.tla / Resilience.tla / Synthesis.tla (the AuditLogWitness    *)
(* pattern); Rel is AnonymityInstance.tla's AnonRel with AnonMem inlined;  *)
(* only the CONSTANTS are made concrete.  Faithfulness is by syntactic     *)
(* identity.                                                               *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

E   == {"g0", "x", "y", "r"}
G   == {"g0"}
Bot == "_"
L   == {"k"}
Surfaces == {"Graph", "Pseud"}
lbl    == [e \in E |-> IF e \in {"g0", "x"} THEN "k" ELSE Bot]
inputs == [e \in E |-> IF e = "r" THEN {"x", "y"} ELSE {}]
Mem(S) == E
Rel(S, l) ==
  CASE S = "Graph" -> { p \in E \X E : p[1] \in inputs[p[2]] }
    [] S = "Pseud" -> { p \in E \X E : l[p[1]] = l[p[2]] /\ l[p[1]] # Bot }

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
EdgeLI(l, x, y) == \E S \in Surfaces : LabelIndep(S) /\ <<x, y>> \in Rel(S, l)
ClosedLI(l, X)  == \A x, y \in E : (x \in X /\ EdgeLI(l, x, y)) => y \in X
ReachLI(l) == { e \in E : \A X \in SUBSET E :
                            (G \subseteq X /\ ClosedLI(l, X)) => e \in X }
PinsLI(S, e) == \E g \in ReachLI(lbl) : <<g, e>> \in Rel(S, lbl)
SealedLI(e)  == \E S \in Surfaces : LabelIndep(S) /\ PinsLI(S, e)

\* ---- Resilience.tla, verbatim ----
EdgeIn(SS, x, y) == \E S \in SS : <<x, y>> \in Rel(S, lbl)
ClosedIn(SS, X)  == \A x, y \in E : (x \in X /\ EdgeIn(SS, x, y)) => y \in X
ReachIn(SS) == { e \in E : \A X \in SUBSET E :
                            (G \subseteq X /\ ClosedIn(SS, X)) => e \in X }

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

\* ---- local abbreviation: the Graph in-neighbourhood of e --------------
GraphPreds(e) == { z \in E : <<z, e>> \in Rel("Graph", lbl) }

----------------------------------------------------------------------------
VARIABLE t
Init == t = 0
Next == UNCHANGED t
Spec == Init /\ [][Next]_t

Witness ==
  \* ---- the structure is a legal, non-degenerate class member ------------
  /\ Dichotomy
  /\ LabelIndep("Graph") /\ ~LabelIndep("Pseud")

  \* ---- (0) MULTI-INPUT: r has TWO DISTINCT Graph predecessors ----------
  \*      A single-pointer surface { p : f[p[2]] = p[1] } admits at most
  \*      ONE in-edge per event, so this observation alone separates
  \*      "Graph" from AuditLogInstance's "Chain".
  /\ inputs["r"] = {"x", "y"}
  /\ GraphPreds("r") = {"x", "y"}
  /\ Cardinality(GraphPreds("r")) = 2
  /\ \E a, b \in E : a # b /\ <<a, "r">> \in Rel("Graph", lbl)
                           /\ <<b, "r">> \in Rel("Graph", lbl)
  \*      ... and the surface DOES read its source coordinate: swapping
  \*      p[1] changes membership.  (A cylinder cannot do this.)
  /\ <<"x", "r">> \in Rel("Graph", lbl)
  /\ <<"g0", "r">> \notin Rel("Graph", lbl)

  \* ---- (1) a reach path of length 2: g0 --Pseud--> x --Graph--> r -----
  /\ Reach = {"g0", "x", "r"}
  /\ "r" \notin ReachIn({"Graph"})            \* the spend graph alone cannot
  /\ "r" \notin ReachIn({"Pseud"})            \* nor can pseudonym reuse
  /\ "r" \in ReachIn({"Graph", "Pseud"})      \* ... only both hops in sequence

  \* ---- (2)+(3) Sealed/SealedLI and Reach/ReachLI come apart -------------
  /\ Sealed("r") /\ ~SealedLI("r")
  /\ Handles("r") = {"Graph"}
  /\ ReachLI(lbl) = {"g0"}                    \* the LI closure stops at G
  /\ "r" \in Reach /\ "r" \notin ReachLI(lbl)

  \* ---- (4) price < integrity: strict inclusion of Thm 7, observed -------
  /\ Sink("r")
  /\ HandlesMinus(AllBot, "r") = {}
  /\ HandlesMinus(AllBot, "r") \subseteq Handles("r")
  /\ HandlesMinus(AllBot, "r") # Handles("r")
  /\ Cardinality(Handles("r")) = 1            \* I(r) = 1, price = 0

  \* ---- (5) clustering futility, live: r's pseudonym is already fresh ----
  /\ lbl["r"] = Bot

  \* ---- (6) the JOIN carries the attribution, not either input alone -----
  \*      y is co-spent with x by r, yet y is NOT itself reachable: the pin
  \*      on r arrives through x.  Under the multi-input heuristic this is
  \*      exactly the inference chain analysis draws.
  /\ "y" \notin Reach
  /\ "y" \in GraphPreds("r")
  /\ "x" \in Reach

  \* ---- sanity: the published theorems hold here --------------------------
  /\ \A e \in E : ~(Sealed(e) /\ Separable(e))                  \* Thm 1
  /\ \A e \in E : HandlesMinus(AllBot, e) \subseteq Handles(e)  \* Thm 7

============================================================================
