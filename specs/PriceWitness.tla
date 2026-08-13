--------------------------- MODULE PriceWitness ---------------------------
(***************************************************************************)
(* ONE witness module that closes five open gaps at once.  All definitions *)
(* copied VERBATIM from Notarization.tla / Antagonism.tla / Synthesis.tla; *)
(* only the CONSTANTS are made concrete.                                    *)
(*                                                                         *)
(*   g0 --K--> x --P--> r      (a TWO-STEP closure: nothing in the shipped  *)
(*   g0 --P--> s                artifact has a path of length >= 2)         *)
(*   g0 --Q--> s                                                            *)
(*                                                                         *)
(*   P, Q : label-independent, and DIFFERENT relations (unlike J1 == J2)    *)
(*   K    : key-equality (label-dependent)                                  *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

E   == {"g0", "x", "r", "s"}
G   == {"g0"}
Bot == "_"
L   == {"k"}
Surfaces == {"P", "Q", "K"}
lbl == [e \in E |-> IF e \in {"g0", "x"} THEN "k" ELSE Bot]
Mem(S) == E
Rel(S, l) ==
  CASE S = "P" -> { <<"x","r">>, <<"g0","s">> }
    [] S = "Q" -> { <<"g0","s">> }
    [] S = "K" -> { p \in E \X E : l[p[1]] = l[p[2]] /\ l[p[1]] # Bot }

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

\* ---- reviewer's addition: closure under an ARBITRARY labelling ----
ClosedAt(l, X) == \A x, y \in E : (x \in X /\ EdgeAt(l, x, y)) => y \in X
ReachAt(l) == { e \in E : \A X \in SUBSET E :
                            (G \subseteq X /\ ClosedAt(l, X)) => e \in X }

----------------------------------------------------------------------------
VARIABLE t
Init == t = 0
Next == UNCHANGED t
Spec == Init /\ [][Next]_t

Witness ==
  \* ---- the structure is a legal, non-degenerate class member ------------
  /\ Dichotomy
  /\ LabelIndep("P") /\ LabelIndep("Q") /\ ~LabelIndep("K")
  /\ Rel("P", lbl) # Rel("Q", lbl)          \* NOT the J1 == J2 duplication

  \* ---- GAP 1: a closure of depth 2 (absent from the whole artifact) -----
  /\ Reach = {"g0", "x", "r", "s"}
  /\ "r" \notin ReachIn({"P"})               \* r needs the K step first
  /\ "r" \in ReachIn({"P", "K"})             \* ... so the path is g0->x->r

  \* ---- GAP 2: NON-DEGENERATE I(e) = 2 (RedundancyResilient, "graded") ---
  /\ Handles("s") = {"P", "Q"} /\ Cardinality(Handles("s")) = 2
  /\ "s" \in ReachIn(Surfaces \ {"P"})       \* survives losing P, via Q
  /\ "s" \in ReachIn(Surfaces \ {"Q"})       \* and vice versa
  /\ HandlesMinus(AllBot, "s") = {"P", "Q"}  \* price = 2 = I(s)   (FreshExactness)
  /\ Sink("s")

  \* ---- GAP 3: price < I(e)  -- the abstract's "equals" is FALSE ---------
  /\ Sink("r") /\ Sealed("r") /\ Handles("r") = {"P"}
  /\ ~SealedLI("r")
  /\ HandlesMinus(AllBot, "r") = {}
  /\ Cardinality(HandlesMinus(AllBot,"r")) # Cardinality(Handles("r"))

  \* ---- GAP 4: PriceWithinIntegrity's inclusion STRICT somewhere ---------
  /\ HandlesMinus(AllBot, "r") \subseteq Handles("r")
  /\ HandlesMinus(AllBot, "r") # Handles("r")

  \* ---- GAP 5: a SEALED effect need NOT be linked under every labelling --
  \*            (:129 is false; :151 is right)
  /\ "r" \in ReachAt(lbl) /\ "r" \notin ReachAt(AllBot)
  /\ "s" \in ReachAt(lbl) /\ "s" \in ReachAt(AllBot)   \* SealedLI: orbit-stable

  \* ---- sanity: every published theorem still holds here ----------------
  /\ \A e \in E : ~(Sealed(e) /\ Separable(e))          \* NoSealedSeparable
  /\ \A e \in E : HandlesMinus(AllBot, e) \subseteq Handles(e)  \* PriceWithinIntegrity

============================================================================
