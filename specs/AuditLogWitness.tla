-------------------------- MODULE AuditLogWitness --------------------------
(***************************************************************************)
(* M4 witness: the AuditLog instance REALIZES the paper's non-trivial      *)
(* distinctions -- on a 3-element hash-chained log with a 2-HOP closure    *)
(* path                                                                    *)
(*                                                                         *)
(*      g0 --Subject--> x --Chain--> r                                     *)
(*                                                                         *)
(*   g0  a committed record (the frontier G), subject key "k"              *)
(*   x   a record sharing g0's subject key; NOT chained to g0              *)
(*   r   an ERASED record (subj = Bot) whose prev-hash points at x         *)
(*                                                                         *)
(* What TLC checks (nothing of this shape existed in the artifact before   *)
(* M4 -- every reach path had length <= 1, so the distinctions below were  *)
(* invisible on every instance):                                           *)
(*   1. a reach path of length 2, crossing a label-DEPENDENT edge first:   *)
(*      r is reachable, but neither surface alone reaches it.              *)
(*   2. Sealed(r) /\ ~SealedLI(r): the pin on r comes from the full        *)
(*      closure, not the LI closure -- Sealed and SealedLI come apart.     *)
(*   3. Reach # ReachLI(lbl): the two closures separate.                   *)
(*   4. price < integrity: HandlesMinus(AllBot, r) = {} is a STRICT        *)
(*      subset of Handles(r) = {"Chain"} -- separation can be cheaper      *)
(*      than I(r) (consistently: r is a sink and ~SealedLI(r), so          *)
(*      ZeroPriceIffUnsealed gives price 0).                               *)
(*   5. erasure futility, live: r's subject key is ALREADY erased          *)
(*      (lbl["r"] = Bot) and r is still chained into the closure.          *)
(*                                                                         *)
(* All definitions are copied VERBATIM from Notarization.tla /             *)
(* Antagonism.tla / Resilience.tla / Synthesis.tla (the PriceWitness.tla   *)
(* pattern); Rel is AuditLogInstance.tla's AuditRel with AuditMem inlined; *)
(* only the CONSTANTS are made concrete.  Faithfulness is by syntactic     *)
(* identity.                                                               *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

E   == {"g0", "x", "r"}
G   == {"g0"}
Bot == "_"
NoPrev == "np"
L   == {"k"}
Surfaces == {"Chain", "Subject"}
lbl  == [e \in E |-> IF e = "r" THEN Bot ELSE "k"]
prev == [e \in E |-> IF e = "r" THEN "x" ELSE NoPrev]
Mem(S) == E
Rel(S, l) ==
  CASE S = "Chain"   -> { p \in E \X E : prev[p[2]] = p[1] }
    [] S = "Subject" -> { p \in E \X E : l[p[1]] = l[p[2]] /\ l[p[1]] # Bot }

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

----------------------------------------------------------------------------
VARIABLE t
Init == t = 0
Next == UNCHANGED t
Spec == Init /\ [][Next]_t

Witness ==
  \* ---- the structure is a legal, non-degenerate class member ------------
  /\ Dichotomy
  /\ LabelIndep("Chain") /\ ~LabelIndep("Subject")

  \* ---- (1) a reach path of length 2: g0 --Subject--> x --Chain--> r -----
  /\ Reach = {"g0", "x", "r"}
  /\ "r" \notin ReachIn({"Chain"})            \* the chain alone cannot reach r
  /\ "r" \notin ReachIn({"Subject"})          \* the index alone cannot either
  /\ "r" \in ReachIn({"Chain", "Subject"})    \* ... only both hops in sequence

  \* ---- (2)+(3) Sealed/SealedLI and Reach/ReachLI come apart -------------
  /\ Sealed("r") /\ ~SealedLI("r")
  /\ Handles("r") = {"Chain"}
  /\ ReachLI(lbl) = {"g0"}                    \* the LI closure stops at G
  /\ "r" \in Reach /\ "r" \notin ReachLI(lbl)

  \* ---- (4) price < integrity: PriceWithinIntegrity strict, observed -----
  /\ Sink("r")
  /\ HandlesMinus(AllBot, "r") = {}
  /\ HandlesMinus(AllBot, "r") \subseteq Handles("r")
  /\ HandlesMinus(AllBot, "r") # Handles("r")
  /\ Cardinality(Handles("r")) = 1            \* I(r) = 1, price = 0

  \* ---- (5) erasure futility, live: r already erased, still sealed -------
  /\ lbl["r"] = Bot

  \* ---- sanity: the published theorems hold here --------------------------
  /\ \A e \in E : ~(Sealed(e) /\ Separable(e))                  \* NoSealedSeparable
  /\ \A e \in E : HandlesMinus(AllBot, e) \subseteq Handles(e)  \* PriceWithinIntegrity

============================================================================
