------------------------- MODULE AntagonismWitness -------------------------
(***************************************************************************)
(* ACA-L2  Phase 1.5: INHABITATION witness for the conservation law.        *)
(*                                                                         *)
(* Purpose: machine-CHECK (TLC) that T1 (`NoSealedSeparable`) is NOT        *)
(* vacuously true -- that `Sealed` and `Separable` are EACH realizable on a *)
(* concrete instance.  (Universal = proven by tlapm in Antagonism.tla;      *)
(* existence = checked here, per the project's TLAPS/TLC division.)         *)
(*                                                                         *)
(* Concrete tiny instance of the Notarization class:                        *)
(*   a  -- an action, in the frontier G                                     *)
(*   r  -- a reflex SEALED by the label-independent chain (edge a->r)       *)
(*   s  -- a reflex with NO handle, hence SEPARABLE                         *)
(*                                                                         *)
(* The definitions below are VERBATIM-IDENTICAL in form to Notarization.tla *)
(* (Edge, ClosedUnder, Reach, LabelIndep) and Antagonism.tla (Pins,         *)
(* Handles, Sealed, Separable); only the abstract CONSTANTS are made        *)
(* concrete so TLC can evaluate Reach.  Faithfulness is by syntactic        *)
(* identity.                                                                *)
(***************************************************************************)
EXTENDS Naturals

\* ---- concrete constants (a valid instance: satisfies Notarization ASSUMEs) ----
E   == {"a", "r", "s"}
G   == {"a"}
Bot == "_"
L   == {"k"}
Surfaces == {"C"}                       \* one label-independent chain surface
lbl == [e \in E |-> "k"]
Mem(S) == E
Rel(S, l) == IF S = "C" THEN {<<"a", "r">>} ELSE {}   \* links only a->r; ignores l

Labelings == [E -> L \cup {Bot}]

\* ---- definitions copied verbatim from Notarization.tla ----
LabelIndep(S)  == \A l1, l2 \in Labelings : Rel(S, l1) = Rel(S, l2)
Edge(x, y)     == \E S \in Surfaces : <<x, y>> \in Rel(S, lbl)
ClosedUnder(X) == \A x, y \in E : (x \in X /\ Edge(x, y)) => y \in X
Reach == { e \in E : \A X \in SUBSET E :
                       (G \subseteq X /\ ClosedUnder(X)) => e \in X }

\* ---- definitions copied verbatim from Antagonism.tla ----
Pins(S, e)   == \E g \in Reach : <<g, e>> \in Rel(S, lbl)
Handles(e)   == { S \in Surfaces : LabelIndep(S) /\ Pins(S, e) }
Sealed(e)    == Handles(e) # {}
Separable(e) == e \notin Reach

----------------------------------------------------------------------------
VARIABLE t
Init == t = 0
Next == UNCHANGED t
Spec == Init /\ [][Next]_t

\* Inhabitation: both predicates realized, plus the exact witnesses claimed.
\* If TLC reports no invariant violation, T1 is non-vacuous.
Inhabited ==
  /\ \E e \in E : Sealed(e)        \* Sealed is realizable
  /\ \E e \in E : Separable(e)     \* Separable is realizable
  /\ \E e \in E : ~Sealed(e)       \* unsealed effects exist (puncture realizable)
  /\ Sealed("r")                   \* the sealed witness
  /\ Separable("s")                \* the separable witness
  /\ ~Sealed("s")                  \* s is genuinely unsealed
  /\ Reach = {"a", "r"}            \* the computed closure (sanity)

============================================================================
