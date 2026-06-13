------------------------- MODULE NecessityWitness -------------------------
(***************************************************************************)
(* ACA-L2  Phase 4: NECESSITY witness -- label-independence is load-bearing. *)
(*                                                                         *)
(* The conservation law (T1) makes integrity and separability antagonistic  *)
(* because the pinning surface is LABEL-INDEPENDENT: dropping the key cannot  *)
(* remove the link, so separation requires EXITING the surface.             *)
(*                                                                         *)
(* Here we drop that hypothesis: the single surface "K" is LABEL-DEPENDENT   *)
(* (it links by shared key).  TLC then exhibits an effect r that is          *)
(*   - re-linked to the frontier NOW (pinned, integrity-ish), AND            *)
(*   - separated by KEY-DROP ALONE (no surface exit needed).                *)
(* So with a label-dependent surface the "must exit" force vanishes and the  *)
(* trivial label-routing partition returns -- confirming label-independence  *)
(* is exactly what couples integrity and separability in T1.                *)
(*                                                                         *)
(* (Existence/necessity = checked by TLC, per the TLAPS/TLC division.)      *)
(***************************************************************************)
EXTENDS Naturals

E   == {"a", "r"}
G   == {"a"}
Bot == "_"
L   == {"k"}
Surfaces == {"K"}
lbl == [e \in E |-> "k"]                 \* a and r initially share key "k"

\* LABEL-DEPENDENT surface: links pairs sharing a non-Bot key (a key-equality
\* surface, the ~LabelIndep half of the dichotomy).
Rel(S, l) == IF S = "K"
             THEN { p \in E \X E : l[p[1]] = l[p[2]] /\ l[p[1]] # Bot }
             ELSE {}

Labelings == [E -> L \cup {Bot}]
LabelIndep(S) == \A l1, l2 \in Labelings : Rel(S, l1) = Rel(S, l2)

\* re-linking closure under an explicit labeling l
EdgeL(l, x, y) == \E S \in Surfaces : <<x, y>> \in Rel(S, l)
ClosedL(l, X)  == \A x, y \in E : (x \in X /\ EdgeL(l, x, y)) => y \in X
ReachL(l) == { e \in E : \A X \in SUBSET E :
                          (G \subseteq X /\ ClosedL(l, X)) => e \in X }

Strip(l, e) == [l EXCEPT ![e] = Bot]     \* drop e's key

----------------------------------------------------------------------------
VARIABLE t
Init == t = 0
Next == UNCHANGED t
Spec == Init /\ [][Next]_t

\* If TLC reports no violation: with a label-dependent surface, key-drop ALONE
\* separates a currently-pinned effect -- the antagonism dissolves.
Necessity ==
  /\ ~LabelIndep("K")                       \* surface reads the label
  /\ "r" \in ReachL(lbl)                    \* r re-linked NOW (pinned)
  /\ "r" \notin ReachL(Strip(lbl, "r"))     \* key-drop alone separates r

============================================================================
