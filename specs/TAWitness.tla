----------------------------- MODULE TAWitness -----------------------------
(***************************************************************************)
(* M9-S2 witness: TOTAL ACCOUNTABILITY IS SATISFIABLE -- and at what price. *)
(*                                                                         *)
(* TA == \A x \in E : Sealed(x) is defined in Antagonism.tla and consumed  *)
(* as the hypothesis of Theorem 2 (BinaryIsDegenerate), but no shipped     *)
(* witness realised it, and in every finite ACYCLIC chain instance TA is   *)
(* in fact false at the genesis record (AuditLogInstance's                 *)
(* Audit_GenesisUnsealed: a record with no predecessor pointer has no      *)
(* label-independent in-edge, hence is never Sealed).                      *)
(*                                                                         *)
(* This witness shows TA is nonetheless satisfiable at the class level --  *)
(* and records honestly HOW: the frontier root pins ITSELF.                *)
(*                                                                         *)
(*      a --C--> a     (the root's self-pin)                               *)
(*      a --C--> b                                                         *)
(*                                                                         *)
(* Every element of E is then LI-pinned from Reach, so TA holds and       *)
(* Theorem 2's conclusion (nothing separable) is realised NON-vacuously.   *)
(*                                                                         *)
(* The degeneracy is the finding, not a defect of the model: in a finite   *)
(* structure TA forces every element -- the roots included -- to carry an  *)
(* LI in-edge from Reach, and a root can only get one from itself (or a    *)
(* cycle).  That is exactly the TRUST-ANCHOR convention of real systems:   *)
(* a hardcoded genesis hash, a self-signed root certificate.  Total        *)
(* accountability is purchasable only by self-certification at the root.   *)
(*                                                                         *)
(* Definitions copied VERBATIM from Notarization.tla / Antagonism.tla /    *)
(* Synthesis.tla (the PriceWitness.tla pattern); only the CONSTANTS are    *)
(* concrete.  Faithfulness is by syntactic identity.                       *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

E   == {"a", "b"}
G   == {"a"}
Bot == "_"
L   == {"k"}
Surfaces == {"C"}
lbl == [e \in E |-> "k"]
Mem(S) == E
Rel(S, l) == {<<"a", "a">>, <<"a", "b">>}    \* ignores l  =>  LI

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
TA           == \A x \in E : Sealed(x)

\* ---- Synthesis.tla, verbatim ----
AllBot == [e \in E |-> Bot]
Dichotomy == \A S \in Surfaces : LabelIndep(S) \/ Rel(S, AllBot) = {}

----------------------------------------------------------------------------
VARIABLE t
Init == t = 0
Next == UNCHANGED t
Spec == Init /\ [][Next]_t

Witness ==
  \* ---- the structure is a legal class member ---------------------------
  /\ Dichotomy
  /\ LabelIndep("C")

  \* ---- TA is REALISED, and Theorem 2 is non-vacuous here ---------------
  /\ TA
  /\ Sealed("a") /\ Sealed("b")
  /\ \A e \in E : ~Separable(e)        \* Thm 2's conclusion, realised
  /\ Reach = E

  \* ---- and the honest price of TA: the root pins itself ----------------
  /\ <<"a", "a">> \in Rel("C", lbl)
  /\ "a" \in G

============================================================================
