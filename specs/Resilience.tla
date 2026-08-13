------------------------------ MODULE Resilience ------------------------------
(***************************************************************************)
(* Seal MULTIPLICITY as handle redundancy, and its resilience -- the       *)
(* strength axis of the conservation law.                                  *)
(*                                                                         *)
(* Seal multiplicity of an effect is the redundancy of the surfaces pinning*)
(* it to the frontier: more independent pins => harder to dislodge by single *)
(* point tampering.  We make this precise by restricting the re-linking      *)
(* closure to a SUB-set of surfaces (a surface compromised/removed) and       *)
(* proving: an effect pinned to a frontier event by TWO distinct surfaces    *)
(* survives the removal of either -- it remains reachable via the other.     *)
(*                                                                         *)
(* This is the formal sense in which raising I(e) (the handle count) hardens *)
(* the effect: redundancy = tamper-resilience.  Combinatorial, no reals;     *)
(* unbounded (E, Surfaces arbitrary, inherited from Notarization).           *)
(***************************************************************************)
EXTENDS Notarization

\* Re-linking closure restricted to a sub-set SS of surfaces (others removed).
EdgeIn(SS, x, y) == \E S \in SS : <<x, y>> \in Rel(S, lbl)
ClosedIn(SS, X)  == \A x, y \in E : (x \in X /\ EdgeIn(SS, x, y)) => y \in X
ReachIn(SS) == { e \in E : \A X \in SUBSET E :
                            (G \subseteq X /\ ClosedIn(SS, X)) => e \in X }

----------------------------------------------------------------------------
(***************************************************************************)
(* RESILIENCE.  An effect e pinned to a frontier event g by two DISTINCT     *)
(* surfaces S1, S2 stays reachable after S1 is removed -- via S2.  Hence an   *)
(* effect with redundant (>=2) pins is robust to the compromise of any one.  *)
(***************************************************************************)
THEOREM RedundancyResilient ==
  ASSUME NEW e \in E, NEW g \in G,
         NEW S1 \in Surfaces, NEW S2 \in Surfaces, S1 # S2,
         <<g, e>> \in Rel(S2, lbl)
  PROVE  e \in ReachIn(Surfaces \ {S1})
  <1> DEFINE SS == Surfaces \ {S1}
  <1>1. S2 \in SS BY DEF SS
  <1> SUFFICES ASSUME NEW X \in SUBSET E, G \subseteq X, ClosedIn(SS, X)
               PROVE  e \in X
      BY DEF ReachIn
  <1>2. g \in X OBVIOUS
  <1>3. EdgeIn(SS, g, e) BY <1>1 DEF EdgeIn
  <1>4. g \in E BY G_inE
  <1>5. QED BY <1>2, <1>3, <1>4 DEF ClosedIn

============================================================================
