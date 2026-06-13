---------------------------- MODULE Antagonism ----------------------------
(***************************************************************************)
(* ACA-L2  Phase 1: the CONSERVATION LAW, qualitative core.                 *)
(*                                                                         *)
(* Integrity strength (>= 1 label-independent handle pinning the effect to  *)
(* the frontier-reachable set) and non-establishment capacity (the effect   *)
(* is non-retroactively separable) are JOINTLY UNREACHABLE for a single     *)
(* effect.  The reason is the Phase-0 touchstone identity: the label-       *)
(* independent link that SEALS an effect is the SAME edge that pulls it into *)
(* Reach -- the integrity carrier and the re-link handle are one link.      *)
(*                                                                         *)
(* L1's binary impossibility (Total Accountability => no non-establishment)  *)
(* is recovered as the DEGENERATE CORNER  I = max  =>  capacity = 0.         *)
(*                                                                         *)
(* Bounds: NONE.  E, L, Surfaces arbitrary (inherited from Notarization).    *)
(***************************************************************************)
EXTENDS Notarization

\* S fixes e to the frontier-reachable set Reach(G): some reachable g links
\* to e on surface S under the actual labeling.
Pins(S, e) == \E g \in Reach : <<g, e>> \in Rel(S, lbl)

\* The LABEL-INDEPENDENT handles pinning e.  By the touchstone these are at
\* once the tamper-evidence carriers AND the re-link handles.
Handles(e) == { S \in Surfaces : LabelIndep(S) /\ Pins(S, e) }

\* Integrity strength >= 1 : robustly sealed by at least one LI surface.
Sealed(e)    == Handles(e) # {}
\* Non-establishment capacity = 1 : non-retroactively separable (= L1/L2 Sep).
Separable(e) == e \notin Reach
\* Total Accountability (notarization facet): every effect is sealed.
TA == \A x \in E : Sealed(x)

----------------------------------------------------------------------------
(***************************************************************************)
(* T1 (engine).  No effect is both robustly sealed and separable.           *)
(* I(e) >= 1  =>  the sealing LI edge puts e in Reach  =>  ~Separable(e).    *)
(***************************************************************************)
THEOREM NoSealedSeparable ==
  ASSUME NEW e \in E
  PROVE  ~(Sealed(e) /\ Separable(e))
  <1> SUFFICES ASSUME Sealed(e), Separable(e) PROVE FALSE
      OBVIOUS
  <1>1. PICK S \in Surfaces : LabelIndep(S) /\ Pins(S, e)
    BY DEF Sealed, Handles
  <1>2. PICK g \in Reach : <<g, e>> \in Rel(S, lbl)
    BY <1>1 DEF Pins
  <1>3. Edge(g, e) BY <1>1, <1>2 DEF Edge
  <1>4. g \in E BY <1>2, Reach_inE
  <1>5. e \in Reach BY <1>2, <1>3, <1>4, Reach_Closed DEF ClosedUnder
  <1>6. QED BY <1>5 DEF Separable

----------------------------------------------------------------------------
(***************************************************************************)
(* Corollary (the PUNCTURE law).  Any non-establishment capacity forces an  *)
(* unsealed effect: to grant a machine "this merely happened" you must       *)
(* puncture total accountability.  Direct formal reading of the thesis.     *)
(***************************************************************************)
THEOREM CapacityRequiresPuncture ==
  ASSUME \E x \in E : Separable(x)
  PROVE  \E x \in E : ~Sealed(x)
  <1>1. PICK x \in E : Separable(x) OBVIOUS
  <1>2. ~Sealed(x) BY <1>1, NoSealedSeparable
  <1>3. QED BY <1>1, <1>2

----------------------------------------------------------------------------
(***************************************************************************)
(* T2 (L1 recovery).  Total accountability is the degenerate corner of the  *)
(* conservation law: I = max (everything sealed) forces capacity = 0         *)
(* (nothing separable) = L1's  TA => ~NE.  L2 thus CONTAINS L1.              *)
(***************************************************************************)
THEOREM BinaryIsDegenerate ==
  ASSUME TA, NEW e \in E
  PROVE  ~Separable(e)
  <1>1. Sealed(e) BY DEF TA
  <1>2. QED BY <1>1, NoSealedSeparable

----------------------------------------------------------------------------
(***************************************************************************)
(* Phase 2.1 -- non-retroactive decomposition.  A separable effect exits     *)
(* EVERY surface from the reachable set: not only the label-independent      *)
(* (notarization) ones (T1) but the key-equality ones too.  This is the      *)
(* abstract "exit notarization AND drop key", and -- because Reach is taken   *)
(* over ALL Surfaces including the worst-case latent traverser -- it is the   *)
(* NON-RETROACTIVE form (survives any future re-link in the surface set).    *)
(***************************************************************************)
THEOREM SeparableExitsAllSurfaces ==
  ASSUME NEW e \in E, Separable(e)
  PROVE  \A x \in Reach, S \in Surfaces : <<x, e>> \notin Rel(S, lbl)
  <1>1. Sep(e) BY DEF Separable, Sep
  <1>2. QED BY <1>1, SepDecomp

----------------------------------------------------------------------------
(***************************************************************************)
(* Revision R2 -- the ORBIT corollary (paper Cor 2).                         *)
(* The closure restricted to LABEL-INDEPENDENT surfaces is a fixed point of  *)
(* the entire label orbit: relabelling (key drop, pseudonym rotation,        *)
(* anonymisation) acts trivially on it.  Hence an effect pinned through      *)
(* label-independent structure to the LI-reachable set stays reachable       *)
(* under EVERY labelling -- the antagonism is orbit-invariant.               *)
(* NOTE the hypothesis is SealedLI (pin from the LI closure), not Sealed     *)
(* (pin from the full closure): a pin whose path to the frontier uses a      *)
(* label-DEPENDENT edge can dissolve under relabelling, so the full-closure  *)
(* form is false in general.  SealedLI => Sealed (SealedLI_Sealed).          *)
(***************************************************************************)

EdgeLI(l, x, y) == \E S \in Surfaces : LabelIndep(S) /\ <<x, y>> \in Rel(S, l)
ClosedLI(l, X)  == \A x, y \in E : (x \in X /\ EdgeLI(l, x, y)) => y \in X
ReachLI(l) == { e \in E : \A X \in SUBSET E :
                            (G \subseteq X /\ ClosedLI(l, X)) => e \in X }

PinsLI(S, e) == \E g \in ReachLI(lbl) : <<g, e>> \in Rel(S, lbl)
SealedLI(e)  == \E S \in Surfaces : LabelIndep(S) /\ PinsLI(S, e)

LEMMA EdgeLI_Orbit ==
  ASSUME NEW l \in Labelings, NEW x \in E, NEW y \in E
  PROVE  EdgeLI(l, x, y) <=> EdgeLI(lbl, x, y)
  BY LblType DEF EdgeLI, LabelIndep

THEOREM OrbitInvariance ==
  ASSUME NEW l \in Labelings
  PROVE  ReachLI(l) = ReachLI(lbl)
  <1>1. \A X \in SUBSET E : ClosedLI(l, X) <=> ClosedLI(lbl, X)
    BY EdgeLI_Orbit DEF ClosedLI
  <1>2. \A x : x \in ReachLI(l) <=> x \in ReachLI(lbl)
    BY <1>1 DEF ReachLI
  <1>3. QED BY <1>2, SetExtensionality

LEMMA ReachLI_inE == ReachLI(lbl) \subseteq E
  BY DEF ReachLI

LEMMA ReachLI_Closed == ClosedLI(lbl, ReachLI(lbl))
  <1> SUFFICES ASSUME NEW a \in E, NEW b \in E, a \in ReachLI(lbl),
                      EdgeLI(lbl, a, b)
               PROVE  b \in ReachLI(lbl)
      BY DEF ClosedLI
  <1>1. \A X \in SUBSET E : (G \subseteq X /\ ClosedLI(lbl, X)) => b \in X
    <2> SUFFICES ASSUME NEW X \in SUBSET E, G \subseteq X, ClosedLI(lbl, X)
                 PROVE  b \in X
        OBVIOUS
    <2>1. a \in X BY DEF ReachLI
    <2>2. QED BY <2>1 DEF ClosedLI
  <1>2. QED BY <1>1 DEF ReachLI

LEMMA ReachLI_sub_Reach == ReachLI(lbl) \subseteq Reach
  <1> SUFFICES ASSUME NEW e \in ReachLI(lbl) PROVE e \in Reach
      OBVIOUS
  <1>1. \A X \in SUBSET E : ClosedUnder(X) => ClosedLI(lbl, X)
    BY DEF ClosedUnder, ClosedLI, Edge, EdgeLI
  <1>2. e \in E BY DEF ReachLI
  <1>3. QED BY <1>1, <1>2 DEF Reach, ReachLI

LEMMA SealedLI_Sealed ==
  ASSUME NEW e \in E, SealedLI(e)
  PROVE  Sealed(e)
  <1>1. PICK S \in Surfaces : LabelIndep(S) /\ PinsLI(S, e)
    BY DEF SealedLI
  <1>2. PICK g \in ReachLI(lbl) : <<g, e>> \in Rel(S, lbl)
    BY <1>1 DEF PinsLI
  <1>3. g \in Reach BY <1>2, ReachLI_sub_Reach
  <1>4. Pins(S, e) BY <1>2, <1>3 DEF Pins
  <1>5. QED BY <1>1, <1>4 DEF Sealed, Handles

THEOREM OrbitAntagonism ==
  ASSUME NEW l \in Labelings, NEW e \in E, SealedLI(e)
  PROVE  e \in ReachLI(l)
  <1>1. PICK S \in Surfaces : LabelIndep(S) /\ PinsLI(S, e)
    BY DEF SealedLI
  <1>2. PICK g \in ReachLI(lbl) : <<g, e>> \in Rel(S, lbl)
    BY <1>1 DEF PinsLI
  <1>3. g \in E BY <1>2, ReachLI_inE
  <1>4. EdgeLI(lbl, g, e) BY <1>1, <1>2 DEF EdgeLI
  <1>5. e \in ReachLI(lbl)
    BY <1>2, <1>3, <1>4, ReachLI_Closed DEF ClosedLI
  <1>6. QED BY <1>5, OrbitInvariance

============================================================================
