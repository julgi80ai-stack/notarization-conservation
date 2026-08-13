--------------------------- MODULE Notarization ---------------------------
(***************************************************************************)
(* The ABSTRACT class of label-independent notarization.                   *)
(*                                                                         *)
(* The impossibility was first proved for one concrete system (the         *)
(* governance model of SepClosureTwoMachines).  This module states it at   *)
(* CLASS level instead: it holds of ANY system whose re-linking surfaces   *)
(* are label-independent in the sense below, and every domain instance in  *)
(* this bundle inherits it by INSTANCE rather than re-proving a local      *)
(* analogue.  Purely relational / set-theoretic                            *)
(* (no temporal logic): a static characterization over abstract            *)
(*   E       events                                                        *)
(*   lbl     the correlation labeling  E -> L \cup {Bot}   (Bot = no key)   *)
(*   Surfaces  re-linking surfaces; Mem(S) its members, Rel(S,l) its        *)
(*           re-linking relation UNDER labeling l (so a surface MAY read    *)
(*           the label; LabelIndep says it does not).                      *)
(*   G       the action-log frontier.                                      *)
(*                                                                         *)
(* Bounds: NONE.  E, L, Surfaces are arbitrary (possibly infinite) sets.    *)
(***************************************************************************)
EXTENDS TLAPS

CONSTANTS E, L, Bot, Surfaces, Mem(_), Rel(_, _), G, lbl

\* Labelings: total maps from events to a key or the no-key marker Bot.
Labelings == [E -> L \cup {Bot}]

ASSUME BotNotLabel == Bot \notin L
ASSUME G_inE       == G \subseteq E
ASSUME LblType     == lbl \in Labelings
ASSUME MemType     == \A S \in Surfaces : Mem(S) \subseteq E
ASSUME RelType     == \A S \in Surfaces, l \in Labelings :
                         Rel(S, l) \subseteq Mem(S) \X Mem(S)

----------------------------------------------------------------------------
\* Surface S is LABEL-INDEPENDENT iff its relation never reads the label:
\* the SAME relation results under any labeling whatsoever.
\*   position/time/membership surfaces (hash chain, time-range) : LI  TRUE
\*   key-equality surfaces (corr-index, ByParent)               : LI  FALSE
LabelIndep(S) == \A l1, l2 \in Labelings : Rel(S, l1) = Rel(S, l2)

\* One re-linking step under the ACTUAL labeling lbl.
Edge(x, y) == \E S \in Surfaces : <<x, y>> \in Rel(S, lbl)

\* reach(G): the least set containing G and closed under Edge, expressed as
\* the intersection of all Edge-closed supersets of G (closure, no sequences).
ClosedUnder(X) == \A x, y \in E : (x \in X /\ Edge(x, y)) => y \in X
Reach == { e \in E : \A X \in SUBSET E :
                       (G \subseteq X /\ ClosedUnder(X)) => e \in X }

\* Non-retroactive separation of an emitted event r (paper Definition 3).
Sep(r) == r \notin Reach

\* Drop r's correlation key (the NE strategy "key-drop").
Strip(l, r) == [l EXCEPT ![r] = Bot]

----------------------------------------------------------------------------
(***************************************************************************)
(* 2.2  DECISIVE LEMMA (the engine of L2).                                  *)
(* On a label-independent surface, dropping an event's key leaves the       *)
(* relation -- hence every link -- intact.  This is the exact reason        *)
(* "strip the correlation key" (B1) FAILS to separate on LI surfaces.       *)
(***************************************************************************)
LEMMA StripIsLabeling ==
  ASSUME NEW r \in E PROVE Strip(lbl, r) \in Labelings
  <1> USE DEF Strip, Labelings
  <1>1. lbl \in [E -> L \cup {Bot}] BY LblType DEF Labelings
  <1>2. Bot \in L \cup {Bot} OBVIOUS
  <1>3. QED BY <1>1, <1>2

THEOREM DecisiveLI ==
  ASSUME NEW S \in Surfaces, NEW r \in E, LabelIndep(S)
  PROVE  Rel(S, lbl) = Rel(S, Strip(lbl, r))
  BY LblType, StripIsLabeling DEF LabelIndep

----------------------------------------------------------------------------
(***************************************************************************)
(* 2.4  IMPOSSIBILITY (the class-level TA vs. NE conflict).                  *)
(*                                                                         *)
(* If r co-locates with an action-log event g on ANY surface (one          *)
(* re-linking step), then r is reachable, so Sep(r) is FALSE.              *)
(***************************************************************************)
THEOREM ColocBreaksSep ==
  ASSUME NEW r \in E, NEW S \in Surfaces, NEW g \in G,
         <<g, r>> \in Rel(S, lbl)
  PROVE  ~Sep(r)
  <1> USE DEF Sep
  <1>1. Edge(g, r) BY DEF Edge
  <1>2. r \in Reach
    <2> SUFFICES ASSUME NEW X \in SUBSET E, G \subseteq X, ClosedUnder(X)
                 PROVE  r \in X
        BY DEF Reach
    <2>1. g \in X BY G_inE
    <2>2. QED BY <2>1, <1>1 DEF ClosedUnder
  <1>3. QED BY <1>2

(***************************************************************************)
(* The STRENGTHENED impossibility: on a LABEL-INDEPENDENT surface the       *)
(* co-location -- and thus ~Sep(r) -- SURVIVES dropping r's key.  So the    *)
(* NE strategy "drop the key" is INSUFFICIENT on LI surfaces; one must also  *)
(* EXIT them.  This is the formal core of the (=>) "exit notarization"      *)
(* conjunct of the characterization, lifted to the abstract class.          *)
(***************************************************************************)
THEOREM KeyDropFailsOnLI ==
  ASSUME NEW r \in E, NEW S \in Surfaces, NEW g \in G,
         LabelIndep(S), <<g, r>> \in Rel(S, lbl)
  PROVE  <<g, r>> \in Rel(S, Strip(lbl, r))
  BY DecisiveLI

(***************************************************************************)
(* Impossibility in the paper's A1 / A2 form (TA excludes NE over the       *)
(* class).  A1 (total accountability: r is put onto some surface) is        *)
(* SUBSUMED by A2's co-location, since Rel(S,lbl) <= Mem(S) x Mem(S).        *)
(***************************************************************************)
THEOREM TA_excludes_NE ==
  ASSUME NEW r \in E,
         \* A2: some action-log event co-locates with r on some surface
         \E S \in Surfaces, g \in G : <<g, r>> \in Rel(S, lbl)
  PROVE  ~Sep(r)
  BY ColocBreaksSep

----------------------------------------------------------------------------
(***************************************************************************)
(* 2.3  CHARACTERIZATION BACKBONE: the least-fixpoint unfold of Reach.       *)
(* Closure helper lemmas, then the one-step characterization                *)
(*   r in Reach  <=>  r in G  \/  (\E x in Reach : Edge(x,r))               *)
(* from which Sep decomposes.  The (=>) direction is least-fixpoint         *)
(* minimality (the closure induction MASTER_PLAN Section 11 flags).         *)
(***************************************************************************)
LEMMA Reach_inE == Reach \subseteq E
  BY DEF Reach

LEMMA G_sub_Reach == G \subseteq Reach
  <1> SUFFICES ASSUME NEW g \in G PROVE g \in Reach
      OBVIOUS
  <1>1. g \in E BY G_inE
  <1>2. \A X \in SUBSET E : (G \subseteq X /\ ClosedUnder(X)) => g \in X
      OBVIOUS
  <1>3. QED BY <1>1, <1>2 DEF Reach

LEMMA Reach_Closed == ClosedUnder(Reach)
  <1> SUFFICES ASSUME NEW a \in E, NEW b \in E, a \in Reach, Edge(a, b)
               PROVE  b \in Reach
      BY DEF ClosedUnder
  <1>1. \A X \in SUBSET E : (G \subseteq X /\ ClosedUnder(X)) => b \in X
    <2> SUFFICES ASSUME NEW X \in SUBSET E, G \subseteq X, ClosedUnder(X)
                 PROVE  b \in X
        OBVIOUS
    <2>1. a \in X BY DEF Reach
    <2>2. QED BY <2>1 DEF ClosedUnder
  <1>2. QED BY <1>1 DEF Reach

\* The one-step least-fixpoint characterization of reachability.
THEOREM ReachUnfold ==
  ASSUME NEW r \in E
  PROVE  r \in Reach <=> (r \in G \/ (\E x \in Reach : Edge(x, r)))
  <1>1. ASSUME r \in G \/ (\E x \in Reach : Edge(x, r)) PROVE r \in Reach
    <2>1. CASE r \in G BY <2>1, G_sub_Reach
    <2>2. CASE \E x \in Reach : Edge(x, r)
      <3>1. PICK x \in Reach : Edge(x, r) BY <2>2
      <3>2. x \in E BY Reach_inE
      <3>3. QED BY <3>1, <3>2, Reach_Closed DEF ClosedUnder
    <2>3. QED BY <1>1, <2>1, <2>2
  <1>2. ASSUME r \in Reach, r \notin G, ~(\E x \in Reach : Edge(x, r))
        PROVE  FALSE
    \* minimality: Reach\{r} is itself a closed superset of G, so r notin Reach.
    <2> DEFINE Y == Reach \ {r}
    <2>1. Y \in SUBSET E BY Reach_inE
    <2>2. G \subseteq Y BY G_sub_Reach, <1>2 DEF Y
    <2>3. ClosedUnder(Y)
      <3> SUFFICES ASSUME NEW a \in E, NEW b \in E, a \in Y, Edge(a, b)
                   PROVE  b \in Y
          BY DEF ClosedUnder
      <3>1. a \in Reach BY DEF Y
      <3>2. b \in Reach BY <3>1, Edge(a,b), Reach_Closed DEF ClosedUnder
      <3>3. b # r BY <3>1, <1>2
      <3>4. QED BY <3>2, <3>3 DEF Y
    <2>4. r \in Y BY <1>2, <2>1, <2>2, <2>3 DEF Reach
    <2>5. QED BY <2>4 DEF Y
  <1>3. QED BY <1>1, <1>2

(***************************************************************************)
(* Sep, decomposed: r is separated iff it is neither in G nor co-located    *)
(* with the reachable set on ANY surface.  (Splitting Surfaces into LI vs   *)
(* key-equality surfaces to obtain the paper's two-conjunct                 *)
(* "exit-notarization AND drop-key" form is the refinement step 2.5; here   *)
(* we fix the unconditional backbone.)                                      *)
(***************************************************************************)
THEOREM SepDecomp ==
  ASSUME NEW r \in E
  PROVE  Sep(r) <=> (r \notin G
                     /\ \A x \in Reach, S \in Surfaces : <<x, r>> \notin Rel(S, lbl))
  <1> USE DEF Sep
  <1>1. (\E x \in Reach : Edge(x, r))
          <=> (\E x \in Reach, S \in Surfaces : <<x, r>> \in Rel(S, lbl))
      BY DEF Edge
  <1>2. QED BY ReachUnfold, <1>1

==========================================================================
