----------------------------- MODULE Synthesis -----------------------------
(***************************************************************************)
(* Phase 3 (P1): the conservation law as an ANALYSIS -- exit synthesis.     *)
(*                                                                         *)
(* Everything is stated over the SAME abstract class (nothing instance-    *)
(* specific).  The optimal separation strategy decomposes into the law's   *)
(* two pillars, made algorithmic:                                          *)
(*   relabel phase : Lemma 1 (DecisiveLI) -- relabelling is futile on LI   *)
(*                   surfaces and decisive on key-type surfaces (those     *)
(*                   whose relation VANISHES at the all-Bot labelling);    *)
(*                   the maximal key-drop AllBot dominates every other     *)
(*                   relabelling (KeyDropDominance).                       *)
(*   exit phase    : Thm 3 (SepDecomp) -- every pin that survives the      *)
(*                   key-drop must be exited, and nothing else need be     *)
(*                   (LeastExit).                                          *)
(*                                                                         *)
(* Headline results:                                                       *)
(*   LeastExit          an exit set works iff it covers HandlesMinus --    *)
(*                      so the least exit set EXISTS, is UNIQUE, and is    *)
(*                      definable (no optimization at per-effect grain).   *)
(*   OptimalSynthesis   over ALL labellings: achievable iff the target is  *)
(*                      off the frontier and the exit set covers           *)
(*                      HandlesMinus(AllBot, r).                           *)
(*   PriceWithinIntegrity  HandlesMinus(AllBot, r) \subseteq Handles(r):   *)
(*                      the price of separation is seal multiplicity --    *)
(*                      the conservation law, operationalized.             *)
(*   FreshExactness     for a fresh (sink) effect the price is EXACTLY     *)
(*                      the SealedLI handle set; zero iff not LI-sealed    *)
(*                      (ZeroPriceIffUnsealed).                            *)
(*                                                                         *)
(* Bounds: NONE.  E, L, Surfaces arbitrary (possibly infinite).            *)
(***************************************************************************)
EXTENDS Antagonism

\* The maximal key-drop: EVERY correlation key removed.
AllBot == [e \in E |-> Bot]

\* One re-linking step under an arbitrary labelling l (Edge generalized).
EdgeAt(l, x, y) == \E S \in Surfaces : <<x, y>> \in Rel(S, l)

(***************************************************************************)
(* Closure of G under l-edges NOT incident to the target r: the frontier   *)
(* the structure still reaches if r exits EVERY surface.  This is the      *)
(* "world without r's links", from which the residual pins are read off.   *)
(***************************************************************************)
ClosedExc(l, r, X) ==
  \A x, y \in E : (x \in X /\ EdgeAt(l, x, y) /\ x # r /\ y # r) => y \in X
ReachExc(l, r) == { e \in E : \A X \in SUBSET E :
                      (G \subseteq X /\ ClosedExc(l, r, X)) => e \in X }

(***************************************************************************)
(* Post-exit reachability: r has exited the surfaces in XS (removed from   *)
(* their membership, so their r-incident links are gone); every other      *)
(* surface still carries all its links.                                    *)
(***************************************************************************)
EdgeExit(l, r, XS, x, y) ==
  \E S \in Surfaces : <<x, y>> \in Rel(S, l)
                      /\ (S \in XS => (x # r /\ y # r))
ClosedExit(l, r, XS, X) ==
  \A x, y \in E : (x \in X /\ EdgeExit(l, r, XS, x, y)) => y \in X
ReachExit(l, r, XS) == { e \in E : \A X \in SUBSET E :
                           (G \subseteq X /\ ClosedExit(l, r, XS, X)) => e \in X }

\* Exit set XS achieves separation of r under labelling l.
SepAch(l, r, XS) == r \notin ReachExit(l, r, XS)

(***************************************************************************)
(* The r-deleted pin set: the surfaces still linking r to the frontier     *)
(* that survives r's own departure.  THE candidate least exit set.         *)
(***************************************************************************)
HandlesMinus(l, r) ==
  { S \in Surfaces : \E x \in ReachExc(l, r) : <<x, r>> \in Rel(S, l) }

(***************************************************************************)
(* The key-type split: every surface is label-independent or its relation  *)
(* vanishes under the maximal key-drop (key-equality surfaces do: with all *)
(* keys at Bot no two keys are equal-and-present).  All four paper         *)
(* instances satisfy this split.                                           *)
(***************************************************************************)
Dichotomy == \A S \in Surfaces : LabelIndep(S) \/ Rel(S, AllBot) = {}

\* r emits no link of its own (typical of the freshest persisted effect).
Sink(r) == \A S \in Surfaces, y \in E : <<r, y>> \notin Rel(S, lbl)

----------------------------------------------------------------------------
(* Basic facts about the two parametrized closures (house pattern).        *)

LEMMA AllBotLabeling == AllBot \in Labelings
  BY DEF AllBot, Labelings

LEMMA ReachExc_inE ==
  ASSUME NEW l, NEW r PROVE ReachExc(l, r) \subseteq E
  BY DEF ReachExc

LEMMA G_sub_ReachExc ==
  ASSUME NEW l, NEW r PROVE G \subseteq ReachExc(l, r)
  <1> SUFFICES ASSUME NEW g \in G PROVE g \in ReachExc(l, r)
      OBVIOUS
  <1>1. g \in E BY G_inE
  <1>2. \A X \in SUBSET E : (G \subseteq X /\ ClosedExc(l, r, X)) => g \in X
      OBVIOUS
  <1>3. QED BY <1>1, <1>2 DEF ReachExc

LEMMA ReachExc_Closed ==
  ASSUME NEW l, NEW r PROVE ClosedExc(l, r, ReachExc(l, r))
  <1> SUFFICES ASSUME NEW a \in E, NEW b \in E,
                      a \in ReachExc(l, r), EdgeAt(l, a, b), a # r, b # r
               PROVE  b \in ReachExc(l, r)
      BY DEF ClosedExc
  <1>1. \A X \in SUBSET E : (G \subseteq X /\ ClosedExc(l, r, X)) => b \in X
    <2> SUFFICES ASSUME NEW X \in SUBSET E, G \subseteq X, ClosedExc(l, r, X)
                 PROVE  b \in X
        OBVIOUS
    <2>1. a \in X BY DEF ReachExc
    <2>2. QED BY <2>1 DEF ClosedExc
  <1>2. QED BY <1>1 DEF ReachExc

(* The target never re-enters the r-deleted closure: no surviving edge     *)
(* points at r, so ReachExc(l, r) omits r whenever the frontier does.      *)
LEMMA ReachExc_NoTarget ==
  ASSUME NEW l, NEW r \in E, r \notin G
  PROVE  r \notin ReachExc(l, r)
  <1> DEFINE Y == ReachExc(l, r) \ {r}
  <1>1. Y \in SUBSET E BY ReachExc_inE
  <1>2. G \subseteq Y BY G_sub_ReachExc DEF Y
  <1>3. ClosedExc(l, r, Y)
    <2> SUFFICES ASSUME NEW a \in E, NEW b \in E,
                        a \in Y, EdgeAt(l, a, b), a # r, b # r
                 PROVE  b \in Y
        BY DEF ClosedExc
    <2>1. a \in ReachExc(l, r) BY DEF Y
    <2>2. b \in ReachExc(l, r) BY <2>1, ReachExc_Closed DEF ClosedExc
    <2>3. QED BY <2>2 DEF Y
  <1>4. ASSUME r \in ReachExc(l, r) PROVE FALSE
    <2>1. r \in Y BY <1>4, <1>1, <1>2, <1>3 DEF ReachExc
    <2>2. QED BY <2>1 DEF Y
  <1>5. QED BY <1>4

LEMMA ReachExit_inE ==
  ASSUME NEW l, NEW r, NEW XS PROVE ReachExit(l, r, XS) \subseteq E
  BY DEF ReachExit

LEMMA G_sub_ReachExit ==
  ASSUME NEW l, NEW r, NEW XS PROVE G \subseteq ReachExit(l, r, XS)
  <1> SUFFICES ASSUME NEW g \in G PROVE g \in ReachExit(l, r, XS)
      OBVIOUS
  <1>1. g \in E BY G_inE
  <1>2. \A X \in SUBSET E :
          (G \subseteq X /\ ClosedExit(l, r, XS, X)) => g \in X
      OBVIOUS
  <1>3. QED BY <1>1, <1>2 DEF ReachExit

LEMMA ReachExit_Closed ==
  ASSUME NEW l, NEW r, NEW XS
  PROVE  ClosedExit(l, r, XS, ReachExit(l, r, XS))
  <1> SUFFICES ASSUME NEW a \in E, NEW b \in E,
                      a \in ReachExit(l, r, XS), EdgeExit(l, r, XS, a, b)
               PROVE  b \in ReachExit(l, r, XS)
      BY DEF ClosedExit
  <1>1. \A X \in SUBSET E :
          (G \subseteq X /\ ClosedExit(l, r, XS, X)) => b \in X
    <2> SUFFICES ASSUME NEW X \in SUBSET E, G \subseteq X,
                        ClosedExit(l, r, XS, X)
                 PROVE  b \in X
        OBVIOUS
    <2>1. a \in X BY DEF ReachExit
    <2>2. QED BY <2>1 DEF ClosedExit
  <1>2. QED BY <1>1 DEF ReachExit

(* Every r-avoiding edge survives every exit, so the r-deleted closure is  *)
(* a lower bound for the post-exit closure -- for ANY exit set.            *)
LEMMA ReachExc_sub_ReachExit ==
  ASSUME NEW l, NEW r, NEW XS
  PROVE  ReachExc(l, r) \subseteq ReachExit(l, r, XS)
  <1>1. \A X \in SUBSET E : ClosedExit(l, r, XS, X) => ClosedExc(l, r, X)
    <2> SUFFICES ASSUME NEW X \in SUBSET E, ClosedExit(l, r, XS, X),
                        NEW x \in E, NEW y \in E,
                        x \in X, EdgeAt(l, x, y), x # r, y # r
                 PROVE  y \in X
        BY DEF ClosedExc
    <2>1. EdgeExit(l, r, XS, x, y) BY DEF EdgeAt, EdgeExit
    <2>2. QED BY <2>1 DEF ClosedExit
  <1>2. QED BY <1>1 DEF ReachExc, ReachExit

----------------------------------------------------------------------------
(***************************************************************************)
(* S1a -- NECESSITY (Thm 3 made algorithmic).  Any exit set that achieves  *)
(* separation must cover the r-deleted pin set, and the target cannot      *)
(* already sit on the frontier.                                            *)
(***************************************************************************)
THEOREM ExitNecessity ==
  ASSUME NEW l \in Labelings, NEW r \in E, NEW XS \in SUBSET Surfaces,
         SepAch(l, r, XS)
  PROVE  r \notin G /\ HandlesMinus(l, r) \subseteq XS
  <1>1. r \notin G
    <2>1. ASSUME r \in G PROVE FALSE
      <3>1. r \in ReachExit(l, r, XS) BY <2>1, G_sub_ReachExit
      <3>2. QED BY <3>1 DEF SepAch
    <2>2. QED BY <2>1
  <1>2. HandlesMinus(l, r) \subseteq XS
    <2> SUFFICES ASSUME NEW S \in Surfaces, S \in HandlesMinus(l, r),
                        S \notin XS
                 PROVE  FALSE
        BY DEF HandlesMinus
    <2>1. PICK x \in ReachExc(l, r) : <<x, r>> \in Rel(S, l)
        BY DEF HandlesMinus
    <2>2. x \in E BY ReachExc_inE
    <2>3. x \in ReachExit(l, r, XS) BY ReachExc_sub_ReachExit
    <2>4. EdgeExit(l, r, XS, x, r) BY <2>1 DEF EdgeExit
    <2>5. r \in ReachExit(l, r, XS)
        BY <2>2, <2>3, <2>4, ReachExit_Closed DEF ClosedExit
    <2>6. QED BY <2>5 DEF SepAch
  <1>3. QED BY <1>1, <1>2

(***************************************************************************)
(* S1b -- SUFFICIENCY.  Covering the r-deleted pin set is enough: the      *)
(* r-deleted closure itself witnesses the separation.                      *)
(***************************************************************************)
THEOREM ExitSufficiency ==
  ASSUME NEW l \in Labelings, NEW r \in E, NEW XS \in SUBSET Surfaces,
         r \notin G, HandlesMinus(l, r) \subseteq XS
  PROVE  SepAch(l, r, XS)
  <1> DEFINE Y == ReachExc(l, r)
  <1>1. Y \in SUBSET E BY ReachExc_inE
  <1>2. G \subseteq Y BY G_sub_ReachExc
  <1>3. r \notin Y BY ReachExc_NoTarget
  <1>4. ClosedExit(l, r, XS, Y)
    <2> SUFFICES ASSUME NEW a \in E, NEW b \in E,
                        a \in Y, EdgeExit(l, r, XS, a, b)
                 PROVE  b \in Y
        BY DEF ClosedExit
    <2>1. PICK S \in Surfaces :
            <<a, b>> \in Rel(S, l) /\ (S \in XS => (a # r /\ b # r))
        BY DEF EdgeExit
    <2>2. a # r BY <1>3
    <2>3. b # r
      <3>1. ASSUME b = r PROVE FALSE
        <4>1. S \notin XS BY <2>1, <3>1
        <4>2. <<a, r>> \in Rel(S, l) BY <2>1, <3>1
        <4>3. S \in HandlesMinus(l, r) BY <4>2 DEF HandlesMinus
        <4>4. QED BY <4>1, <4>3
      <3>2. QED BY <3>1
    <2>4. EdgeAt(l, a, b) BY <2>1 DEF EdgeAt
    <2>5. QED BY <2>2, <2>3, <2>4, ReachExc_Closed DEF ClosedExc
  <1>5. ASSUME r \in ReachExit(l, r, XS) PROVE FALSE
    <2>1. r \in Y BY <1>5, <1>1, <1>2, <1>4 DEF ReachExit
    <2>2. QED BY <2>1, <1>3
  <1>6. QED BY <1>5 DEF SepAch

(***************************************************************************)
(* S1 -- LEAST EXIT.  An exit set achieves separation iff the target is    *)
(* off the frontier and the set covers HandlesMinus(l, r).  Hence the      *)
(* least exit set exists, is unique, and IS HandlesMinus(l, r): at         *)
(* per-effect granularity, synthesis is not an optimization problem --     *)
(* the optimum is a definable set.                                         *)
(***************************************************************************)
THEOREM LeastExit ==
  ASSUME NEW l \in Labelings, NEW r \in E, NEW XS \in SUBSET Surfaces
  PROVE  SepAch(l, r, XS) <=> (r \notin G /\ HandlesMinus(l, r) \subseteq XS)
  BY ExitNecessity, ExitSufficiency

(***************************************************************************)
(* S1c -- ESTABLISHMENT IS FINAL.  The `r \notin G' conjunct of LeastExit    *)
(* is not a side condition: it says that membership of the established      *)
(* frontier CANNOT BE BOUGHT BACK.  For an effect already in G no exit set  *)
(* achieves separation -- not the least one, not the largest one, not       *)
(* Surfaces itself -- and no relabelling helps either, since l is           *)
(* universally quantified here.  Price is defined only before establishment;*)
(* after it, the separation problem has no solution at any price.           *)
(*                                                                         *)
(* This is the static form of an ordering statement the framework cannot    *)
(* otherwise make: it carries no notion of time, yet this theorem is what   *)
(* an architecture means when it puts a decision point BEFORE the record.   *)
(***************************************************************************)
THEOREM EstablishmentIsFinal ==
  ASSUME NEW l \in Labelings, NEW r \in G, NEW XS \in SUBSET Surfaces
  PROVE  ~SepAch(l, r, XS)
  <1> SUFFICES ASSUME SepAch(l, r, XS) PROVE FALSE
      OBVIOUS
  <1>1. r \in E BY G_inE
  <1>2. r \notin G BY <1>1, ExitNecessity
  <1>3. QED BY <1>2

----------------------------------------------------------------------------
(* Under the key-type split, an AllBot-edge is an LI edge of the actual    *)
(* labelling -- the algorithmic content of Lemma 1.                        *)
LEMMA AllBotEdgeLI ==
  ASSUME Dichotomy, NEW x \in E, NEW y \in E, NEW S \in Surfaces,
         <<x, y>> \in Rel(S, AllBot)
  PROVE  LabelIndep(S) /\ <<x, y>> \in Rel(S, lbl)
  <1>1. LabelIndep(S) BY DEF Dichotomy
  <1>2. Rel(S, AllBot) = Rel(S, lbl)
      BY <1>1, AllBotLabeling, LblType DEF LabelIndep
  <1>3. QED BY <1>1, <1>2

(* ... and therefore an edge under EVERY labelling.                        *)
LEMMA AllBotEdgeEverywhere ==
  ASSUME Dichotomy, NEW l \in Labelings,
         NEW x \in E, NEW y \in E, NEW S \in Surfaces,
         <<x, y>> \in Rel(S, AllBot)
  PROVE  <<x, y>> \in Rel(S, l)
  <1>1. LabelIndep(S) BY DEF Dichotomy
  <1>2. Rel(S, AllBot) = Rel(S, l) BY <1>1, AllBotLabeling DEF LabelIndep
  <1>3. QED BY <1>2

LEMMA ReachExcAllBot_Least ==
  ASSUME Dichotomy, NEW l \in Labelings, NEW r
  PROVE  ReachExc(AllBot, r) \subseteq ReachExc(l, r)
  <1>1. \A X \in SUBSET E : ClosedExc(l, r, X) => ClosedExc(AllBot, r, X)
    <2> SUFFICES ASSUME NEW X \in SUBSET E, ClosedExc(l, r, X),
                        NEW x \in E, NEW y \in E,
                        x \in X, EdgeAt(AllBot, x, y), x # r, y # r
                 PROVE  y \in X
        BY DEF ClosedExc
    <2>1. PICK S \in Surfaces : <<x, y>> \in Rel(S, AllBot) BY DEF EdgeAt
    <2>2. <<x, y>> \in Rel(S, l) BY <2>1, AllBotEdgeEverywhere
    <2>3. EdgeAt(l, x, y) BY <2>2 DEF EdgeAt
    <2>4. QED BY <2>3 DEF ClosedExc
  <1>2. QED BY <1>1 DEF ReachExc

(***************************************************************************)
(* S3 -- KEY-DROP DOMINANCE.  Under the key-type split, the maximal        *)
(* key-drop minimizes the required exit set pointwise: whatever a          *)
(* relabelling l demands, AllBot demands no more.  The relabel phase has   *)
(* a closed-form optimum.                                                  *)
(***************************************************************************)
THEOREM KeyDropDominance ==
  ASSUME Dichotomy, NEW l \in Labelings, NEW r \in E
  PROVE  HandlesMinus(AllBot, r) \subseteq HandlesMinus(l, r)
  <1> SUFFICES ASSUME NEW S \in Surfaces, S \in HandlesMinus(AllBot, r)
               PROVE  S \in HandlesMinus(l, r)
      BY DEF HandlesMinus
  <1>1. PICK x \in ReachExc(AllBot, r) : <<x, r>> \in Rel(S, AllBot)
      BY DEF HandlesMinus
  <1>2. x \in E BY ReachExc_inE
  <1>3. <<x, r>> \in Rel(S, l) BY <1>1, <1>2, AllBotEdgeEverywhere
  <1>4. x \in ReachExc(l, r) BY <1>1, ReachExcAllBot_Least
  <1>5. QED BY <1>3, <1>4 DEF HandlesMinus

(***************************************************************************)
(* S1+S3 -- OPTIMAL SYNTHESIS.  Quantifying over ALL labellings: an exit   *)
(* set works for SOME labelling iff it works for the maximal key-drop.     *)
(* The optimal strategy is exactly "drop every key, then exit precisely    *)
(* HandlesMinus(AllBot, r)" -- the law's two-conjunct exit, synthesized.   *)
(***************************************************************************)
THEOREM OptimalSynthesis ==
  ASSUME Dichotomy, NEW r \in E, NEW XS \in SUBSET Surfaces
  PROVE  (\E l \in Labelings : SepAch(l, r, XS))
           <=> (r \notin G /\ HandlesMinus(AllBot, r) \subseteq XS)
  <1>1. ASSUME NEW l \in Labelings, SepAch(l, r, XS)
        PROVE  r \notin G /\ HandlesMinus(AllBot, r) \subseteq XS
    <2>1. r \notin G /\ HandlesMinus(l, r) \subseteq XS
        BY <1>1, ExitNecessity
    <2>2. HandlesMinus(AllBot, r) \subseteq HandlesMinus(l, r)
        BY KeyDropDominance
    <2>3. QED BY <2>1, <2>2
  <1>2. ASSUME r \notin G, HandlesMinus(AllBot, r) \subseteq XS
        PROVE  \E l \in Labelings : SepAch(l, r, XS)
    <2>1. SepAch(AllBot, r, XS)
        BY <1>2, AllBotLabeling, ExitSufficiency
    <2>2. QED BY <2>1, AllBotLabeling
  <1>3. QED BY <1>1, <1>2

----------------------------------------------------------------------------
LEMMA ReachExcAllBot_sub_Reach ==
  ASSUME Dichotomy, NEW r
  PROVE  ReachExc(AllBot, r) \subseteq Reach
  <1>1. \A X \in SUBSET E : ClosedUnder(X) => ClosedExc(AllBot, r, X)
    <2> SUFFICES ASSUME NEW X \in SUBSET E, ClosedUnder(X),
                        NEW x \in E, NEW y \in E,
                        x \in X, EdgeAt(AllBot, x, y), x # r, y # r
                 PROVE  y \in X
        BY DEF ClosedExc
    <2>1. PICK S \in Surfaces : <<x, y>> \in Rel(S, AllBot) BY DEF EdgeAt
    <2>2. <<x, y>> \in Rel(S, lbl) BY <2>1, AllBotEdgeLI
    <2>3. Edge(x, y) BY <2>2 DEF Edge
    <2>4. QED BY <2>3 DEF ClosedUnder
  <1>2. QED BY <1>1 DEF ReachExc, Reach

(***************************************************************************)
(* S2 -- THE PRICE IS INTEGRITY.  The least exit set is contained in       *)
(* Handles(r): every surface the separation must escape is one of the      *)
(* label-independent links measured by seal multiplicity I(r).  The        *)
(* antagonism of Theorem 1 (NoSealedSeparable), read as a price:           *)
(* separation is purchased surface-for-surface out of the integrity        *)
(* carrier.                                                                *)
(***************************************************************************)
THEOREM PriceWithinIntegrity ==
  ASSUME Dichotomy, NEW r \in E
  PROVE  HandlesMinus(AllBot, r) \subseteq Handles(r)
  <1> SUFFICES ASSUME NEW S \in Surfaces, S \in HandlesMinus(AllBot, r)
               PROVE  S \in Handles(r)
      BY DEF HandlesMinus
  <1>1. PICK x \in ReachExc(AllBot, r) : <<x, r>> \in Rel(S, AllBot)
      BY DEF HandlesMinus
  <1>2. x \in E BY ReachExc_inE
  <1>3. LabelIndep(S) /\ <<x, r>> \in Rel(S, lbl)
      BY <1>1, <1>2, AllBotEdgeLI
  <1>4. x \in Reach BY <1>1, ReachExcAllBot_sub_Reach
  <1>5. Pins(S, r) BY <1>3, <1>4 DEF Pins
  <1>6. QED BY <1>3, <1>5 DEF Handles

----------------------------------------------------------------------------
LEMMA ReachExcAllBot_sub_ReachLI ==
  ASSUME Dichotomy, NEW r
  PROVE  ReachExc(AllBot, r) \subseteq ReachLI(lbl)
  <1>1. \A X \in SUBSET E : ClosedLI(lbl, X) => ClosedExc(AllBot, r, X)
    <2> SUFFICES ASSUME NEW X \in SUBSET E, ClosedLI(lbl, X),
                        NEW x \in E, NEW y \in E,
                        x \in X, EdgeAt(AllBot, x, y), x # r, y # r
                 PROVE  y \in X
        BY DEF ClosedExc
    <2>1. PICK S \in Surfaces : <<x, y>> \in Rel(S, AllBot) BY DEF EdgeAt
    <2>2. LabelIndep(S) /\ <<x, y>> \in Rel(S, lbl) BY <2>1, AllBotEdgeLI
    <2>3. EdgeLI(lbl, x, y) BY <2>2 DEF EdgeLI
    <2>4. QED BY <2>3 DEF ClosedLI
  <1>2. QED BY <1>1 DEF ReachExc, ReachLI

(***************************************************************************)
(* S2' -- FRESH EXACTNESS.  For a fresh effect (a sink: it emits no link   *)
(* of its own, typical of the newest persisted record) the bound is an     *)
(* identity: the least exit set is EXACTLY the SealedLI handle set of      *)
(* Corollary 2 (OrbitAntagonism).  The synthesis layer and the orbit       *)
(* layer meet.                                                             *)
(***************************************************************************)
THEOREM FreshExactness ==
  ASSUME Dichotomy, NEW r \in E, Sink(r)
  PROVE  HandlesMinus(AllBot, r)
           = { S \in Surfaces : LabelIndep(S) /\ PinsLI(S, r) }
  <1>1. ASSUME NEW S \in Surfaces, S \in HandlesMinus(AllBot, r)
        PROVE  LabelIndep(S) /\ PinsLI(S, r)
    <2>1. PICK x \in ReachExc(AllBot, r) : <<x, r>> \in Rel(S, AllBot)
        BY <1>1 DEF HandlesMinus
    <2>2. x \in E BY ReachExc_inE
    <2>3. LabelIndep(S) /\ <<x, r>> \in Rel(S, lbl)
        BY <2>1, <2>2, AllBotEdgeLI
    <2>4. x \in ReachLI(lbl) BY <2>1, ReachExcAllBot_sub_ReachLI
    <2>5. PinsLI(S, r) BY <2>3, <2>4 DEF PinsLI
    <2>6. QED BY <2>3, <2>5
  <1>2. ASSUME NEW S \in Surfaces, LabelIndep(S), PinsLI(S, r)
        PROVE  S \in HandlesMinus(AllBot, r)
    <2>1. PICK g \in ReachLI(lbl) : <<g, r>> \in Rel(S, lbl)
        BY <1>2 DEF PinsLI
    <2>2. g \in E BY ReachLI_inE
    <2>3. g # r BY <2>1, <2>2 DEF Sink
    <2> DEFINE Y == ReachExc(AllBot, r) \cup {r}
    <2>4. Y \in SUBSET E BY ReachExc_inE
    <2>5. G \subseteq Y BY G_sub_ReachExc DEF Y
    <2>6. ClosedLI(lbl, Y)
      <3> SUFFICES ASSUME NEW a \in E, NEW b \in E,
                          a \in Y, EdgeLI(lbl, a, b)
                   PROVE  b \in Y
          BY DEF ClosedLI
      <3>1. PICK T \in Surfaces : LabelIndep(T) /\ <<a, b>> \in Rel(T, lbl)
          BY DEF EdgeLI
      <3>2. a # r BY <3>1 DEF Sink
      <3>3. a \in ReachExc(AllBot, r) BY <3>2 DEF Y
      <3>4. CASE b = r BY <3>4 DEF Y
      <3>5. CASE b # r
        <4>1. <<a, b>> \in Rel(T, AllBot)
            BY <3>1, AllBotLabeling, LblType DEF LabelIndep
        <4>2. EdgeAt(AllBot, a, b) BY <4>1 DEF EdgeAt
        <4>3. b \in ReachExc(AllBot, r)
            BY <3>3, <3>2, <3>5, <4>2, ReachExc_Closed DEF ClosedExc
        <4>4. QED BY <4>3 DEF Y
      <3>6. QED BY <3>4, <3>5
    <2>7. ReachLI(lbl) \subseteq Y
      <3> SUFFICES ASSUME NEW e \in ReachLI(lbl) PROVE e \in Y
          OBVIOUS
      <3>1. QED BY <2>4, <2>5, <2>6 DEF ReachLI
    <2>8. g \in ReachExc(AllBot, r) BY <2>1, <2>3, <2>7 DEF Y
    <2>9. <<g, r>> \in Rel(S, AllBot)
        BY <2>1, <1>2, AllBotLabeling, LblType DEF LabelIndep
    <2>10. QED BY <2>8, <2>9 DEF HandlesMinus
  <1>3. \A S : S \in HandlesMinus(AllBot, r)
                 <=> S \in { T \in Surfaces : LabelIndep(T) /\ PinsLI(T, r) }
    <2>1. ASSUME NEW S, S \in HandlesMinus(AllBot, r)
          PROVE  S \in { T \in Surfaces : LabelIndep(T) /\ PinsLI(T, r) }
      <3>1. S \in Surfaces BY <2>1 DEF HandlesMinus
      <3>2. QED BY <2>1, <3>1, <1>1
    <2>2. ASSUME NEW S, S \in { T \in Surfaces : LabelIndep(T) /\ PinsLI(T, r) }
          PROVE  S \in HandlesMinus(AllBot, r)
      <3>1. S \in Surfaces /\ LabelIndep(S) /\ PinsLI(S, r) BY <2>2
      <3>2. QED BY <3>1, <1>2
    <2>3. QED BY <2>1, <2>2
  <1>4. QED BY <1>3, SetExtensionality

(***************************************************************************)
(* The zero-price corollary: a fresh effect separates for free exactly     *)
(* when it is not LI-sealed -- the synthesis-layer restatement of the      *)
(* conservation law's puncture (Cor 1, CapacityRequiresPuncture) at the    *)
(* orbit level (Cor 2, OrbitAntagonism).                                   *)
(***************************************************************************)
THEOREM ZeroPriceIffUnsealed ==
  ASSUME Dichotomy, NEW r \in E, Sink(r)
  PROVE  HandlesMinus(AllBot, r) = {} <=> ~SealedLI(r)
  <1>1. HandlesMinus(AllBot, r)
          = { S \in Surfaces : LabelIndep(S) /\ PinsLI(S, r) }
      BY FreshExactness
  <1>2. SealedLI(r) <=> \E S \in Surfaces : LabelIndep(S) /\ PinsLI(S, r)
      BY DEF SealedLI
  <1>3. ({ S \in Surfaces : LabelIndep(S) /\ PinsLI(S, r) } = {})
          <=> ~(\E S \in Surfaces : LabelIndep(S) /\ PinsLI(S, r))
      OBVIOUS
  <1>4. QED BY <1>1, <1>2, <1>3

============================================================================
