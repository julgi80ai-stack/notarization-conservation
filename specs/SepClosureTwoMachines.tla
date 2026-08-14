------------------- MODULE SepClosureTwoMachines -------------------
(***************************************************************************)
(* Non-retroactive separation (Sep) as a closure property, machine-checked *)
(* at the two design vertices of the prior bounded trade-off result.       *)
(*                                                                         *)
(* Question: is a reflex actuation effect e* UN-reachable from the         *)
(* action log G under the closure of the re-linking operations             *)
(*   {ByTime (J2), ByPosition (J1), ByParent (J4)} ?                        *)
(* ByParent has no traverser in the audited code (LATENT), but             *)
(* non-retroactivity requires the separation to survive a FUTURE traverser, *)
(* so it is included as a worst case.                                       *)
(*                                                                         *)
(* Three machines -- the module name predates the third (NE_KEEP) --       *)
(* switched by CONSTANT Machine, each checked with TLC:                    *)
(*   ACCT     accountability vertex (the audited system): the reflex also   *)
(*            enters the sealing pipeline (store + chain).  Even with the    *)
(*            correlation key stripped, ByPosition (the position-linked      *)
(*            hash chain) re-links it to G  =>  Sep VIOLATED.               *)
(*   NE_KEEP  bypasses sealing but KEEPS the correlation key (mirrors the    *)
(*            conflict reflex preserving the original action's corr):        *)
(*            the latent ByParent re-links it  =>  Sep VIOLATED.            *)
(*            This is why ByParent must be in the closure (non-retroactivity).*)
(*   NE       non-establishment vertex: bypasses sealing AND drops the key.  *)
(*            No operation reaches it  =>  Sep HOLDS.  Realisable only by     *)
(*            exiting the whole pipeline and dropping the key.               *)
(*                                                                         *)
(* The surfaces are the audited system's own: a hash chain (J1), a         *)
(* time-series store (J2), and a parent-key index (J4).  Only their        *)
(* re-linking behaviour is modelled; no implementation detail is needed    *)
(* and none is given.                                                      *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS CorrIDs, NONE, Actions, Reflexes, Machine,
          EnableByTime, EnableByPosition  \* surface-isolation knobs (J2/J1)

ASSUME NoneNotCorr  == NONE \notin CorrIDs
ASSUME DisjointKinds == Actions \cap Reflexes = {}
ASSUME MachineDom    == Machine \in {"ACCT", "NE_KEEP", "NE"}

EventIds == Actions \cup Reflexes
ACorr    == CHOOSE c \in CorrIDs : TRUE     \* the (single) action correlation key

Kind(e) == IF e \in Actions THEN "ACTION" ELSE "REFLEX"

\* corr assigned at emission, per machine policy for the reflex.
CorrAssign(e) ==
  IF e \in Actions THEN ACorr
  ELSE IF Machine = "ACCT"    THEN NONE     \* strip corr (yet still sealed)
  ELSE IF Machine = "NE_KEEP" THEN ACorr    \* bypass sealing but KEEP the key
  ELSE                             NONE     \* NE: bypass sealing AND drop key

VARIABLES emitted,    \* set of EventIds that have been emitted to the bus
          linked      \* set reachable-from-G under the join closure (G-frontier)
vars == << emitted, linked >>

\* Surface routing (derived).  Actions are always on the sealing pipeline.
\* The reflex is on the pipeline ONLY for ACCT (the audited behaviour:
\* unconditional store + the chain seals the low-level command).  NE*/
\* route the reflex to a disjoint non-action surface (bypasses store + chain).
OnSealingPipeline(e) ==
  /\ e \in emitted
  /\ (Kind(e) = "ACTION" \/ (Kind(e) = "REFLEX" /\ Machine = "ACCT"))
InDb(e)    == OnSealingPipeline(e)          \* J2 surface (corr-agnostic)
InChain(e) == OnSealingPipeline(e)          \* J1 surface (corr-agnostic, position)

----------------------------------------------------------------------------
\* Emission.
EmitAction(e) ==
  /\ e \in Actions /\ e \notin emitted
  /\ emitted' = emitted \cup {e}
  /\ linked'  = linked  \cup {e}            \* an established action IS in G
EmitReflex(e) ==
  /\ e \in Reflexes /\ e \notin emitted
  /\ emitted' = emitted \cup {e}
  /\ linked'  = linked

\* Join operations = the threat-operation closure {J1, J2, J4}.
\* J2 ByTime: co-presence in the corr-agnostic store (time-range / event-id).
JoinByTime(x, y) ==
  /\ EnableByTime
  /\ x \in linked /\ {x, y} \subseteq emitted
  /\ InDb(x) /\ InDb(y)
  /\ linked' = linked \cup {y} /\ UNCHANGED emitted
\* J1 ByPosition: the single hash chain links by sealing position (label-agnostic).
JoinByPosition(x, y) ==
  /\ EnableByPosition
  /\ x \in linked /\ {x, y} \subseteq emitted
  /\ InChain(x) /\ InChain(y)
  /\ linked' = linked \cup {y} /\ UNCHANGED emitted
\* J4 ByParent (LATENT worst-case): pure key traversal, surface-INDEPENDENT.
\* models a future parent-key traverser; needs only a shared non-NONE key.
JoinByParent(x, y) ==
  /\ x \in linked /\ {x, y} \subseteq emitted
  /\ CorrAssign(x) = CorrAssign(y) /\ CorrAssign(x) # NONE
  /\ linked' = linked \cup {y} /\ UNCHANGED emitted

Next ==
  \/ \E e \in EventIds : EmitAction(e) \/ EmitReflex(e)
  \/ \E x \in EventIds, y \in EventIds :
        JoinByTime(x, y) \/ JoinByPosition(x, y) \/ JoinByParent(x, y)

Init == emitted = {} /\ linked = {}
Spec == Init /\ [][Next]_vars

\* ===== the invariant to machine-check =====
\* Sep (non-retroactive separation): no emitted reflex effect is ever
\* reachable from G under the closure {J1, J2, J4}.
Sep == \A r \in Reflexes : (r \in emitted) => (r \notin linked)

====================================================================
(*                      TLC RESULTS (see README)                     *)
(*  cfg: CorrIDs={c1} NONE=NoCorr Actions={a1} Reflexes={r1} INV Sep   *)
(*                                                                   *)
(*  ACCT, J1+J2 on                      -> VIOLATED via JoinByTime     *)
(*                          (label-strip insufficient; store re-links) *)
(*  ACCT, J2 off                        -> VIOLATED via JoinByPosition *)
(*                          (the hash chain ALONE re-links; label moot)*)
(*  ACCT, J1+J2 off                     -> NO ERROR                    *)
(*                          (cause = the surfaces, not the label)      *)
(*  NE_KEEP                             -> VIOLATED via JoinByParent    *)
(*                          (J4 must be in the closure; retro gap)     *)
(*  NE                                  -> NO ERROR                    *)
(*                          (Sep = pipeline-exit AND key-drop)         *)
(***************************************************************************)
====================================================================
