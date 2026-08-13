# Reproduction artifact — *The Price of Non-Establishment*

Machine-checked companion to the paper **"The Price of Non-Establishment: Least Exit Sets in Label-Independent Notarization, with Machine-Checked Instances."**

This bundle is **self-contained** and reproduces **every** machine-checked claim in the paper with one command. Universals are *proven* (TLAPS, unbounded); existence/necessity are *checked* (TLC); the synthesis complexity propositions and the cryptographic dual are *paper-proved arguments*, not machine-checked, and are not part of this bundle.

---

## 1. Requirements

- **TLAPS** (`tlapm`) 1.5.0 on `PATH` — backends Isabelle / Zenon / SMT.
  `export PATH="$HOME/tlaps/bin:$PATH"`
- **TLC**: `tla2tools.jar` (v2.19) + Java 21. Default location `/tmp/tla2tools.jar`; override with `TLC_JAR=/path/to/tla2tools.jar`. (Not bundled — fetch from the TLA⁺ tools releases.)
- **Python 3** — for `./check.sh` only (§2b). Standard library, nothing to install. `./prove.sh` does not use it.

The specifications use only `Naturals`, `FiniteSets`, and the `TLAPS` standard module; they depend on no external library and on no source code of any audited system.

## 2. Reproduce

```sh
export PATH="$HOME/tlaps/bin:$PATH"
./prove.sh
```

Expected output: **8× "All N obligations proved"** (TLAPS, 0 omitted/admitted) and **7× "No error has been found"** (TLC). A verbatim run is in `logs/anc_reproduce.log`; the per-module logs in `logs/` are `--cleanfp` (cold-cache) runs.

## 2b. Run the synthesis checker (independent second entry point)

```sh
./check.sh              # run the procedure; the specifications confirm it
./check.sh --negative   # non-vacuity self-test: a wrong value must be REFUSED
```

Proposition 1 says the least exit set is computable in
`O(|E| + Σ_S |Rel(S)|)`. `checker/` implements that procedure and then asserts
its answers back into the specifications as TLC invariants — over modules it
`EXTENDS` rather than copies. A pass is therefore *"an independent
implementation computed this, and the artifact that owns the definitions
confirmed it"*, not *"our tool says so"*.

It also reproduces the paper's four-domain dividend table as tool output
from concrete members of the four instance modules, and measures Proposition 1's
bound — the paper's one non-machine-checked result — as an operation count.

**The two entry points are independent.** `check.sh` cannot change what
`prove.sh` reports: the 1,181 obligations and 7 witnesses stand on their own,
and a reader uninterested in the tool can ignore it. Details, including how to
verify for yourself that a `PASS` is not vacuous, are in **`checker/README.md`**.

A verbatim run is in `logs/checker.log`.

> **Reading the logs for cache reuse.** `tlapm` marks an obligation resolved from its fingerprint cache with `already:true`. A genuine cold run of this bundle produces **exactly one**, in `Synthesis.log`: that module states one obligation twice, so the second lookup hits the fingerprint the first just wrote. Every other log has **zero**. More than that means the cache was warm and the run does not demonstrate what it claims.

> **Fresh re-verification.** `tlapm` caches results in `specs/.tlacache/`. That directory is intentionally **not** shipped, so a clean clone re-proves every obligation from scratch. To force a fresh run on an existing checkout, delete `specs/.tlacache/` (or pass `--cleanfp` to `tlapm`) before `./prove.sh`.

## 3. What is proved, and where (claim = proof, 1:1)

| Paper result | Statement | Module (`specs/`) | Tool | Obligations |
|---|---|---|---|---|
| Lemma 1 | relabelling futility (`DecisiveLI`) | `Notarization.tla` | TLAPS | 83 (module) |
| **Theorem 1** | `∀e ¬(Sealed(e) ∧ Separable(e))` (antagonism) | `Antagonism.tla` | TLAPS | 84 (module) |
| **Corollary 1** | `(∃ separable) ⟹ (∃ unsealed)` (puncture) | `Antagonism.tla` | TLAPS | ″ |
| **Corollary 2** | antagonism over the label orbit (`OrbitInvariance`, `OrbitAntagonism`) | `Antagonism.tla` | TLAPS | ″ |
| **Theorem 2** | `TA ⟹ ∀e ¬Separable(e)` (binary impossibility = degenerate corner) | `Antagonism.tla` | TLAPS | ″ |
| **Theorem 3** | separation exits every surface (non-retroactive decomposition) | `Antagonism.tla` | TLAPS | ″ |
| **Remark 1** | redundancy ⟹ resilience (strength axis) | `Resilience.tla` | TLAPS | 11 |
| **Theorem 4** | least exit set is unique & definable (`LeastExit`) | `Synthesis.tla` | TLAPS | 324 (module) |
| **Theorem 5** | key-drop dominance; closed-form optimal synthesis | `Synthesis.tla` | TLAPS | ″ |
| **Theorem 6** | separation price ⊆ seal multiplicity (`PriceWithinIntegrity`) | `Synthesis.tla` | TLAPS | ″ |
| **Corollary 3** | **establishment is final** — for `r ∈ G` no exit set separates, under any labelling (`EstablishmentIsFinal`) | `Synthesis.tla` | TLAPS | ″ |
| **Corollary 4** | fresh effects: price = `SealedLI` handles; zero iff unsealed (`FreshExactness`, `ZeroPriceIffUnsealed`) | `Synthesis.tla` | TLAPS | ″ |
| Non-vacuity | `Sealed`, `Separable` both realised | `AntagonismWitness.tla`+`.cfg` | TLC | — |
| Necessity | label-independence is load-bearing for the orbit layer | `NecessityWitness.tla`+`.cfg` | TLC | — |
| **Depth & separation** | a length-2 closure; `Sealed ∧ ¬SealedLI`; `Reach ⊋ ReachLI`; price `< I(e)` | `AuditLogWitness.tla`+`.cfg` | TLC | — |
| **Multi-input join** | a length-2 closure through a spend join: one effect with **two** distinct `Graph` in-edges — impossible for a predecessor pointer, and a source coordinate that is read — impossible for a cylinder | `AnonymityWitness.tla`+`.cfg` | TLC | — |
| Instance — deniability | non-repudiation vs. deniability (`RepudiationFutileOnSig`) | `DeniabilityInstance.tla` | TLAPS | 151 |
| Instance — anonymity | anonymity vs. accountability (`ClusteringFutile`) | `AnonymityInstance.tla` | TLAPS | 149 |
| Instance — erasure | immutability vs. right-to-be-forgotten (`ErasureFutile`) | `AuditLogInstance.tla` | TLAPS | 174 |
| Instance — governance | action non-establishment (`AcctKeyStripFutile`) | `SepClosureInstance.tla` (+ `SepClosureTwoMachines.tla`) | TLAPS | 205 |
| Key-type split, per instance | `Dichotomy` discharged in each substitution | `*_Dichotomy` in all four instances | TLAPS | (in the above) |
| Least exit, per instance | `HandlesMinus(AllBot, r)` computed in each domain | `*_LeastExit` in all four instances | TLAPS | (in the above) |
| Zero price, per instance | price `= {}` off the sealing surfaces | `*_ZeroPrice` in all four instances | TLAPS | (in the above) |
| **`TA` false in the log** | a genesis entry has no `prev`, is never sealed, hence `¬TA` | `AuditLogInstance` (`Audit_GenesisUnsealed`) | TLAPS | (in the above) |
| Distinct pins | `Rel(J1) ≠ Rel(J2)` — the governance `I = 2` is two surfaces, not one twice | `SepClosureInstance` (`J1_J2_Distinct`) | TLAPS | (in the above) |
| **Non-degenerate strength** | `I(e) = 2` with two *distinct* surfaces, each survivable; strict Thm 6 inclusion | `PriceWitness.tla`+`.cfg` | TLC | — |
| **Thm 2 non-vacuous, and its price** | `TA` realised together with its conclusion — via a self-pinning root | `TAWitness.tla`+`.cfg` | TLC | — |
| **Thm 6 strict above multiplicity 1** | `I(r) = 2`, price `1`, `r` not a sink — separates Thm 6 from Cor 4 | `StrictPriceWitness.tla`+`.cfg` | TLC | — |

> **On the numbering.** These are the conference version's numbers. Every row also names the TLA⁺ theorem, which does not move when a version renumbers — prefer the name if you are holding a different version of the paper.

**Total reproduced by `prove.sh`: 1,181 TLAPS obligations (0 omitted/admitted) + 7 TLC witnesses.**

### Reproduced by `check.sh` (the checker — a different kind of evidence)

These are **not** additional obligations; the totals above are unchanged. They are the paper's *analysis* run as a program and confirmed against the specifications.

| Paper result | What `check.sh` establishes | Where | Tool |
|---|---|---|---|
| **Proposition 1** (procedure) | the least-exit-set procedure implemented independently; its output on every witness model asserted as an invariant over the **real** witness module and confirmed | `checker/certify.py` → `gen/*Cert.tla` | TLC, 4 certificates |
| **the four-domain dividend table** | each row reproduced as **tool output** from a concrete member of its instance module — `EXTENDS DeniabilityInstance` / `AnonymityInstance` / `AuditLogInstance` / `SepClosureInstance`, constants fixed in the `.cfg`, **no definition copied** | `checker/concrete.py` → `gen3/*Concrete.tla` | TLC, 4 certificates |
| hypotheses of `*_LeastExit`, `*_ZeroPrice` | asserted alongside the conclusion in each of the four, so those theorems are witnessed **non-vacuous** on a concrete model | ″ | TLC |
| class membership | the instance modules' `ASSUME`s are enforced by TLC on each concrete model | ″ | TLC |
| **Proposition 1** (the bound) | `O(|E| + Σ_S |Rel(S)|)` measured as an operation count: `ops/(|E|+Σ|Rel|)` **bounded by 2** up to `|E| = 10⁵` and `Σ|Rel| ≈ 2 × 10⁵` | `checker/scaling.py` | measurement |
| **non-vacuity of the above** | one deliberately wrong value per model, **refused** by TLC | `./check.sh --negative` | TLC |

Proposition 1's *proof* remains a paper argument (stated in the paper, proved in its appendix); what is added here is a measurement of the count it asserts, and a confirmation that the procedure it describes computes what the machine-checked theorems say it should.

Per-module counts: `Notarization` 83, `Antagonism` 84, `Resilience` 11, `Synthesis` 324, `DeniabilityInstance` 151, `AnonymityInstance` 149, `AuditLogInstance` 174, `SepClosureInstance` 205.

> **On the instance counts.** Each instance now *instantiates the law* (`INSTANCE Synthesis`, which extends `Antagonism` and `Notarization`) rather than only its definitions. Instantiating obliges each substitution to **discharge the abstract module's `ASSUME`s** — five per instance — and to justify every inherited theorem it uses. Those obligations did not exist while the instances merely re-proved local facts, which is why the counts rise rather than fall. The number is a measure of what is *connected*, not of depth.

### New to this paper vs. reused (honest breakdown)
- **New (the impossibility, the analysis, and the two new instances): 719 obligations** — `Antagonism` (84, incl. the orbit corollary) + `Resilience` (11) + `Synthesis` (324) + `DeniabilityInstance` (151) + `AnonymityInstance` (149).
- **Modules originating in prior work: 462 obligations** — `Notarization` (83, the framework this paper builds on) + `AuditLogInstance` (174) + `SepClosureInstance` (205). They are included so the paper's class table is reproducible end-to-end in one bundle, not to claim them as new. **But the label is by module, not by obligation, and the difference matters here:** of the erasure instance's 174, **52 are new to this paper** — `Audit_ZeroPrice` (29) and `Audit_GenesisUnsealed` (23) were written for it and have no counterpart in the prior development. Counted by obligation rather than by module the split is **771 new / 410 prior**. We give both because the module-level split is the one a reader can check by opening files, and the obligation-level split is the one that is true. **Further caveat:** the erasure instance is no longer purely reused — its chain surface was re-modelled for this paper from a height *pre-order* to a `prev`-pointer *adjacency*, and the governance instance's position surface `J1` likewise — which is what makes the closure genuinely multi-step (see `AuditLogWitness`) and the governance `I = 2` two surfaces rather than one counted twice (`J1_J2_Distinct`). The anonymity instance's `Graph` surface was likewise re-modelled, from a boolean exposure flag to **multi-input spend adjacency** (`inputs` is set-valued, so a transaction joins *all* of its inputs; see `AnonymityWitness`). The re-modelling and the wiring are new; the domain mappings are not.

## 3b. Notation ↔ specification (what the paper's symbols are called here)

The paper writes mathematics; the modules write TLA⁺. This is the mapping, so a claim in the paper can be located in the source without guessing. Every operator below is verbatim from `specs/`.

| Paper | TLA⁺ | Defined in | Definition |
|---|---|---|---|
| `E`, `L`, `⊥` | `E`, `L`, `Bot` | `Notarization` (CONSTANT) | effects, labels, the absent label |
| `lbl` | `lbl` | `Notarization` (CONSTANT) | the labelling; `Labelings == [E -> L \cup {Bot}]` |
| `lbl_⊥` | `AllBot` | `Synthesis` | `[e \in E \|-> Bot]` — the maximal key drop |
| `Surfaces`, `Rel(S,l)` | `Surfaces`, `Rel(S,l)` | `Notarization` (CONSTANT) | surfaces; `S`'s links **under labelling `l`** |
| `G` | `G` | `Notarization` (CONSTANT) | the established frontier |
| `LabelIndep(S)` | `LabelIndep(S)` | `Notarization` | `\A l1, l2 : Rel(S,l1) = Rel(S,l2)` |
| `Edge(x,y)` | `Edge(x,y)` | `Notarization` | `\E S : <<x,y>> \in Rel(S,lbl)` |
| `Reach` | `Reach` | `Notarization` | least `Edge`-closed superset of `G` |
| `Sep(e)` | `Sep(e)` — **and** `Separable(e)` | `Notarization` / `Antagonism` | both are `e \notin Reach`. Two names, one predicate: `Sep` is the framework's, `Separable` reads better beside `Sealed` |
| `Pins(S,e)` | `Pins(S,e)` | `Antagonism` | `\E g \in Reach : <<g,e>> \in Rel(S,lbl)` |
| `Handles(e)` | `Handles(e)` | `Antagonism` | `{S : LabelIndep(S) /\ Pins(S,e)}` |
| `I(e)` | *(no operator)* | — | `Cardinality(Handles(e))`. The seal multiplicity is **counted, not defined** — deliberately: counting needs finiteness, and the theorems are unbounded |
| `Sealed(e)` | `Sealed(e)` | `Antagonism` | `Handles(e) # {}` |
| `Reach_LI(l)` | `ReachLI(l)` | `Antagonism` | closure of `G` under the **label-independent** surfaces only |
| `SealedLI(e)` | `SealedLI(e)` | `Antagonism` | `\E S : LabelIndep(S) /\ PinsLI(S,e)` — pinned **from the LI closure**. Strictly stronger than `Sealed` |
| `TA` | `TA` | `Antagonism` | `\A x \in E : Sealed(x)` — total accountability |
| `Handles⁻(l,r)` | `HandlesMinus(l,r)` | `Synthesis` | `{S : \E x \in ReachExc(l,r) : <<x,r>> \in Rel(S,l)}` — **the least exit set** |
| `Reach^{-r}(l)` | `ReachExc(l,r)` | `Synthesis` | closure of `G` with every edge incident to `r` deleted |
| — | `SepAch(l,r,XS)` | `Synthesis` | separation of `r` is achieved under labelling `l` by exiting surface set `XS` |
| `Sink(r)` (*fresh*) | `Sink(r)` | `Synthesis` | `r` emits no link of its own — Corollary 4's hypothesis |
| key-type split | `Dichotomy` | `Synthesis` | `\A S : LabelIndep(S) \/ Rel(S,AllBot) = {}` |
| — | `ReachIn(SS)` | `Resilience` | closure restricted to a **subset** `SS` of surfaces (a surface removed) |

> **Two things worth knowing before reading the source.**
> `Rel` takes the labelling as an argument, so a surface *may* read the label; `LabelIndep` is the predicate saying it does not — the split is proved per instance (`*_Dichotomy`), never assumed.
> `Reach` and `ReachLI` are different closures, and so are `Sealed` and `SealedLI`. Conflating either pair is the mistake this development has had to correct before; `AuditLogWitness` exists to show they come apart.

---

## 4. The synthesis layer

`Synthesis.tla` (EXTENDS `Antagonism`) turns the law into an *analysis*: given a target effect **that is not already on the established frontier `G`**, the minimum-cost exit achieving non-establishment is unique, definable, and equals the effect's residual label-independent pin set (`HandlesMinus`); its cost is bounded by the seal multiplicity `I(r)` and, for fresh effects, equals the effect's orbit-invariant (`SealedLI`) handle set — which that bound contains, and which coincides with `I(r)` exactly where the pin comes from the frontier itself. For an effect already in `G` there is no such exit **at any cost** (`EstablishmentIsFinal`) — the `r ∉ G` conjunct of `LeastExit` is a load-bearing hypothesis, not a side condition. The module proves `LeastExit`, `KeyDropDominance`, `OptimalSynthesis`, `PriceWithinIntegrity`, `FreshExactness`, `ZeroPriceIffUnsealed`, and `EstablishmentIsFinal`. The complexity propositions (P / NP-complete / Minimum Label Cut) are paper-proved and are not in this bundle.

## 5. The four instances — honest scope

All four instances are `INSTANCE Synthesis WITH …` (hence of `Antagonism` and `Notarization`) and are **isomorphic** by design: each maps its domain's structural re-link to a label-independent surface and its privacy/identity binding to a label surface, then discharges the abstract `ASSUME`s, classifies its surfaces, *inherits* the impossibility, proves the "privacy move is futile" theorem, discharges the key-type split (`*_Dichotomy`), and computes its own least exit set (`*_LeastExit`). This isomorphism **is** the unification claimed in the paper — that independently-developed trade-offs share one structure under one predicate — and **not** a claim of depth in any single instance. The per-domain patterns are each community's own; what is new is that they are one law.

**Faithfulness commitments** (the paper proves each *formula*; a reviewer must grant the *modelling*):
- **erasure** — the chain links each entry to the one its `prev` pointer names, independent of the subject key (uncontested).
- **anonymity** — clustering is modelled as *multi-input spend adjacency*: `x` re-links `t` exactly when `t` consumes `x` (`x ∈ inputs[t]`), the multi-input heuristic of chain analysis, read independently of the pseudonym label. What a transaction records is which outputs it consumes; transitive clustering is the closure's job. Real clustering is heuristic, and the model captures the *linkage structure it operates on*, not its success probability. (An earlier revision made this a boolean `flowlinked` exposure flag — a cylinder that took the *conclusion* of clustering as a primitive input. That is no longer the model; see the note in `AnonymityInstance.tla`.)
- **deniability** — `G` is the *third-party epistemic frontier*; a transferable signature is a label-independent re-link from it, a forgeable MAC is not. The model captures *non-transferability*, abstracting the *simulatability* mechanism that achieves it — the level at which the deniability literature itself defines deniability.

Reject a commitment and that instance becomes a *boundary* case, not a member; the breadth claim then drops one rung (the paper states the ladder). Nothing here is forced.

## 6. Files

```
prove.sh                 one-command reproduction of the machine-checked claims
check.sh                 the synthesis checker (§2b); --negative for its self-test
logs/anc_reproduce.log   verbatim run of prove.sh
logs/checker.log         verbatim run of check.sh
logs/*.log               per-module TLAPS logs
checker/
  README.md              what the checker establishes, and how to disbelieve it
  leastexit.py           Proposition 1's procedure, implemented
  certify.py             asserts its output back into the witness modules (TLC)
  concrete.py            concrete members of all four instances -> the dividend table
  scaling.py             Proposition 1's bound, measured as an operation count
specs/
  Notarization.tla              the abstract label-independent notarization class
  Antagonism.tla                conservation law (Thm 1, Cor 1, Cor 2, Thm 2, Thm 3)
  Resilience.tla                strength axis (Remark 1)
  Synthesis.tla                 exit synthesis (Thm 4, Thm 5, Thm 6, Cor 3, Cor 4)
  DeniabilityInstance.tla       non-repudiation vs. deniability
  AnonymityInstance.tla         anonymity vs. accountability
  AuditLogInstance.tla          immutability vs. right-to-be-forgotten
                                (chain surface = prev-pointer adjacency)
  SepClosureInstance.tla        action non-establishment (governance)
  SepClosureTwoMachines.tla     (dependency of SepClosureInstance)
  AntagonismWitness.tla/.cfg    TLC: non-vacuity
  NecessityWitness.tla/.cfg     TLC: necessity of LI for the orbit layer
  AuditLogWitness.tla/.cfg      TLC: a length-2 closure, and Sealed/SealedLI
                                and Reach/ReachLI coming apart in a domain
  AnonymityWitness.tla/.cfg     TLC: a length-2 closure through a multi-input
                                spend join; two distinct Graph in-edges
  PriceWitness.tla/.cfg         TLC: a non-degenerate I(e) = 2 on two distinct
                                surfaces; Thm 6's inclusion strict
  TAWitness.tla/.cfg            TLC: Thm 2's hypothesis TA is satisfiable —
                                at the price of a self-pinning root
  StrictPriceWitness.tla/.cfg   TLC: I(r) = 2 with price 1 on a non-sink —
                                Thm 6 (bound) separated from Cor 4 (identity)
LICENSE                       MIT
```

Each of the four instances is an `INSTANCE Synthesis` (hence of `Antagonism` and `Notarization`): it discharges the abstract `ASSUME`s, inherits the law's theorems rather than re-proving local analogues, discharges the key-type split (`*_Dichotomy`), and computes its own least exit set (`*_LeastExit`).

(`specs/.tlacache/` — `tlapm`'s fingerprint cache — is not part of the bundle; see §2.)

## 7. License & availability

The TLA⁺ specifications, the reproduction script and the checker are released under the **MIT License** (see `LICENSE`, included in this bundle; every script also carries an `SPDX-License-Identifier: MIT` header). They contain no proprietary source and depend on none. See the paper's "Artifact availability" for the citable archive.
