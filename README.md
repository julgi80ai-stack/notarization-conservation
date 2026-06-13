# Reproduction artifact — *A Conservation Law for Accountable Systems*

Machine-checked companion to the paper **"A Conservation Law for Accountable Systems: Integrity and Non-Establishment as Antagonistic Resources, with Machine-Checked Instances in Deniability, Anonymity, and Erasure."**

This bundle is **self-contained** and reproduces **every** machine-checked claim in the paper with one command. Universals are *proven* (TLAPS, unbounded); existence/necessity are *checked* (TLC); the synthesis complexity propositions (paper §7.3) and the cryptographic dual (paper §9) are *paper-proved arguments*, not machine-checked, and are not part of this bundle.

---

## 1. Requirements

- **TLAPS** (`tlapm`) 1.5.0 on `PATH` — backends Isabelle / Zenon / SMT.
  `export PATH="$HOME/tlaps/bin:$PATH"`
- **TLC**: `tla2tools.jar` (v2.19) + Java 21. Default location `/tmp/tla2tools.jar`; override with `TLC_JAR=/path/to/tla2tools.jar`. (Not bundled — fetch from the TLA⁺ tools releases.)

The specifications use only `Naturals`, `FiniteSets`, and the `TLAPS` standard module; they depend on no external library and on no source code of any audited system.

## 2. Reproduce

```sh
export PATH="$HOME/tlaps/bin:$PATH"
./prove.sh
```

Expected output: **8× "All N obligations proved"** (TLAPS, 0 omitted/admitted) and **2× "No error has been found"** (TLC). A verbatim run is in `logs/anc_reproduce.log`.

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
| **Theorem 4** | redundancy ⟹ resilience (strength axis) | `Resilience.tla` | TLAPS | 11 |
| **Theorem 5** | least exit set is unique & definable (`LeastExit`) | `Synthesis.tla` | TLAPS | 316 (module) |
| **Theorem 6** | key-drop dominance; closed-form optimal synthesis | `Synthesis.tla` | TLAPS | ″ |
| **Theorem 7** | separation price ⊆ integrity strength (`PriceWithinIntegrity`) | `Synthesis.tla` | TLAPS | ″ |
| **Corollary 3** | fresh effects: price = `SealedLI` handles; zero iff unsealed | `Synthesis.tla` | TLAPS | ″ |
| Non-vacuity | `Sealed`, `Separable` both realised | `AntagonismWitness.tla`+`.cfg` | TLC | — |
| Necessity | label-independence is load-bearing | `NecessityWitness.tla`+`.cfg` | TLC | — |
| Instance — deniability | non-repudiation vs. deniability (`RepudiationFutileOnSig`) | `DeniabilityInstance.tla` | TLAPS | 44 |
| Instance — anonymity | anonymity vs. accountability (`ClusteringFutile`) | `AnonymityInstance.tla` | TLAPS | 44 |
| Instance — erasure | immutability vs. right-to-be-forgotten (`ErasureFutile`) | `AuditLogInstance.tla` | TLAPS | 44 |
| Instance — governance | action non-establishment (`AcctKeyStripFutile`) | `SepClosureInstance.tla` (+ `SepClosureTwoMachines.tla`) | TLAPS | 53 |

**Total reproduced by `prove.sh`: 679 TLAPS obligations (0 omitted/admitted) + 2 TLC witnesses.**

Per-module counts: `Notarization` 83, `Antagonism` 84, `Resilience` 11, `Synthesis` 316, `DeniabilityInstance` 44, `AnonymityInstance` 44, `AuditLogInstance` 44, `SepClosureInstance` 53.

### New to this paper vs. reused (honest breakdown)
- **New (the conservation law, the synthesis layer, and two new instances): 499 obligations** — `Antagonism` (84, incl. the orbit corollary) + `Resilience` (11) + `Synthesis` (316) + `DeniabilityInstance` (44) + `AnonymityInstance` (44).
- **Reused / reproduced for completeness: 180 obligations** — `Notarization` (83, the framework this paper builds on) + `AuditLogInstance` (44) + `SepClosureInstance` (53). These originate in the authors' prior notarization-class development; they are included here so the paper's §10 class table is reproducible end-to-end in one bundle, not to claim them as new.

## 4. The synthesis layer (paper §7)

`Synthesis.tla` (EXTENDS `Antagonism`) turns the law into an *analysis*: given a target effect, the minimum-cost exit achieving non-establishment is unique, definable, and equals the effect's residual label-independent pin set (`HandlesMinus`); its cost is bounded by — and for fresh effects equal to — integrity strength. The module proves `LeastExit`, `KeyDropDominance`, `OptimalSynthesis`, `PriceWithinIntegrity`, `FreshExactness`, and `ZeroPriceIffUnsealed`. The complexity propositions (P / NP-complete / Minimum Label Cut) are paper-proved in §7.3 and are not in this bundle.

## 5. The four instances (paper §10) — honest scope

All four instances are `INSTANCE Notarization WITH …` and are **isomorphic** by design: each maps its domain's structural re-link to a label-independent surface and its privacy/identity binding to a label surface, then proves the same facts (surface classification; the impossibility `*Pins`; the "privacy move is futile" theorem). This isomorphism **is** the unification claimed in the paper — that independently-developed trade-offs share one structure under one predicate — and **not** a claim of depth in any single instance. The per-domain patterns are each community's own; what is new is that they are one law.

**Faithfulness commitments** (the paper proves each *formula*; a reviewer must grant the *modelling*):
- **erasure** — the chain links by position independent of the subject key (uncontested).
- **anonymity** — graph clustering is modelled as a *boolean* label-independent re-link (`flowlinked`); real clustering is heuristic. The boolean abstraction captures "exposed-or-not," not success probability.
- **deniability** — `G` is the *third-party epistemic frontier*; a transferable signature is a label-independent re-link from it, a forgeable MAC is not. The model captures *non-transferability*, abstracting the *simulatability* mechanism that achieves it — the level at which the deniability literature itself defines deniability.

Reject a commitment and that instance becomes a *boundary* case, not a member; the breadth claim then drops one rung (the paper states the ladder). Nothing here is forced.

## 6. Files

```
prove.sh                 one-command reproduction (this bundle)
logs/anc_reproduce.log   verbatim run
logs/*.log               per-module TLAPS logs
specs/
  Notarization.tla              the abstract label-independent notarization class
  Antagonism.tla                conservation law (Thm 1, Cor 1, Cor 2, Thm 2, Thm 3)
  Resilience.tla                strength axis (Thm 4)
  Synthesis.tla                 exit synthesis (Thm 5, Thm 6, Thm 7, Cor 3)
  DeniabilityInstance.tla       non-repudiation vs. deniability
  AnonymityInstance.tla         anonymity vs. accountability
  AuditLogInstance.tla          immutability vs. right-to-be-forgotten
  SepClosureInstance.tla        action non-establishment (governance)
  SepClosureTwoMachines.tla     (dependency of SepClosureInstance)
  AntagonismWitness.tla/.cfg    TLC: non-vacuity
  NecessityWitness.tla/.cfg     TLC: necessity of label-independence
```

(`specs/.tlacache/` — `tlapm`'s fingerprint cache — is not part of the bundle; see §2.)

## 7. License & availability

The TLA⁺ specifications and the reproduction script are released under the **MIT License** (see `LICENSE`). They contain no proprietary source and depend on none. See the paper's "Artifact availability" for the citable archive.
