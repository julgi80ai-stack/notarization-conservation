# The synthesis checker

Proposition 1 of the paper says the least exit set of an effect can be computed
in `O(|E| + Σ_S |Rel(S)|)`. This directory implements that procedure and then
does the thing that makes an implementation worth shipping: **it hands its
answers to TLC and has the specifications refuse or confirm them.**

Run it:

```sh
cd ..            # the bundle root, next to prove.sh
./check.sh
```

`prove.sh` and `check.sh` are independent. Nothing here can change the verdict
of `prove.sh` — the 1,181 obligations and 7 witnesses stand on their own. If
you only care about the machine-checked claims, you can ignore this directory.

---

## 1. The problem this solves, and why it is not the obvious one

The obvious design is: write the procedure in Python, run it, print a table,
compare the table with the paper by eye. A reviewer answers that in one line —
*"what makes your Python agree with your TLA⁺?"* Nothing would. The tool would
be a second, unverified statement of the same claim.

So the output is not printed for comparison. It is **asserted back into the
specification**:

```
  ① the checker computes an answer, from its own implementation
       HandlesMinus(AllBot, "r")  =  {"Chain"}

  ② that answer is written into a TLA+ module that EXTENDS the real one
       ---- MODULE AuditLogConcrete ----
       EXTENDS AuditLogInstance                 <- the artifact's own module
       CheckerOutput == /\ A!HandlesMinus(A!AllBot, "r") = {"Chain"}
                        ...

  ③ TLC evaluates it using the SPECIFICATION's definitions
       Model checking completed. No error has been found.
```

A pass is therefore not *"our tool says so"* but *"an independent
implementation computed this, and the artifact that owns the definitions
confirmed it."*

Two details keep that honest:

- **Nothing is copied.** The generated modules `EXTENDS` the real ones and add
  no definition of their own. The `.tla` files inside `gen/` and `gen3/` are
  **symlinks** into `../specs/`, so a certificate cannot drift away from the
  module it claims to certify. Watch TLC's own parse log say so:
  `Parsing .../anc/specs/AuditLogInstance.tla`, then `Synthesis`, `Antagonism`,
  `Notarization` — the whole law is loaded.
- **Only what the module defines is asserted.** `TAWitness.tla` does not define
  `HandlesMinus`, so its certificate does not mention it (see `CAPS` in
  `certify.py`). Filling in a missing definition ourselves and then certifying
  against it would prove nothing.

## 2. If you do not believe a PASS means anything

Neither did we. A certification that can only pass might be reporting an
invariant TLC never evaluates. So the check is runnable:

```sh
./check.sh --negative
```

It regenerates each certificate with **one deliberately wrong value** — the
effect's full handle set `Handles(r)` stated where the least exit set
`HandlesMinus(⊥, r)` belongs, which Theorem 7 makes a strict subset in these
models — and requires TLC to reject it:

```
  AuditLogWitness      good  TLC refused it: Error: The invariant of CheckerOutput is equal to FALSE
  AnonymityWitness     good  TLC refused it: Error: The invariant of CheckerOutput is equal to FALSE
  StrictPriceWitness   good  TLC refused it: Error: The invariant of CheckerOutput is equal to FALSE
```

The true certificates are restored automatically afterwards.

## 3. What each step establishes

| Step | Script | Establishes |
|---|---|---|
| 1 | `leastexit.py` | The procedure, implemented. Every operator carries the TLA⁺ line it mirrors in its docstring, so the correspondence is auditable by eye — and then stops depending on eyes at step 2. |
| 2 | `certify.py` | The specification confirms the checker on all four witness models that have the needed operators. |
| 3 | `concrete.py` | Concrete finite members of **all four domain instances**, each `EXTENDS`ing its instance module with constants fixed in the `.cfg`. Reproduces the paper's four-domain table as tool output. |
| 4 | `scaling.py` | Proposition 1's bound, measured — as a **step count**, not a stopwatch. |

### Step 3 in more detail — why it is stronger than step 2

The witness modules (`AuditLogWitness.tla` and friends) copy the abstract
definitions in by hand and say so: *"All definitions are copied VERBATIM …
Faithfulness is by syntactic identity."* That is a claim about a
transcription, and a reader has to check it.

Step 3 removes the transcription. Each model is a module that `EXTENDS` the
**instance** — `DeniabilityInstance`, `AnonymityInstance`, `AuditLogInstance`,
`SepClosureInstance` — and fixes that module's `CONSTANTS` in the `.cfg`. TLC
then evaluates `HandlesMinus` through the module's own `INSTANCE Synthesis`
wiring: the same wiring the TLAPS proofs use.

Three things overlap in one run:

1. **The model is a legal member of the class.** TLC enforces the instance
   module's `ASSUME`s. (Check it: set `NoSubj = "k"` in
   `gen3/AuditLogConcrete.cfg` and TLC answers `Assumption line 50 … of module
   AuditLogInstance is false`. Note TLC reports only its *first* error and
   invariants come first, so to see an assumption failure you must leave the
   invariant true.)
2. **The theorems are not vacuous.** Each model's constants are chosen to
   satisfy the hypotheses of that domain's `*_LeastExit` and `*_ZeroPrice`
   theorems, and those hypotheses are asserted in the invariant alongside the
   conclusion.
3. **The values agree** — independent implementation, and the wired law.

Reproduced (each row also a theorem of its own module):

| Instance | Adjudicator | least exit | price | free case |
|---|---|---|---|---|
| Deniability | third party (judge) | `{Sig}` | 1 | unsigned → `{}` |
| Unlinkability | de-anonymising analyst | `{Graph}` | 1 | no inputs → `{}` |
| RTBF | chain verifier | `{Chain}` | 1 | no `prev` → `{}` |
| Action governance | auditor of the record | `{J1, J2}` | 2 | not emitted → `{}` |

The checker also prints a note for every effect on the frontier `G`:
establishment is final (Corollary 4), so whatever `HandlesMinus` returns for
such an effect is **not a price** — no exit set separates it at all. That note
is not decoration; it is what a caller must not misread.

### Step 4 — why a count and not a clock

Proposition 1 is the one result in the paper that is not machine-checked
(*"only the running-time count lives on paper"*). `scaling.py` measures it as
an operation count: one touch per edge scanned, one per edge traversed, one
per node settled — the three steps of the appendix proof, in order.

`ops / (|E| + Σ|Rel|)` comes out **bounded by 2**, rising toward 2 as edges
come to dominate nodes. Wall time is printed too and is *not* the measurement:
the same input has timed anywhere from 14× to 26× a 10× smaller one across
runs on one machine, while the ops figure is identical to the digit. The
counted implementation is checked against the certified one on every model in
the bundle before any number is printed.

## 4. Files

```
check.sh              (in the bundle root) one command; --negative for the self-test
checker/
  leastexit.py        the procedure; each operator quotes the TLA+ it mirrors
  certify.py          generates <Module>Cert.tla, runs TLC   [--negative]
  concrete.py         generates <Domain>Concrete.tla for the four instances
  scaling.py          Proposition 1's bound, measured as a step count
  gen/  gen3/         generated certificates + symlinks to ../specs (not shipped)
```

Python 3 standard library only. No package to install.

## 5. What this is not

It is **not a verification tool for other people's systems.** It runs one
procedure on the finite models in this bundle. Its computational content is a
graph reachability pass; nobody doubted that such a pass is linear. What it
adds is the evidence grade of claims the paper already makes: the four-domain
table stops being a reading of the theory and becomes an output the
specification signs off on, and the paper's one unmeasured bound gets measured.

It found two real defects while being built, which is the honest argument for
its existence: a hand-written mirror of `AnonymityWitness` that had the wrong
structure and computed a price of 1 where the answer is 0, and a missing
`r ∉ G` guard in a remark of the paper — caught by the frontier note above.
