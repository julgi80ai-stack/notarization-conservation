#!/usr/bin/env bash
# ===========================================================================
# Reproduction artifact for
#   "A Conservation Law for Accountable Systems: Integrity and
#    Non-Establishment as Antagonistic Resources, with Machine-Checked
#    Instances in Deniability, Anonymity, and Erasure"
#
# Reproduces EVERY machine-checked claim in the paper, self-contained:
#   TLAPS (unbounded, machine-PROVEN):
#     Notarization          framework lemmas (closure, decisive lemma)
#     Antagonism            Thm 1, Cor 1, Thm 2 (L1 recovery), Thm 4
#     Resilience            Thm 3 (strength axis)
#     Synthesis             exit synthesis: LeastExit, KeyDropDominance,
#                           OptimalSynthesis, PriceWithinIntegrity,
#                           FreshExactness, ZeroPriceIffUnsealed
#     DeniabilityInstance   non-repudiation XOR deniability  (class member)
#     AnonymityInstance     anonymity XOR accountability      (class member)
#     AuditLogInstance      immutability XOR right-to-be-forgotten (member)
#     SepClosureInstance    action non-establishment (governance, origin)
#   TLC (existence / necessity, machine-CHECKED):
#     AntagonismWitness     Thm 1 non-vacuity
#     NecessityWitness      label-independence is load-bearing
#
# Requires: tlapm 1.5.0 on PATH (export PATH="$HOME/tlaps/bin:$PATH")
#           tla2tools.jar (v2.19) + Java 21   [TLC_JAR overrides location]
# ===========================================================================
set -euo pipefail
cd "$(dirname "$0")/specs"
export PATH="$HOME/tlaps/bin:$PATH"
TLC_JAR="${TLC_JAR:-/tmp/tla2tools.jar}"

P() { tlapm --toolbox 0 0 "$1.tla" 2>&1 | grep -E "All [0-9]+ obligations? proved|failed|omitted" | tail -1; }
C() { java -XX:+UseParallelGC -cp "$TLC_JAR" tlc2.TLC -config "$1.cfg" "$1.tla" 2>&1 \
        | grep -E "No error has been found|Error|violated" | tail -1; }

echo "================ TLAPS (universal, unbounded) ================"
for M in Notarization Antagonism Resilience Synthesis \
         DeniabilityInstance AnonymityInstance AuditLogInstance SepClosureInstance; do
  printf "%-22s : " "$M"; P "$M"
done

echo "================ TLC (existence / necessity) ================"
for W in AntagonismWitness NecessityWitness; do
  printf "%-22s : " "$W"; C "$W"
done

echo
echo "Expected: 8x 'All N obligations proved' (TLAPS, 0 omitted) + 2x 'No error has been found' (TLC)."
echo "Universal = proven (TLAPS); existence/necessity = checked (TLC); synthesis complexity (Sec. 7.3) & crypto dual (Sec. 9) = argued in paper."
