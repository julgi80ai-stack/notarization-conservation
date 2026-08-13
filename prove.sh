#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# ===========================================================================
# Reproduction artifact for
#   "The Price of Non-Establishment: Least Exit Sets in Label-Independent
#    Notarization, with Machine-Checked Instances"
#
# Reproduces EVERY machine-checked claim in the paper, self-contained:
#   TLAPS (unbounded, machine-PROVEN):
#     Notarization          framework lemmas (closure, decisive lemma)
#     Antagonism            Thm 1, Cor 1, Cor 2 (orbit), Thm 2, Thm 3
#     Resilience            Thm 4 (strength axis)
#     Synthesis             exit synthesis (Thm 5, Thm 6, Thm 7, Cor 3,
#                           Cor 4): LeastExit, KeyDropDominance,
#                           OptimalSynthesis, PriceWithinIntegrity,
#                           FreshExactness, ZeroPriceIffUnsealed,
#                           EstablishmentIsFinal
#     DeniabilityInstance   non-repudiation XOR deniability  (class member)
#     AnonymityInstance     anonymity XOR accountability      (class member)
#     AuditLogInstance      immutability XOR right-to-be-forgotten (member)
#     SepClosureInstance    action non-establishment (governance, origin)
#   TLC (existence / necessity, machine-CHECKED):
#     AntagonismWitness     Thm 1 non-vacuity
#     NecessityWitness      label-independence is load-bearing
#     AuditLogWitness       depth-2 closure path; Sealed/SealedLI and
#                           price/integrity distinctions realized (M4)
#     AnonymityWitness      depth-2 closure path through a MULTI-INPUT
#                           spend join: two distinct Graph in-edges, so
#                           the surface is neither a cylinder nor a
#                           predecessor pointer (D-4b)
#     PriceWitness          non-degenerate I = 2 (two DISTINCT LI handles),
#                           price < integrity, strict Thm-7 inclusion (M5)
#     TAWitness             TA satisfiable at class level -- via a root
#                           self-pin (the trust-anchor convention) (M9)
#     StrictPriceWitness    Thm 7 strictly a BOUND at I = 2: price 1 < 2
#                           on a non-sink (outside Cor 3) (M9)
#
# The SYNTHESIS CHECKER is a separate, independent entry point: ./check.sh
# (see README section 2b).  It cannot affect anything this script reports.
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
for W in AntagonismWitness NecessityWitness AuditLogWitness AnonymityWitness \
         PriceWitness TAWitness StrictPriceWitness; do
  printf "%-22s : " "$W"; C "$W"
done

echo
echo "Expected: 8x 'All N obligations proved' (TLAPS, 0 omitted) + 7x 'No error has been found' (TLC)."
echo "Universal = proven (TLAPS); existence/necessity = checked (TLC); synthesis complexity (Sec. 7.3) & crypto dual (Sec. 9) = argued in paper."
