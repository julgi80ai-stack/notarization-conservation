#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# ===========================================================================
# Reproduction artifact for
#   "The Price of Non-Establishment: Least Exit Sets in Label-Independent
#    Notarization, with Machine-Checked Instances"
#
# SECOND ENTRY POINT — the synthesis CHECKER.  `./prove.sh` reproduces the
# machine-checked claims (TLAPS + TLC); this script runs the least-exit-set
# procedure of Proposition 1 as an actual program and has TLC confirm its
# output against the specifications themselves.
#
# The two are independent on purpose.  Nothing here can change the verdict of
# `prove.sh`: the 1,181 obligations and 7 witnesses stand or fall on their own,
# and a reader who does not care about the tool can ignore this file entirely.
#
#   1. checker      run the procedure on every witness model in this bundle
#   2. certify      assert those outputs as TLC invariants over the REAL
#                   witness modules  ->  the specification certifies the tool
#   3. instances    concrete finite members of all four domain instances,
#                   EXTENDing the instance modules themselves (no definition
#                   is copied)  ->  Table 2 of the paper, as tool output
#   4. scaling      Proposition 1's O(|E| + sum_S |Rel(S)|), measured as a
#                   step count (the paper's only non-machine-checked result)
#
#   ./check.sh --negative
#                   NON-VACUITY SELF-TEST.  States one deliberately WRONG
#                   value per model and requires TLC to refuse it.  Run this
#                   if you do not believe the PASSes above mean anything.
#
# Requires: Python 3 (standard library only)
#           tla2tools.jar (v2.19) + Java 21   [TLC_JAR overrides location]
#           TLAPS.tla, for step 3 only -- the instance modules EXTEND it
#                                         [TLAPS_LIB overrides location]
# ===========================================================================
set -euo pipefail
cd "$(dirname "$0")/checker"

export TLC_JAR="${TLC_JAR:-/tmp/tla2tools.jar}"

# TLAPS.tla ships with tlapm; find it next to whatever tlapm is on PATH.
if [ -z "${TLAPS_LIB:-}" ]; then
  if command -v tlapm >/dev/null 2>&1; then
    TLAPS_LIB="$(cd "$(dirname "$(command -v tlapm)")/../lib/tlaps" && pwd)"
  else
    TLAPS_LIB="$HOME/tlaps/lib/tlaps"
  fi
fi
export TLAPS_LIB

if [ "${1:-}" = "--negative" ]; then
  python3 certify.py --negative
  echo
  echo "Restoring the true certificates ..."
  python3 certify.py >/dev/null
  echo "done."
  exit 0
fi

echo "================ 1. the procedure, run ================"
python3 leastexit.py

echo "================ 2. the specification certifies it ================"
python3 certify.py

echo "================ 3. the four instances, made concrete ================"
python3 concrete.py

echo "================ 4. Proposition 1, measured ================"
python3 scaling.py

echo
echo "Expected: 4x PASS (step 2) + 4x 'TLC PASS' (step 3), Table 2 reproduced,"
echo "and ops/(|E|+sum|Rel|) bounded by 2 (step 4)."
echo "Not convinced a PASS means anything?  Run:  ./check.sh --negative"
