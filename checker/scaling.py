#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Phase 4 -- Proposition 1's O(|E| + sum_S |Rel(S)|), measured.

Proposition 1 is the one result in the paper that is *not* machine-checked:
"only the running-time count lives on paper" (Appendix A).  Nothing in the
artifact measured it.  This does.

The measurement is primarily a COUNT, not a clock.  Wall time on a shared
machine is a statement about the machine; an operation count is a statement
about the algorithm, and it is what the O(.) claim is about.  Counting also
survives what a stopwatch cannot: while this was written, seven orphaned z3
processes were pinning seven cores of this host, which would have made any
timing curve meaningless.  Times are reported too, clearly marked as
load-sensitive.

The counted implementation is not trusted on its own.  It is checked against
leastexit.py -- the implementation TLC certified in Phases 2 and 3 -- on every
model in the artifact before any number below is produced.

    python3 scaling.py            # agreement check, then both families
"""

import sys
import time

import certify
import concrete
import leastexit as L

BOT = L.BOT


# --------------------------------------------------------------------------
# The procedure again, this time counting.  The three steps are Appendix A's
# three steps, in order, so the count can be read against the proof.
# --------------------------------------------------------------------------

def least_exit_counted(model, r):
    """Returns (least exit set, ops).  `ops` counts the elementary steps the
    proof charges for: one touch per edge scanned, one per node settled."""
    ops = 0
    E, G, surfaces = model["E"], model["G"], model["surfaces"]
    ab = L.all_bot(E)

    # (1) Collect the edges that survive the maximal key drop and delete the
    #     pairs incident to r.  One scan: O(sum_S |Rel(S)|).
    adj, into_r = {}, {}
    for name, s in surfaces.items():
        for (x, y) in s["rel"](ab):
            ops += 1
            if y == r:
                into_r.setdefault(name, set()).add(x)
                continue
            if x == r:
                continue
            adj.setdefault(x, []).append(y)

    # (2) One reachability pass from G over what remains: O(|E| + edges).
    X, stack = set(G), list(G)
    ops += len(G)
    while stack:
        x = stack.pop()
        ops += 1
        for y in adj.get(x, ()):
            ops += 1
            if y not in X:
                X.add(y)
                stack.append(y)

    # (3) One further scan reads off HandlesMinus.
    out = set()
    for name, srcs in into_r.items():
        ops += 1
        if srcs & X:
            out.add(name)
    return out, ops


# --------------------------------------------------------------------------
# Agreement: the counted implementation must equal the certified one.
# --------------------------------------------------------------------------

def agreement():
    models = [f() for f in L.MODELS] + [f()["py"] for f in concrete.MODELS]
    bad = 0
    for m in models:
        ab = L.all_bot(m["E"])
        for r in m["E"]:
            a = L.handles_minus(m, ab, r)
            b, _ = least_exit_counted(m, r)
            if a != b:
                print(f"  [FAIL] {m['name']} / {r}: counted {sorted(b)} "
                      f"!= certified {sorted(a)}")
                bad += 1
    n = sum(len(m["E"]) for m in models)
    print(f"  counted implementation agrees with the TLC-certified one on "
          f"{n - bad}/{n} effects across {len(models)} models")
    return bad == 0


# --------------------------------------------------------------------------
# Two families.  The bound has two terms, so vary them one at a time.
# --------------------------------------------------------------------------

def fam_chain(n):
    """|E| grows, edges grow with it: a hash-chained log of n entries.
    The target is the newest entry; its least exit set is {Chain} at every n
    (Audit_LeastExit), so the answer is size-independent and only the work
    changes."""
    E = [f"e{i}" for i in range(n)]
    chain = {(f"e{i}", f"e{i+1}") for i in range(n - 1)}
    return ({"name": f"chain-{n}", "E": E, "G": {"e0"},
             "lbl": {e: BOT for e in E},
             "surfaces": {"Chain": {"li": True, "rel": lambda l: chain}}},
            f"e{n-1}", n, len(chain), {"Chain"})


def fam_dense(n, k):
    """|E| fixed, sum|Rel| grows: each effect consumes k inputs (a spend graph
    with fan-in k).  Isolates the second term of the bound."""
    E = [f"e{i}" for i in range(n)]
    ins = {(f"e{max(0, i-1-j)}", f"e{i}")
           for i in range(1, n) for j in range(k)}
    return ({"name": f"dense-{n}x{k}", "E": E, "G": {"e0"},
             "lbl": {e: BOT for e in E},
             "surfaces": {"Graph": {"li": True, "rel": lambda l: ins}}},
            f"e{n-1}", n, len(ins), {"Graph"})


def run(family, cases, title):
    print(f"\n=== {title} ===")
    print(f"  {'|E|':>7} {'sum|Rel|':>9} {'ops':>10} {'ops/(E+R)':>10} "
          f"{'ms':>8} {'ms/prev':>8} {'size/prev':>9}")
    prev_t = prev_s = None
    for args in cases:
        model, r, ne, nr, expect = family(*args)
        # build once, outside the clock: the bound is about the procedure,
        # not about constructing the input
        got, ops = least_exit_counted(model, r)
        assert got == expect, (model["name"], got, expect)
        ts = []
        for _ in range(3):
            t0 = time.perf_counter()
            least_exit_counted(model, r)
            ts.append((time.perf_counter() - t0) * 1e3)
        t, size = sorted(ts)[1], ne + nr
        gt = f"{t / prev_t:.1f}x" if prev_t else "-"
        gs = f"{size / prev_s:.1f}x" if prev_s else "-"
        prev_t, prev_s = max(t, 1e-9), size
        print(f"  {ne:>7} {nr:>9} {ops:>10} {ops / size:>10.2f} "
              f"{t:>8.1f} {gt:>8} {gs:>9}")


def main():
    print("=== agreement with the certified implementation ===")
    if not agreement():
        print("\nDISAGREEMENT — the counted implementation is wrong; no "
              "measurement below would mean anything.")
        return 1

    run(fam_chain, [(100,), (1000,), (10000,), (50000,), (100000,)],
        "family 1: |E| grows (hash-chained log, target = newest entry)")
    run(fam_dense, [(2000, 1), (2000, 5), (2000, 20), (2000, 50),
                    (2000, 100)],
        "family 2: |E| fixed at 2000, fan-in k grows (spend graph)")

    print("""
READING THE TABLES

  ops/(|E|+sum|Rel|) is bounded by 2 and rises toward it as edges come to
  dominate nodes (1.50 on the chain, where |Rel| ~ |E|; 1.99 at fan-in 100).
  That is the constant the proof implies, not a coincidence: step (1) touches
  every edge once and step (2) traverses it once, plus one settle per node.
  So the OPERATION COUNT is linear in |E| + sum_S |Rel(S)| -- Proposition 1's
  bound, measured.

  WALL TIME tracks size/prev at the large end (about 2x for 2x on both
  families) and overshoots in the middle.  By how much is not reproducible:
  the same 10x input at |E|=10^4 has measured anywhere from 14x to 26x across
  runs of this script, on the same machine, while the ops column is identical
  to the digit every time.  Attributing that spread to the procedure would be
  a mistake -- it belongs to Python dict and set resizing, timer resolution
  on a sub-millisecond base, and whatever else the host is doing.

  That instability is the argument for counting.  Proposition 1 asserts a
  step count; a step count is what a contended or noisy machine cannot
  corrupt, and it is what this table therefore reports as the measurement.""")
    return 0


if __name__ == "__main__":
    sys.exit(main())
