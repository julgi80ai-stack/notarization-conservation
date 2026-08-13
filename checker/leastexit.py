#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Least-exit-set checker — Proposition 1's procedure, implemented.

Every operator below mirrors a definition in ../specs/Synthesis.tla
(which EXTENDS Antagonism EXTENDS Notarization).  The TLA+ source of each is
quoted above it so that the correspondence is auditable by eye; certify.py
then replaces eye-auditing with TLC certification of this file's output.

Stdlib only, by design: the artifact's stated requirements are tlapm + Java,
and this adds Python 3 alone.

    python3 leastexit.py            # run every model, print verdicts
    python3 leastexit.py --scale    # Prop 1 scaling measurement
"""

import sys
import time
from itertools import product

BOT = "_"  # the absent label; matches Bot / NoSubj / NoId / NoAuth / NONE


# --------------------------------------------------------------------------
# A model is a concrete, finite member of the abstract class.
#   E        : list of effects
#   G        : set of effects on the established frontier
#   lbl      : dict effect -> label (BOT for "no key")
#   surfaces : dict name -> {"li": declared label-independent?,
#                            "rel": callable(lbl_dict) -> set of (x, y) pairs}
# `rel` takes the labelling so that a key-equality surface really reads it —
# exactly as Rel(S, l) does in the specs.
# --------------------------------------------------------------------------


def all_bot(E):
    """Synthesis.tla:  AllBot == [e \\in E |-> Bot]"""
    return {e: BOT for e in E}


def edges_at(model, lbl):
    """Synthesis.tla:  EdgeAt(l,x,y) == \\E S \\in Surfaces : <<x,y>> \\in Rel(S,l)

    NOTE the union is over ALL surfaces, not only the label-independent ones.
    Filtering by LI here is the natural mis-implementation; it would make the
    r-deleted closure too small and the price too cheap.
    """
    adj = {}
    for s in model["surfaces"].values():
        for (x, y) in s["rel"](lbl):
            adj.setdefault(x, set()).add(y)
    return adj


def reach_exc(model, lbl, r):
    """Synthesis.tla:
         ClosedExc(l,r,X) == \\A x,y \\in E :
             (x \\in X /\\ EdgeAt(l,x,y) /\\ x # r /\\ y # r) => y \\in X
         ReachExc(l,r)    == least such X containing G

    Propagate only along edges whose BOTH endpoints differ from r.  G is
    included unconditionally -- even if r \\in G, in which case r enters X but
    never propagates.
    """
    adj = edges_at(model, lbl)
    X = set(model["G"])
    stack = [x for x in X]
    while stack:
        x = stack.pop()
        if x == r:
            continue
        for y in adj.get(x, ()):
            if y == r or y in X:
                continue
            X.add(y)
            stack.append(y)
    return X


def reach(model, lbl):
    """Notarization.tla:  Reach == least Edge-closed superset of G."""
    adj = edges_at(model, lbl)
    X = set(model["G"])
    stack = [x for x in X]
    while stack:
        x = stack.pop()
        for y in adj.get(x, ()):
            if y not in X:
                X.add(y)
                stack.append(y)
    return X


def handles_minus(model, lbl, r):
    """Synthesis.tla:
         HandlesMinus(l,r) == { S \\in Surfaces :
             \\E x \\in ReachExc(l,r) : <<x,r>> \\in Rel(S,l) }

    This is the least exit set (`LeastExit`) and its size is the price.
    """
    RE = reach_exc(model, lbl, r)
    out = set()
    for name, s in model["surfaces"].items():
        rel = s["rel"](lbl)
        if any((x, r) in rel for x in RE):
            out.add(name)
    return out


def handles(model, r):
    """Antagonism.tla:
         Pins(S,e)  == \\E g \\in Reach : <<g,e>> \\in Rel(S,lbl)
         Handles(e) == { S : LabelIndep(S) /\\ Pins(S,e) }
    Seal multiplicity I(e) is |Handles(e)|.
    """
    lbl = model["lbl"]
    R = reach(model, lbl)
    out = set()
    for name, s in model["surfaces"].items():
        if not s["li"]:
            continue
        rel = s["rel"](lbl)
        if any((g, r) in rel for g in R):
            out.add(name)
    return out


def is_sink(model, r):
    """Synthesis.tla:  Sink(r) == \\A S, y : <<r,y>> \\notin Rel(S,lbl)"""
    lbl = model["lbl"]
    return not any((r, y) in s["rel"](lbl)
                   for s in model["surfaces"].values() for y in model["E"])


# --------------------------------------------------------------------------
# Checks.  Each one corresponds 1:1 to a claim in the paper.
# --------------------------------------------------------------------------

def check_model(model):
    E, lbl, ab = model["E"], model["lbl"], all_bot(model["E"])
    findings, ok = [], True

    # Dichotomy (Synthesis.tla): every surface is LI or vanishes at AllBot.
    # The LI half is universally quantified over labellings and so is taken as
    # declared; what is checkable here is the other half, plus a necessary
    # condition for the declared LI ones.
    for name, s in model["surfaces"].items():
        if s["li"]:
            if s["rel"](ab) != s["rel"](lbl):
                findings.append(f"  [FAIL] {name}: declared LI but "
                                f"Rel(S,AllBot) != Rel(S,lbl)")
                ok = False
        else:
            if s["rel"](ab) != set():
                findings.append(f"  [FAIL] {name}: declared key-type but "
                                f"Rel(S,AllBot) is non-empty -- Dichotomy fails")
                ok = False

    # Per-effect facts.
    rows = []
    for r in E:
        hm, h = handles_minus(model, ab, r), handles(model, r)
        rows.append((r, hm, h, is_sink(model, r), r in model["G"]))

        # PriceWithinIntegrity: HandlesMinus(AllBot, r) subseteq Handles(r)
        if not hm <= h:
            findings.append(f"  [FAIL] {r}: PriceWithinIntegrity violated, "
                            f"{sorted(hm)} "
                            f"not subset of {sorted(h)}")
            ok = False

        # EstablishmentIsFinal: r in G => NO exit set separates
        # it, whatever HandlesMinus returns.  The caveat is about membership in
        # G, not about the computed set being empty: a non-empty value is no
        # more a price than an empty one is a licence.
        if r in model["G"]:
            findings.append(
                f"  [note] {r}: in G — establishment is final "
                f"(EstablishmentIsFinal), so "
                f"{sorted(hm) if hm else '{}'} is not a price at all")

    return ok, rows, findings


def report(model):
    print(f"=== {model['name']} ===")
    ok, rows, findings = check_model(model)
    print(f"  {'effect':<6} {'price':>5}  {'least exit':<22} "
          f"{'I(e)':>4}  {'sink':>5} {'in G':>5}")
    for (r, hm, h, sink, ing) in rows:
        print(f"  {r:<6} {len(hm):>5}  {str(sorted(hm)):<22} "
              f"{len(h):>4}  {str(sink):>5} {str(ing):>5}")
    for f in findings:
        print(f)
    print(f"  --> {'OK' if ok else 'DEFECT'}\n")
    return ok


# --------------------------------------------------------------------------
# Models.  Mirrors of the witness modules in ../specs/.
# --------------------------------------------------------------------------

def m_auditlog():
    """AuditLogWitness.tla -- g0 --Subject--> x --Chain--> r, a 2-step closure.
    prev[r] = x, prev[g0] = prev[x] = NoPrev ; lbl[r] = Bot (already erased)."""
    E = ["g0", "x", "r"]
    lbl = {"g0": "k", "x": "k", "r": BOT}
    prev = {"g0": "np", "x": "np", "r": "x"}
    return {
        "name": "AuditLogWitness",
        "E": E, "G": {"g0"}, "lbl": lbl,
        "surfaces": {
            # AuditRel("Chain", l) == {p : prev[p[2]] = p[1]}   (ignores l)
            "Chain": {"li": True, "rel": lambda l: {
                (a, b) for a, b in product(E, E) if prev[b] == a}},
            # AuditRel("Subject", l) == {p : l[p1] = l[p2] /\\ l[p1] # Bot}
            "Subject": {"li": False, "rel": lambda l: {
                (a, b) for a, b in product(E, E)
                if l[a] == l[b] and l[a] != BOT}},
        },
    }


def m_anonymity():
    """AnonymityWitness.tla -- multi-input spend join.
    r consumes BOTH x and y, so Graph gives r two distinct in-edges: a
    predecessor pointer cannot do that, and a cylinder cannot read p[1].
    The frontier reaches r as g0 --Pseud--> x --Graph--> r (y is unreachable),
    so this is also a 2-step closure crossing a label-dependent edge first.

    NB the earlier hand-mirror of this model had inputs = {x:{g0}, w:{g0},
    r:{x,w}} and was WRONG; certify.py caught it.  Values below are read from
    ../specs/AnonymityWitness.tla verbatim."""
    E = ["g0", "x", "y", "r"]
    lbl = {"g0": "k", "x": "k", "y": BOT, "r": BOT}
    inputs = {"g0": set(), "x": set(), "y": set(), "r": {"x", "y"}}
    return {
        "name": "AnonymityWitness",
        "E": E, "G": {"g0"}, "lbl": lbl,
        "surfaces": {
            # AnonRel("Graph", l) == {p : p[1] \\in inputs[p[2]]}   (ignores l)
            "Graph": {"li": True, "rel": lambda l: {
                (a, b) for a, b in product(E, E) if a in inputs[b]}},
            "Pseud": {"li": False, "rel": lambda l: {
                (a, b) for a, b in product(E, E)
                if l[a] == l[b] and l[a] != BOT}},
        },
    }


def m_strictprice():
    """StrictPriceWitness.tla -- g0 --P--> r, r --T--> z, z --Q--> r.
    Handles(r) = {P,Q} (I = 2) but the least exit set is {P}: Q's source z is
    reachable only through r, so it drops out of the r-deleted closure.
    Part of r's seal is procured by r.  r is not a sink -> outside
    FreshExactness."""
    E = ["g0", "r", "z"]
    lbl = {e: BOT for e in E}
    rels = {"P": {("g0", "r")}, "Q": {("z", "r")}, "T": {("r", "z")}}
    return {
        "name": "StrictPriceWitness",
        "E": E, "G": {"g0"}, "lbl": lbl,
        "surfaces": {n: {"li": True, "rel": (lambda s: (lambda l: s))(v)}
                     for n, v in rels.items()},
    }


def m_ta():
    """TAWitness.tla -- a --C--> a (root self-pin) and a --C--> b.
    Total accountability holds, bought with a self-certifying root."""
    E = ["a", "b"]
    lbl = {e: "k" for e in E}
    return {
        "name": "TAWitness",
        "E": E, "G": {"a"}, "lbl": lbl,
        "surfaces": {"C": {"li": True,
                           "rel": lambda l: {("a", "a"), ("a", "b")}}},
    }


MODELS = [m_auditlog, m_anonymity, m_strictprice, m_ta]


# --------------------------------------------------------------------------
# Proposition 1's O(|E| + sum_S |Rel(S)|) claim, measured.
# --------------------------------------------------------------------------

def scale(n):
    """A chained audit log of n entries: e0 <- e1 <- ... <- e(n-1)."""
    E = [f"e{i}" for i in range(n)]
    lbl = {e: BOT for e in E}
    chain = {(f"e{i}", f"e{i+1}") for i in range(n - 1)}
    return {
        "name": f"chain-{n}", "E": E, "G": {"e0"}, "lbl": lbl,
        "surfaces": {"Chain": {"li": True, "rel": lambda l: chain}},
    }


def run_scale():
    print("=== Proposition 1 scaling: least exit set of the newest entry ===")
    print(f"  {'n':>7} {'edges':>9} {'ms':>9} {'us/edge':>9}")
    for n in (100, 1000, 5000, 20000, 50000):
        m = scale(n)
        r = f"e{n-1}"
        t0 = time.perf_counter()
        hm = handles_minus(m, all_bot(m["E"]), r)
        dt = (time.perf_counter() - t0) * 1e3
        assert hm == {"Chain"}, hm
        print(f"  {n:>7} {n-1:>9} {dt:>9.1f} {dt*1e3/max(n,1):>9.2f}")
    print("  (least exit set = {'Chain'} at every size, as Audit_LeastExit says)\n")


if __name__ == "__main__":
    if "--scale" in sys.argv:
        run_scale()
    else:
        results = [report(f()) for f in MODELS]
        run_scale()
        print("ALL OK" if all(results) else "DEFECTS FOUND")
        sys.exit(0 if all(results) else 1)
