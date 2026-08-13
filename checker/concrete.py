#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Phase 3 -- run the procedure in the four domains, on the REAL instances.

Phase 2 certified the checker against the *witness* modules.  Those modules
copy the abstract definitions in by hand and say so ("Faithfulness is by
syntactic identity"): a claim about a transcription.  This phase removes the
transcription.  Each concrete model here is a module that

    EXTENDS <Domain>Instance

and fixes that module's CONSTANTS in the .cfg.  Nothing is copied.  TLC
therefore evaluates HandlesMinus through the module's own `INSTANCE Synthesis`
wiring -- the same wiring the TLAPS proofs use -- so a passing invariant is
the deployed law confirming the tool, not a look-alike of it.

Two further things come free from EXTENDS:

  * the module's ASSUMEs are checked, so TLC certifies that each concrete
    model is a legal member of the class before it evaluates anything;
  * every constant is chosen to satisfy the hypotheses of that domain's
    `*_LeastExit` and `*_ZeroPrice` theorems, so the run also witnesses those
    hypotheses to be satisfiable -- the theorems are not vacuous.

Together the four models reproduce Table 2 of the paper (§7.4).

    python3 concrete.py            # generate, check, certify, print the table

Requires: java + tla2tools.jar (TLC_JAR), and TLAPS.tla (TLAPS_LIB), which the
instance modules EXTEND.
"""

import os
import subprocess
import sys
from itertools import product

import leastexit as L

HERE = os.path.dirname(os.path.abspath(__file__))
def _find_specs():
    """Locate specs/ by walking up from this file.

    The checker lives in the artifact (anc/checker/) but was developed beside
    the review notes; resolving the path by search rather than by a fixed
    number of "../" means the same file works from either place and cannot
    silently point at a stale copy.
    """
    d = os.path.dirname(os.path.abspath(__file__))
    for _ in range(6):
        cand = os.path.join(d, "specs", "Synthesis.tla")
        if os.path.exists(cand):
            return os.path.dirname(cand)
        cand = os.path.join(d, "anc", "specs", "Synthesis.tla")
        if os.path.exists(cand):
            return os.path.dirname(cand)
        d = os.path.dirname(d)
    raise SystemExit("cannot locate specs/ containing Synthesis.tla")


SPECS = _find_specs()
GEN = os.path.join(HERE, "gen3")
TLC_JAR = os.environ.get("TLC_JAR", os.path.expanduser("~/tools/tla2tools.jar"))
TLAPS_LIB = os.environ.get("TLAPS_LIB",
                           os.path.expanduser("~/tlaps/lib/tlaps"))

BOT = L.BOT


# --------------------------------------------------------------------------
# Helpers shared by the mirrors.  Each mirrors one shape of *Rel.
# --------------------------------------------------------------------------

def key_surface(E, mem=None):
    """The label-DEPENDENT surface of every instance:
         Rel(S,l) == {p \\in Mem \\X Mem : l[p1] = l[p2] /\\ l[p1] # Bot}
    Vanishes at AllBot -- that is the Dichotomy half the checker can test."""
    dom = E if mem is None else mem
    return lambda l: {(a, b) for a, b in product(dom, dom)
                      if l[a] == l[b] and l[a] != BOT}


def pointer_surface(E, ptr, nil, mem=None):
    """Chain / J1: adjacency by a predecessor POINTER (a function), so in-degree
    is at most one.  Ignores l."""
    dom = E if mem is None else mem
    return lambda l: {(a, b) for a, b in product(dom, dom)
                      if ptr[b] != nil and ptr[b] == a}


def set_surface(E, ins):
    """Graph: adjacency by SET-valued inputs, so in-degree is arbitrary.  This
    is the distinction D-4(b) bought; a pointer surface cannot express it."""
    return lambda l: {(a, b) for a, b in product(E, E) if a in ins[b]}


# --------------------------------------------------------------------------
# The four concrete models.  `tla` fixes the module's CONSTANTS; `py` is the
# independent implementation's view of the same model.  They are written next
# to each other on purpose: any divergence is what TLC is here to catch.
# --------------------------------------------------------------------------

def c_deniability():
    E = ["g", "m", "u"]
    signed = {"g": True, "m": True, "u": False}
    author = {"g": "k", "m": "k", "u": BOT}
    return {
        "name": "Deniability", "module": "DeniabilityInstance", "inst": "D",
        "adjudicator": "third party (judge)",
        # Den_LeastExit: m is signed and unattributed  -> {"Sig"}
        # Den_ZeroPrice: u is unsigned                 -> {}
        "priced": "m", "free": "u",
        "thm": "Den_LeastExit / Den_ZeroPrice",
        "hyps": ('/\\ "m" \\in Msgs /\\ "m" \\notin Attributed /\\ signed["m"]\n                  /\\ ~signed["u"]'),
        "expect": {"m": {"Sig"}, "u": set()},
        "cfg": [
            'Msgs = {"g", "m", "u"}',
            'Authors = {"k"}',
            f'NoAuth = "{BOT}"',
            'Attributed = {"g"}',
            "author <- author_c",
            "signed <- signed_c",
        ],
        "defs": (
            'author_c == [x \\in Msgs |-> IF x = "u" THEN NoAuth ELSE "k"]\n'
            'signed_c == [x \\in Msgs |-> x \\in {"g", "m"}]'
        ),
        "py": {
            "name": "Deniability (concrete)", "E": E, "G": {"g"}, "lbl": author,
            "surfaces": {
                # DenRel("Sig", l) == {p : signed[p[2]]}  -- a CYLINDER: it
                # never reads p[1].  The one that survives; §8 says so.
                "Sig": {"li": True, "rel": lambda l: {
                    (a, b) for a, b in product(E, E) if signed[b]}},
                "Mac": {"li": False, "rel": key_surface(E)},
            },
        },
    }


def c_anonymity():
    E = ["g", "t", "u"]
    inputs = {"g": set(), "t": {"g"}, "u": set()}
    ident = {"g": "k", "t": "k", "u": BOT}
    return {
        "name": "Unlinkability", "module": "AnonymityInstance", "inst": "A",
        "adjudicator": "de-anonymising analyst",
        # Anon_LeastExit: t consumes the deanonymised g  -> {"Graph"}
        # Anon_ZeroPrice: u consumes nothing             -> {}
        "priced": "t", "free": "u",
        "thm": "Anon_LeastExit / Anon_ZeroPrice",
        "hyps": ('/\\ "g" \\in Deanon /\\ "t" \\in Txs /\\ "t" \\notin Deanon\n                  /\\ "g" \\in inputs["t"] /\\ inputs["u"] = {}'),
        "expect": {"t": {"Graph"}, "u": set()},
        "cfg": [
            'Txs = {"g", "t", "u"}',
            'Idents = {"k"}',
            f'NoId = "{BOT}"',
            'Deanon = {"g"}',
            "ident <- ident_c",
            "inputs <- inputs_c",
        ],
        "defs": (
            'ident_c  == [x \\in Txs |-> IF x = "u" THEN NoId ELSE "k"]\n'
            'inputs_c == [x \\in Txs |-> IF x = "t" THEN {"g"} ELSE {}]'
        ),
        "py": {
            "name": "Unlinkability (concrete)", "E": E, "G": {"g"}, "lbl": ident,
            "surfaces": {
                "Graph": {"li": True, "rel": set_surface(E, inputs)},
                "Pseud": {"li": False, "rel": key_surface(E)},
            },
        },
    }


def c_auditlog():
    E = ["g0", "r", "u"]
    prev = {"g0": "np", "r": "g0", "u": "np"}
    subj = {"g0": "k", "r": "k", "u": BOT}
    return {
        "name": "RTBF", "module": "AuditLogInstance", "inst": "A",
        "adjudicator": "chain verifier",
        # Audit_LeastExit: prev[r] is a logged entry  -> {"Chain"}
        # Audit_ZeroPrice: u has no prev              -> {}
        "priced": "r", "free": "u",
        "thm": "Audit_LeastExit / Audit_ZeroPrice",
        "hyps": ('/\\ "g0" \\in Logged /\\ "r" \\in Entries /\\ prev["r"] = "g0"\n                  /\\ prev["u"] = NoPrev'),
        "expect": {"r": {"Chain"}, "u": set()},
        "cfg": [
            'Entries = {"g0", "r", "u"}',
            'Subjects = {"k"}',
            f'NoSubj = "{BOT}"',
            'NoPrev = "np"',
            'Logged = {"g0"}',
            "subj <- subj_c",
            "prev <- prev_c",
        ],
        "defs": (
            'subj_c == [e \\in Entries |-> IF e = "u" THEN NoSubj ELSE "k"]\n'
            'prev_c == [e \\in Entries |-> IF e = "r" THEN "g0" ELSE NoPrev]'
        ),
        "py": {
            "name": "RTBF (concrete)", "E": E, "G": {"g0"}, "lbl": subj,
            "surfaces": {
                "Chain": {"li": True, "rel": pointer_surface(E, prev, "np")},
                "Subject": {"li": False, "rel": key_surface(E)},
            },
        },
    }


def c_sepclosure():
    # Machine = "ACCT": the reflex is ON the sealing pipeline, and its corr key
    # is stripped -- which is exactly the case where stripping does not help.
    E = ["a", "r", "u"]
    emitted, actions = {"a", "r"}, {"a"}
    prevEv = {"a": "np", "r": "a", "u": "np"}
    lbl = {"a": "c1", "r": BOT, "u": BOT}          # CorrAssign under ACCT
    pipe = {e for e in E if e in emitted}          # ACCT: all emitted are on it
    return {
        "name": "Action gov.", "module": "SepClosureInstance", "inst": "N",
        "adjudicator": "auditor of the record",
        # Morph_LeastExit: the emitted reflex chained to the action -> {J1,J2}
        # Morph_ZeroPrice: u is not emitted (pre-action)            -> {}
        "priced": "r", "free": "u",
        "thm": "Morph_LeastExit / Morph_ZeroPrice",
        "hyps": ('/\\ Machine = "ACCT" /\\ EnableByPosition /\\ EnableByTime\n                  /\\ "a" \\in Actions /\\ "r" \\in Reflexes\n                  /\\ "a" \\in Emitted /\\ "r" \\in Emitted /\\ prevEv["r"] = "a"\n                  /\\ ~PipeS("u")'),
        "expect": {"r": {"J1", "J2"}, "u": set()},
        "cfg": [
            'CorrIDs = {"c1"}',
            f'NONE = "{BOT}"',
            'Actions = {"a"}',
            'Reflexes = {"r", "u"}',
            'Machine = "ACCT"',
            "EnableByTime = TRUE",
            "EnableByPosition = TRUE",
            'Emitted = {"a", "r"}',
            'NoPrev = "np"',
            "prevEv <- prevEv_c",
        ],
        "defs": (
            'prevEv_c == [e \\in EventIds |-> IF e = "r" THEN "a" ELSE NoPrev]'
        ),
        # SepClosureTwoMachines already declares VARIABLES; reuse them.
        "vars": ("<<emitted, linked>>", "emitted = {} /\\ linked = {}"),
        "py": {
            "name": "Action gov. (concrete)", "E": E,
            "G": sorted(emitted & actions), "lbl": lbl,
            "surfaces": {
                # J2: co-presence on the pipeline -- the full square, so its
                # in-degree is arbitrary but for a different reason than Graph.
                "J2": {"li": True, "rel": lambda l: {
                    (a, b) for a, b in product(pipe, pipe)}},
                "J1": {"li": True,
                       "rel": pointer_surface(E, prevEv, "np", mem=pipe)},
                "J4": {"li": False, "rel": key_surface(E)},
            },
        },
    }


MODELS = [c_deniability, c_anonymity, c_auditlog, c_sepclosure]


# --------------------------------------------------------------------------
# Generation.
# --------------------------------------------------------------------------

def tla_set(items):
    return "{}" if not items else "{" + ", ".join(
        f'"{i}"' for i in sorted(items)) + "}"


def build(spec):
    m, inst, py = spec["module"], spec["inst"], spec["py"]
    name = spec["module"].replace("Instance", "") + "Concrete"
    ab = L.all_bot(py["E"])

    # The hypotheses of this domain's *_LeastExit / *_ZeroPrice theorems, as
    # the theorems state them.  Asserting them here is what makes the run a
    # non-vacuity witness: TLAPS proves the theorem for all models satisfying
    # these, and TLC confirms this model does.  The conclusion below must then
    # agree with the theorem's right-hand side -- if it did not, the artifact
    # would contradict itself, which is precisely what we want checkable.
    claims = [f"  \\* hypotheses of {spec['thm']}", f"  {spec['hyps']}",
              "  \\* the procedure's output on this model",
              f'  /\\ {inst}!Reach = {tla_set(L.reach(py, py["lbl"]))}']
    for e in sorted(py["E"]):
        claims.append(f'  /\\ {inst}!HandlesMinus({inst}!AllBot, "{e}") = '
                      f'{tla_set(L.handles_minus(py, ab, e))}')
        claims.append(f'  /\\ {inst}!Handles("{e}") = '
                      f'{tla_set(L.handles(py, e))}')

    # Corollary 4, live.  For a frontier effect the procedure still returns a
    # set, and that set is not a price: nothing separates it.  Asserting
    # ~Sep(e) alongside the returned value makes each frontier row a certified
    # counterexample to reading HandlesMinus without the r \notin G guard --
    # the guard Theorem 5 carries and a reader may drop.
    for e in sorted(py["G"]):
        claims.append(f'  /\\ ~{inst}!Sep("{e}")')

    if "vars" in spec:
        vdecl, vinit = "", spec["vars"][1]
        vtuple = spec["vars"][0]
    else:
        vdecl, vinit, vtuple = "VARIABLE tick\n", "tick = 0", "tick"

    tla = f"""---- MODULE {name} ----
(***************************************************************************)
(* GENERATED by checker/concrete.py -- do not edit by hand.                 *)
(*                                                                         *)
(* A concrete finite member of the {m:<24}                *)
(* class.  This module EXTENDS that instance and fixes its CONSTANTS in the *)
(* .cfg; it copies NO definition.  TLC therefore evaluates the claims below *)
(* through the instance's own INSTANCE Synthesis wiring -- the same wiring  *)
(* the TLAPS proofs use.                                                   *)
(*                                                                         *)
(* Each claim is a value computed by ../leastexit.py, an independent        *)
(* implementation of Proposition 1's procedure.  The constants also satisfy *)
(* the hypotheses of this domain's *_LeastExit and *_ZeroPrice theorems, so *)
(* the run witnesses those hypotheses to be satisfiable.                   *)
(***************************************************************************)
EXTENDS {m}

{spec["defs"]}

{vdecl}CInit == {vinit}
CNext == UNCHANGED {vtuple}
CSpec == CInit /\\ [][CNext]_{vtuple}

CheckerOutput ==
{chr(10).join(claims)}

====
"""
    cfg = ("SPECIFICATION CSpec\nCONSTANTS\n  "
           + "\n  ".join(spec["cfg"])
           + "\nINVARIANT CheckerOutput\n")
    return name, tla, cfg


def run_tlc(name):
    # -metadir per run: see certify.py -- sub-second runs collide otherwise.
    cmd = ["java", f"-DTLA-Library={TLAPS_LIB}", "-cp", TLC_JAR, "tlc2.TLC",
           "-metadir", os.path.join("states", name),
           "-config", f"{name}.cfg", f"{name}.tla"]
    p = subprocess.run(cmd, cwd=GEN, capture_output=True, text=True)
    out = p.stdout + p.stderr
    if "No error has been found" in out:
        return True, "No error has been found."
    for line in out.splitlines():
        if line.startswith("Error") or "is equal to FALSE" in line \
                or "is violated" in line or "is not a module" in line \
                or "Assumption" in line:
            return False, line.strip()
    return False, (out.strip().splitlines()[-1] if out.strip() else "no output")


def main():
    os.makedirs(GEN, exist_ok=True)
    # Symlink, never copy: a copy could drift from the module it certifies.
    for f in os.listdir(SPECS):
        if f.endswith(".tla"):
            dst = os.path.join(GEN, f)
            if os.path.islink(dst) or os.path.exists(dst):
                os.remove(dst)
            os.symlink(os.path.join(SPECS, f), dst)

    # Relative / basename only -- see certify.py.
    print(f"specs : {os.path.relpath(SPECS, HERE)}")
    print(f"jar   : {os.path.basename(TLC_JAR)}")
    print(f"tlaps : {os.path.basename(TLAPS_LIB)}\n")

    rows, ok_all = [], True
    for factory in MODELS:
        spec = factory()
        py = spec["py"]

        # (1) the independent implementation runs the procedure
        ok, _, findings = L.check_model(py)
        ab = L.all_bot(py["E"])
        got = {e: L.handles_minus(py, ab, e) for e in py["E"]}

        # (2) it must agree with the *_LeastExit / *_ZeroPrice theorem it
        #     instantiates -- this is the paper's table, checked
        agree = all(got[e] == v for e, v in spec["expect"].items())
        if not agree or not ok:
            ok_all = False

        # (3) and the specification must certify it
        name, tla, cfg = build(spec)
        with open(os.path.join(GEN, name + ".tla"), "w") as f:
            f.write(tla)
        with open(os.path.join(GEN, name + ".cfg"), "w") as f:
            f.write(cfg)
        tlc_ok, msg = run_tlc(name)
        if not tlc_ok:
            ok_all = False

        rows.append((spec, got, agree, ok, tlc_ok, msg, findings))
        print(f"  {name:<24} checker {'ok ' if ok and agree else 'BAD'}  "
              f"TLC {'PASS' if tlc_ok else 'FAIL'}  {msg}")

    print("\n" + "=" * 78)
    print("Table 2 (§7.4), reproduced as tool output")
    print("=" * 78)
    print(f"{'Instance':<14}{'Adjudicator':<26}{'least exit':<20}{'price':>6}")
    print("-" * 78)
    for (spec, got, *_rest) in rows:
        p, f_ = spec["priced"], spec["free"]
        print(f"{spec['name']:<14}{spec['adjudicator']:<26}"
              f"{str(sorted(got[p])):<20}{len(got[p]):>6}")
        print(f"{'':<14}{'(pre-/unlinked case)':<26}"
              f"{str(sorted(got[f_])):<20}{len(got[f_]):>6}")
    print("-" * 78)

    for (spec, _g, _a, _o, _t, _m, findings) in rows:
        for line in findings:
            print(f"  {spec['name']}: {line.strip()}")

    print()
    if ok_all:
        print("ALL FOUR DOMAINS CERTIFIED — each row of Table 2 is now a "
              "theorem AND a tool output,\nconfirmed by TLC against the "
              "instance module itself (no transcription).")
    else:
        print("MISMATCH — see above.  A disagreement here is a finding: "
              "either the checker,\nthe concrete model, or the paper's row "
              "is wrong.")
    return 0 if ok_all else 1


if __name__ == "__main__":
    sys.exit(main())
