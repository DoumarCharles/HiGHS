#!/usr/bin/env python3
"""Exact (rational) check of the optimum of highs-tableau-cut-mre.lp.

Standard library only. Usage:
    python3 verify_optimum.py highs-tableau-cut-mre.lp witness.sol

It does three things, all in exact rational arithmetic:
  1. Checks that the witness satisfies every bound, integrality and every row
     of the LP, and computes its objective.
  2. Checks a Chvatal-Gomory lower-bound certificate: nonnegative multipliers
     on >= rows (any sign on equalities) whose sum leaves only c * (sum of a
     group of objective variables) on the left; the group sum is then at least
     ceil(rhs / c) because the variables are integer. The groups must
     partition the objective variables, each with objective coefficient 1.
  3. Reports optimal iff the bound equals the witness objective.

The witness file has one "name value" pair per line; other lines (HiGHS
solution-file headers, "#" comments) are ignored, and only the first value
section is read.
"""
import math
import re
import sys
from fractions import Fraction as Q


def parse_lp(path):
    text = open(path).read()
    sections = re.split(r"(?im)^\s*(minimize|subject to|bounds|general|end)\s*$", text)
    sec = {}
    for i in range(1, len(sections) - 1, 2):
        sec[sections[i].lower()] = sections[i + 1]
    term = re.compile(r"([+-])\s*(\d+(?:\.\d+)?)\s+([A-Za-z_][\w]*)")

    def linear(s):
        return {v: (Q(c) if sg == "+" else -Q(c)) for sg, c, v in term.findall(s)}

    obj_name, obj_expr = sec["minimize"].strip().split(":", 1)
    obj = linear(obj_expr)
    rows = {}
    for line in sec["subject to"].strip().splitlines():
        name, rest = line.split(":", 1)
        m = re.match(r"(.*?)(>=|<=|=)\s*(-?\d+(?:\.\d+)?)\s*$", rest)
        rows[name.strip()] = (linear(m.group(1)), m.group(2), Q(m.group(3)))
    bounds = {}
    for line in sec["bounds"].strip().splitlines():
        lo, v, hi = re.match(r"\s*(-?\d+)\s*<=\s*(\w+)\s*<=\s*(-?\d+)", line).groups()
        bounds[v] = (Q(lo), Q(hi))
    ints = set(sec["general"].split())
    return obj, rows, bounds, ints


def read_sol(path):
    sol = {}
    for line in open(path):
        parts = line.split()
        if len(parts) == 2 and re.match(r"^[A-Za-z_]\w*$", parts[0]):
            try:
                val = Q(parts[1])
            except ValueError:
                continue
            if parts[0] in sol:  # second section (e.g. duals) begins
                break
            sol[parts[0]] = val
    return sol


def check_witness(obj, rows, bounds, ints, sol):
    ok = True
    allvars = set(bounds) | {v for r in rows.values() for v in r[0]} | set(obj)
    for v in sorted(allvars):
        x = sol.get(v)
        if x is None:
            print(f"  MISSING value for {v}"); ok = False; continue
        lo, hi = bounds.get(v, (Q(0), None))
        if x < lo or (hi is not None and x > hi):
            print(f"  BOUND violated: {v} = {x} not in [{lo}, {hi}]"); ok = False
        if v in ints and x.denominator != 1:
            print(f"  INTEGRALITY violated: {v} = {x}"); ok = False
    for name, (lin, sense, rhs) in rows.items():
        lhs = sum(c * sol[v] for v, c in lin.items())
        good = {">=": lhs >= rhs, "<=": lhs <= rhs, "=": lhs == rhs}[sense]
        slack = lhs - rhs
        print(f"  {name:5s} lhs={lhs} {sense} {rhs}  slack={slack}  {'ok' if good else 'VIOLATED'}")
        ok &= good
    val = sum(c * sol[v] for v, c in obj.items())
    return ok, val


# Lower-bound certificate: group -> {row: multiplier}.
CERTIFICATE = {
    # 14 single-variable rows: c * p >= rhs  =>  p >= ceil(rhs / c)
    **{f"p_{k}": {f"r_{k}": Q(1)} for k in
       (0, 4, 6, 7, 11, 16, 21, 27, 28, 29, 30, 34, 42, 45)},
    # r_23 + r_24 + g_9:  10 (p_23 + p_24) >= 1810157 - 8
    "p_23+p_24": {"r_23": Q(1), "r_24": Q(1), "g_9": Q(1)},
    # r_9 + r_10 + r_44 + 3 g_16:  20 (p_9 + p_10 + p_44) >= 10029252 + 45
    "p_9+p_10+p_44": {"r_9": Q(1), "r_10": Q(1), "r_44": Q(1), "g_16": Q(3)},
}


def check_bound(obj, rows, ints):
    total = 0
    covered = []
    for group, mult in CERTIFICATE.items():
        lin, rhs = {}, Q(0)
        for r, m in mult.items():
            rl, sense, rr = rows[r]
            if sense == ">=":
                assert m >= 0, f"{r}: >= row needs nonnegative multiplier"
            elif sense == "<=":
                assert m <= 0, f"{r}: <= row needs nonpositive multiplier"
            for v, c in rl.items():
                lin[v] = lin.get(v, 0) + m * c
            rhs += m * rr
        lin = {v: c for v, c in lin.items() if c != 0}
        coefs = set(lin.values())
        assert len(coefs) == 1 and next(iter(coefs)) > 0, f"{group}: not c*sum(p): {lin}"
        c = next(iter(coefs))
        vars_ = sorted(lin)
        assert all(v in ints for v in vars_), f"{group}: non-integer variable"
        assert all(obj.get(v) == 1 for v in vars_), f"{group}: objective coef != 1"
        lb = math.ceil(rhs / c)
        print(f"  {group:15s} {c} * ({' + '.join(vars_)}) >= {rhs}  =>  sum >= {rhs / c} => {lb}")
        total += lb
        covered += vars_
    assert sorted(covered) == sorted(obj) and len(covered) == len(set(covered)), \
        "groups do not partition the objective variables"
    return total


def main():
    lp, solf = sys.argv[1], sys.argv[2]
    obj, rows, bounds, ints = parse_lp(lp)
    print(f"{lp}: {len(rows)} rows, {len(bounds)} columns, {len(ints)} integer, "
          f"{len(obj)} objective terms")
    print("Witness check:")
    ok, val = check_witness(obj, rows, bounds, ints, read_sol(solf))
    print(f"  witness feasible: {ok}; objective = {val}")
    print("Lower-bound certificate:")
    lb = check_bound(obj, rows, ints)
    singles = sum(math.ceil(rows[f"r_{k}"][2] / rows[f"r_{k}"][0][f"p_{k}"])
                  for k in (0, 4, 6, 7, 11, 16, 21, 27, 28, 29, 30, 34, 42, 45))
    print(f"  14 single-variable minima sum to {singles}")
    print(f"  lower bound = {lb}")
    if ok and lb == val:
        print(f"OPTIMAL VALUE = {val} (feasible witness attains the proven lower bound)")
        return 0
    print("NOT PROVEN")
    return 1


if __name__ == "__main__":
    sys.exit(main())
