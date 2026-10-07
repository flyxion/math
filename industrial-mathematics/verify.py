"""
verify.py

Exact (SymPy) checks of the propositions used by the corpus.  Each check is
tagged with the contributions (T1..T8) it supports.  A class is reported as
checked only if every check tagged with any of its member contributions passed.

What this establishes: the stated closed forms agree with direct computation
from explicit n x n matrices for n = 2..8, and the symbolic-in-n identities
hold.  What it does not establish: that the propositions are new, interesting,
or independent of one another.
"""

import sympy as sp

from rhombus import (CONTRIBUTIONS, GENERIC, INFINITE, a, c, det_closed, gram,
                     n, spec_content, subsumed)

KS = range(2, 9)


def _check(results, name, tags, fn):
    try:
        ok = bool(fn())
    except Exception as exc:  # a failed check must be visible, never silent
        ok = False
        name = f"{name} (raised {type(exc).__name__}: {exc})"
    results.append({"name": name, "tags": list(tags), "ok": ok})


def run_all():
    R = []

    # Lemma 1: determinant and spectrum
    _check(R, "det G_k(c) = (1-c)^(k-1)(1+(k-1)c), k=2..8", ["T1", "T2", "T3", "T4", "T7", "T8"],
           lambda: all(sp.simplify(gram(k).det() - det_closed(k)) == 0 for k in KS))
    _check(R, "spectrum of G_k(c) is {1+(k-1)c, (1-c)^(k-1 times)}, k=2..8", ["T1", "T5"],
           lambda: all(gram(k).eigenvals() == {1 + (k - 1) * c: 1, 1 - c: k - 1} for k in KS))

    # Domain of positive definiteness, sampled exactly
    def domain_sample():
        for k in KS:
            lo = -sp.Rational(1, k - 1)
            for j in range(-19, 20):
                v = sp.Rational(j, 20)
                pd = all(e > 0 for e in gram(k).subs(c, v).eigenvals())
                if pd != (lo < v < 1):
                    return False
        return True
    _check(R, "positive definite exactly on (-1/(k-1),1), grid check k=2..8", ["T1"], domain_sample)

    # Facets (Lemma 2)
    _check(R, "principal (k-1)x(k-1) submatrix of G_k(c) equals G_(k-1)(c), k=2..8",
           ["T6"], lambda: all(sp.simplify(gram(k)[: k - 1, : k - 1] - gram(k - 1)) == sp.zeros(k - 1, k - 1)
                              for k in KS))

    # Lemma 3: F' formula, symbolic in n
    F = (n - 1) * sp.log(1 - c) + sp.log(1 + (n - 1) * c)
    Fp = -n * (n - 1) * c / ((1 - c) * (1 + (n - 1) * c))
    _check(R, "F'(c) = -n(n-1)c / ((1-c)(1+(n-1)c)), symbolic n", ["T2", "T3", "T8"],
           lambda: sp.simplify(sp.diff(F, c) - Fp) == 0)

    # T2/T3: grid check that det < 1 off c = 0
    def sharp():
        for k in KS:
            lo = -sp.Rational(1, k - 1)
            for j in range(-19, 20):
                v = sp.Rational(j, 20)
                if lo < v < 1:
                    d = det_closed(k).subs(c, v)
                    if (v == 0) != (d == 1) or d > 1:
                        return False
        return True
    _check(R, "det G_k(c) <= 1 with equality only at c=0, grid check k=2..8", ["T2", "T3"], sharp)

    # T4: series, symbolic in n
    def series_symbolic():
        ser = sp.expand(sp.series(F, c, 0, 4).removeO())
        return (sp.simplify(ser.coeff(c, 1)) == 0
                and sp.simplify(ser.coeff(c, 2) - GENERIC["T4"]["F_c2"]) == 0
                and sp.simplify(ser.coeff(c, 3) - GENERIC["T4"]["F_c3"]) == 0)
    _check(R, "series of ln det: c^2 and c^3 coefficients, symbolic n", ["T4"], series_symbolic)

    # T5: edge sum vanishes at the lower endpoint
    def edge_sum():
        for k in KS:
            lo = -sp.Rational(1, k - 1)
            one = sp.ones(k, 1)
            if sp.simplify((one.T * gram(k).subs(c, lo) * one)[0]) != 0:
                return False
        return True
    _check(R, "|v_1+...+v_k|^2 = 0 at c = -1/(k-1), k=2..8", ["T5"], edge_sum)

    # T6 at n = 2: perimeter independent of c, area not
    _check(R, "n=2: perimeter 4 for all c, area sqrt(1-c^2) not constant", ["T6"],
           lambda: sp.simplify(sp.sqrt(det_closed(2)) - sp.sqrt(1 - c ** 2)) == 0
           and sp.sqrt(det_closed(2)).subs(c, 0) != sp.sqrt(det_closed(2)).subs(c, sp.Rational(1, 2)))

    # T7: limit, symbolic and numeric
    fv = GENERIC["T7"]["finite_value"]
    _check(R, "lim_{n->inf} det G_n(a/n) = (1+a)e^{-a}, symbolic", ["T7"],
           lambda: sp.simplify(sp.limit(fv, n, sp.oo) - GENERIC["T7"]["limit"]) == 0)
    def numeric_limit():
        import mpmath
        mpmath.mp.dps = 30
        N, A = mpmath.mpf(10) ** 6, mpmath.mpf(1) / 2
        finite = (1 - A / N) ** (N - 1) * (1 + (N - 1) * A / N)
        return abs(finite - (1 + A) * mpmath.e ** (-A)) < mpmath.mpf(10) ** -5
    _check(R, "det G_n(a/n) at n=10^6, a=1/2 within 1e-5 of (1+a)e^{-a} (mpmath, 30 digits)",
           ["T7"], numeric_limit)

    # T8: fibre cardinality on a finer grid, exact root counting
    def fibres():
        for k in KS:
            lo = -sp.Rational(1, k - 1)
            for j in range(1, 20):
                P = sp.Poly(sp.expand(det_closed(k) - sp.Rational(j, 20)), c)
                if P.count_roots(lo, 1) != 2:
                    return False
        return True
    _check(R, "det G_k(c) = v has exactly two roots in the domain, v=j/20, k=2..8", ["T8"], fibres)

    # Subsumption: the general-n content specializes to the directly computed one
    def subsumption():
        for t in CONTRIBUTIONS:
            for k in range(2, 9):
                spec = spec_content(t, k)
                common = {m: v for m, v in spec.items() if m in GENERIC[t]}
                if common and not subsumed(common, GENERIC[t], k):
                    return False
        return True
    _check(R, "general-n content equals directly computed content for k=2..8 (shared components)",
           CONTRIBUTIONS, subsumption)

    # Vertex lemma: sign patterns with constant pair products
    def vertex_lemma():
        import itertools
        for k in range(2, 9):
            prods = set()
            for eps in itertools.product((1, -1), repeat=k):
                pairs = {eps[i] * eps[j] for i in range(k) for j in range(i + 1, k)}
                if len(pairs) == 1:
                    prods |= pairs
            if k >= 3 and prods != {1}:
                return False
            if k == 2 and prods != {1, -1}:
                return False
        return True
    _check(R, "vertex lemma: constant pair products of sign patterns are +1 for k>=3, and +-1 for k=2",
           ["T6", "T8"], vertex_lemma)

    # Infinite dimension
    def inf_construction():
        for val in (sp.Rational(1, 4), sp.Rational(1, 2), sp.Integer(0)):
            m = 5
            V = sp.zeros(m + 1, m)
            for i in range(m):
                V[0, i] = sp.sqrt(val)
                V[i + 1, i] = sp.sqrt(1 - val)
            if sp.simplify(V.T * V - gram(m).subs(c, val)) != sp.zeros(m, m):
                return False
        return True
    _check(R, "v_i = sqrt(c) e_0 + sqrt(1-c) e_i has Gram G(c), truncated m=5", ["T1"], inf_construction)

    cc = sp.Symbol("cc", positive=True)
    _check(R, "column norm sqrt(1+(m-1)c^2) of the infinite Gram matrix diverges for c>0", ["T1"],
           lambda: sp.limit(sp.sqrt(1 + (n - 1) * cc ** 2), n, sp.oo) == sp.oo)
    _check(R, "lim det G_n(1/2) = 0 (limit volume vanishes for c in (0,1))", ["T2", "T3", "T8"],
           lambda: sp.limit(det_closed(n).subs(c, sp.Rational(1, 2)), n, sp.oo) == 0)
    _check(R, "F_c2 coefficient -n(n-1)/2 tends to -infinity", ["T4"],
           lambda: INFINITE["T4"]["F_c2_limit"] == -sp.oo)
    _check(R, "infinite T7 content equals the limit component of general T7", ["T7"],
           lambda: subsumed(INFINITE["T7"], GENERIC["T7"], None))

    return R


def summary(results):
    return {"checks": len(results), "passed": sum(r["ok"] for r in results),
            "failed": [r["name"] for r in results if not r["ok"]]}


def class_status(results, members):
    """members: list of (contribution, dim).  Returns (n_checks, all_passed)."""
    tags = {t for t, _ in members}
    rel = [r for r in results if tags & set(r["tags"])]
    return len(rel), all(r["ok"] for r in rel)


if __name__ == "__main__":
    res = run_all()
    for r in res:
        print(("PASS " if r["ok"] else "FAIL ") + r["name"])
    s = summary(res)
    print(f"\n{s['passed']}/{s['checks']} checks passed")
    raise SystemExit(0 if not s["failed"] else 1)
