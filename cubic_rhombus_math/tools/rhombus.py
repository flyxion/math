"""
rhombus.py

Exact mathematics for the cubic rhombus family R_n(c).

Definition used throughout this corpus (the term is local to the corpus and is
not claimed to be standard): for n >= 2 and -1/(n-1) < c < 1, a cubic rhombus
R_n(c) is the parallelotope in R^n spanned by n unit vectors v_1..v_n with
<v_i, v_j> = c for all i != j.  c = 0 gives the unit cube, n = 2 gives a
rhombus, n = 3 gives a rhombohedron.  Its Gram matrix is

    G_n(c) = (1 - c) I + c J,        J = all-ones matrix.

Eight kinds of "contribution" (T1..T8) are attached to the family.  Each one is
a precise, true proposition.  For every (contribution, dimension) pair this
module computes the CONTENT of the proposition as a dictionary of exact
components.  Two pairs belong to the same class when their contents coincide,
or when the content of a specific dimension is obtained by substitution from
the general-n content (subsumption).  Nothing in this file is probabilistic.
"""

import sympy as sp

n = sp.Symbol("n", integer=True, positive=True)
c = sp.Symbol("c", real=True)
a = sp.Symbol("a", real=True)

CONTRIBUTIONS = ["T1", "T2", "T3", "T4", "T5", "T6", "T7", "T8"]

LABELS = {
    "T1": "Existence and Uniqueness",
    "T2": "A Sharp Inequality",
    "T3": "Extremal Characterization",
    "T4": "Local Stability",
    "T5": "Embedding Obstructions",
    "T6": "Boundary Rigidity",
    "T7": "Asymptotic Equidistribution",
    "T8": "A Counterexample",
}

FINITE_DIMS = [2, 3, 4, 5, 6]
DIM_LABELS = ["2", "3", "4", "5", "6", "n", "infinite"]


def gram(k):
    return (1 - c) * sp.eye(k) + c * sp.ones(k, k)


def det_closed(k):
    return (1 - c) ** (k - 1) * (1 + (k - 1) * c)


# --------------------------------------------------------------------------
# Content of each proposition, for a specific finite dimension k.
# Everything here is computed from the explicit k x k matrix.
# --------------------------------------------------------------------------

def _domain(G):
    lo, hi = -sp.oo, sp.oo
    for lam in G.eigenvals():
        sol = sp.solve_univariate_inequality(lam > 0, c, relational=False)
        lo = sp.Max(lo, sol.start)
        hi = sp.Min(hi, sol.end)
    return sp.nsimplify(lo), sp.nsimplify(hi)


def spec_content(t, k):
    G = gram(k)
    det = sp.factor(G.det())
    lo, hi = _domain(G)
    if t == "T1":
        return {"det": det, "pd_domain": (lo, hi)}
    if t in ("T2", "T3"):
        crit = [s for s in sp.solve(sp.diff(det, c), c) if lo < s < hi]
        vals = {s: det.subs(c, s) for s in crit}
        sup = max(vals.values())
        at = tuple(sorted(s for s in crit if vals[s] == sup))
        return {"sup": sup, "attained_at": at}
    if t == "T4":
        ser = sp.expand(sp.series(sp.log(sp.expand(G.det())), c, 0, 4).removeO())
        return {"F_c2": ser.coeff(c, 2), "F_c3": ser.coeff(c, 3)}
    if t == "T5":
        pts = [lo / 2, sp.Integer(0), hi / 2]
        interior = {G.subs(c, v).rank() for v in pts}
        if len(interior) != 1:
            raise ValueError("rank not constant on the interior sample")
        return {
            "rank_interior": sp.Integer(interior.pop()),
            "rank_lower_endpoint": sp.Integer(G.subs(c, lo).rank()),
            "rank_upper_endpoint": sp.Integer(G.subs(c, hi).rank()),
        }
    if t == "T6":
        F = G[: k - 1, : k - 1]
        member = sp.simplify(F - gram(k - 1)) == sp.zeros(k - 1, k - 1)
        return {
            "facet_gram_is_lower_dimensional_member": bool(member),
            "c_recoverable_from_boundary": bool(c in F.free_symbols),
        }
    if t == "T7":
        return {"finite_value": det.subs(c, a / k)}
    if t == "T8":
        counts = set()
        for j in range(1, 10):
            P = sp.Poly(sp.expand(det - sp.Rational(j, 10)), c)
            counts.add(P.count_roots(lo, hi))
        if len(counts) != 1:
            raise ValueError("fibre cardinality not constant")
        content = {"det_fibre_cardinality_on_(0,1)": sp.Integer(counts.pop())}
        if k == 2 and sp.simplify(det - det.subs(c, -c)) == 0:
            content["explicit_partner"] = -c
        return content
    raise KeyError(t)


# --------------------------------------------------------------------------
# Content for general n.  These are the closed forms proved in lib/lemmas.tex
# and in the contribution bodies.  verify.py checks each of them against
# spec_content for k = 2..8 and checks the symbolic ones for symbolic n.
# --------------------------------------------------------------------------

GENERIC = {
    "T1": {"det": (1 - c) ** (n - 1) * (1 + (n - 1) * c),
           "pd_domain": (-1 / (n - 1), sp.Integer(1))},
    "T2": {"sup": sp.Integer(1), "attained_at": (sp.Integer(0),)},
    "T3": {"sup": sp.Integer(1), "attained_at": (sp.Integer(0),)},
    "T4": {"F_c2": -n * (n - 1) / 2, "F_c3": n * (n - 1) * (n - 2) / 3},
    "T5": {"rank_interior": n, "rank_lower_endpoint": n - 1,
           "rank_upper_endpoint": sp.Integer(1)},
    "T6": {"facet_gram_is_lower_dimensional_member": True,
           "c_recoverable_from_boundary": sp.Ge(n, 3)},
    "T7": {"finite_value": (1 - a / n) ** (n - 1) * (1 + (n - 1) * a / n),
           "limit": (1 + a) * sp.exp(-a)},
    "T8": {"det_fibre_cardinality_on_(0,1)": sp.Integer(2)},
}

# Infinite dimension: the content is a statement about the limit n -> infinity
# of the finite family, or about unit vector systems indexed by N.
INFINITE = {
    "T1": {"unit_system_exists_iff": "0 <= c <= 1",
           "gram_operator_bounded_on_l2_iff": "c = 0"},
    "T2": {"limit_sup": sp.Integer(1), "limit_attained_at": (sp.Integer(0),)},
    "T3": {"limit_sup": sp.Integer(1), "limit_attained_at": (sp.Integer(0),)},
    "T4": {"F_c2_limit": sp.limit(GENERIC["T4"]["F_c2"], n, sp.oo)},
    "T5": {"min_ambient_dimension": "countably infinite"},
    "T6": {"c_recoverable_from_two_faces": True},
    "T7": {"limit": GENERIC["T7"]["limit"]},
    "T8": {"limit_volume_injective_in_c": False},
}


# --------------------------------------------------------------------------
# Comparison, substitution, canonical serialization
# --------------------------------------------------------------------------

def _eq(x, y):
    if isinstance(x, tuple) or isinstance(y, tuple):
        return (isinstance(x, tuple) and isinstance(y, tuple)
                and len(x) == len(y) and all(_eq(i, j) for i, j in zip(x, y)))
    if isinstance(x, str) or isinstance(y, str):
        return x == y
    sx, sy = sp.sympify(x), sp.sympify(y)
    if sx == sy:
        return True
    if isinstance(sx, sp.logic.boolalg.Boolean) and not isinstance(sx, sp.Expr):
        return False
    if isinstance(sy, sp.logic.boolalg.Boolean) and not isinstance(sy, sp.Expr):
        return False
    return sp.simplify(sx - sy) == 0


def _subs(x, k):
    if k is None or isinstance(x, (str, bool)):
        return x
    if isinstance(x, tuple):
        return tuple(_subs(i, k) for i in x)
    return sp.sympify(x).subs(n, k)


def subsumed(spec, gen, k):
    """Every component of spec equals the corresponding component of gen
    (after substituting n = k).  Components absent from gen are not subsumed."""
    for name, val in spec.items():
        if name not in gen or not _eq(val, _subs(gen[name], k)):
            return False
    return True


def _canon(x):
    if isinstance(x, tuple):
        return "(" + ",".join(_canon(i) for i in x) + ")"
    if isinstance(x, bool):
        return str(x)
    if isinstance(x, str):
        return repr(x)
    return sp.sstr(sp.simplify(sp.sympify(x)))


def canon_content(content):
    return "{" + "; ".join(f"{k}={_canon(content[k])}" for k in sorted(content)) + "}"


def build_classes():
    """Return (classes, index).  classes is an ordered list of dicts with keys
    id, scope, content, members.  index maps (contribution, dim label) to id."""
    classes, by_key, index = [], {}, {}

    def register(t, dim, content, scope):
        key = canon_content(content)
        if key not in by_key:
            rec = {"id": f"S{len(classes) + 1:02d}", "scope": scope,
                   "content": content, "members": []}
            classes.append(rec)
            by_key[key] = rec
        rec = by_key[key]
        rec["members"].append((t, dim))
        index[(t, dim)] = rec["id"]

    for t in CONTRIBUTIONS:
        register(t, "n", GENERIC[t], "general n")
    for k in FINITE_DIMS:
        for t in CONTRIBUTIONS:
            spec = spec_content(t, k)
            if subsumed(spec, GENERIC[t], k):
                register(t, str(k), GENERIC[t], "general n")
            else:
                register(t, str(k), spec, f"n = {k} only")
    for t in CONTRIBUTIONS:
        inf = INFINITE[t]
        if subsumed(inf, GENERIC[t], None):
            register(t, "infinite", GENERIC[t], "general n")
        else:
            register(t, "infinite", inf, "infinite dimension")
    return classes, index
