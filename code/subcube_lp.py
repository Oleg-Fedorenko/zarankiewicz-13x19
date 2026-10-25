# Afrasyab's block-polytope relaxation (arXiv:2608.08154, Sec. 5) taken one step further: not with one column fixed,
# but with the columns 0..k of a sub-cube fixed (subcubes.py). The rows fall into groups with equal entries in the
# fixed columns; a remaining column is described by its type, the number of its ones in each group. For any matrix of
# the sub-cube, y[d, type] = the number of remaining columns of degree d and that type satisfies, exactly:
#   - for each degree class d and each value v: the columns of class d with v ones in the anchor's rows number as the
#     pattern says (minus the fixed columns of that class);
#   - for each orbit of row triples (a multiset of groups): sum over types of y * prod_g C(k_g, t_g) <= (2 - the number
#     of fixed columns containing such a triple) * prod_g C(n_g, t_g) — the triple capacity summed over the orbit;
#   - for each group g: the ones in its rows, from the fixed and the remaining columns, are at least cut1 * n_g.
# So if this linear system has no nonnegative real solution, the sub-cube holds no matrix; a Farkas vector (found in
# floating point by HiGHS, then made rational) is checked here in exact arithmetic and is the certificate.
#   .venv-lp/bin/python subcube_lp.py <m> <n> <T> <cut1> <profile json> <pattern json> <supports json>
import itertools, json, math, sys
from collections import Counter
from fractions import Fraction

def build(m, n, T, cut1, profile, pattern, supports):
    c = profile[0]; fixed = [tuple(range(c))] + [tuple(s) for s in supports]; k = len(supports)
    member = {r: tuple(1 if r in S else 0 for S in fixed) for r in range(m)}
    groups = sorted(set(member.values()), reverse=True)
    size = {g: sum(1 for r in range(m) if member[r] == g) for g in groups}
    left = {d: Counter(pattern[d]) for d in pattern}
    for j, S in enumerate(fixed[1:], start=1):
        left[profile[j]][sum(1 for r in S if r < c)] -= 1
    assert all(v >= 0 for d in left for v in left[d].values()), "fixed columns not in the pattern"
    classes = Counter(profile[k + 1:])
    var = []                                                       # (d, type) with type = counts per group
    for d in classes:
        for ks in itertools.product(*[range(size[g] + 1) for g in groups]):
            if sum(ks) == d: var.append((d, ks))
    A, b, names = [], [], []                                       # rows of A x <= b
    for orb in itertools.combinations_with_replacement(range(len(groups)), 3):
        t = Counter(orb)
        if any(t[i] > size[groups[i]] for i in t): continue
        cover = sum(1 for col in range(len(fixed)) if all(groups[i][col] for i in t))
        A.append([math.prod(math.comb(ks[i], t[i]) for i in t) for d, ks in var])
        b.append((2 - cover) * math.prod(math.comb(size[groups[i]], t[i]) for i in t)); names.append(("triple", orb))
    for i, g in enumerate(groups):                                # -(ones in group g) <= -(cut1 * n_g)
        A.append([-ks[i] for d, ks in var]); b.append(sum(g) * size[g] - cut1 * size[g]); names.append(("group", g))
    E, e = [], []                                                  # rows of E x = e
    for d in classes:
        values = {sum(ks[i] for i, g in enumerate(groups) if g[0]) for dd, ks in var if dd == d}
        for v in sorted(values | set(left[d])):
            E.append([1 if dd == d and sum(ks[i] for i, g in enumerate(groups) if g[0]) == v else 0 for dd, ks in var])
            e.append(left[d][v])
    return var, A, b, names, E, e, groups, size

def solve(var, A, b, E, e):
    import highspy, numpy as np
    h = highspy.Highs(); h.setOptionValue("output_flag", False)
    nv = len(var); inf = highspy.kHighsInf
    lp = highspy.HighsLp(); lp.num_col_ = nv; lp.num_row_ = len(A) + len(E)
    lp.col_cost_ = np.zeros(nv); lp.col_lower_ = np.zeros(nv); lp.col_upper_ = np.full(nv, inf)
    lp.row_lower_ = np.array([-inf] * len(A) + list(map(float, e))); lp.row_upper_ = np.array(list(map(float, b)) + list(map(float, e)))
    M = np.array(A + E, dtype=float); starts, idx, vals = [0], [], []
    for jcol in range(nv):
        nz = np.nonzero(M[:, jcol])[0]; idx += list(nz); vals += list(M[nz, jcol]); starts.append(len(idx))
    lp.a_matrix_.format_ = highspy.MatrixFormat.kColwise; lp.a_matrix_.start_ = starts; lp.a_matrix_.index_ = idx; lp.a_matrix_.value_ = vals
    h.passModel(lp); h.run()
    status = h.modelStatusToString(h.getModelStatus())
    ray = None
    if "nfeasible" in status:
        res = h.getDualRay()                                       # (has, values) or (status, has, values)
        has, r = res[-2], res[-1]
        if has: ray = list(r)
    return status, ray

def _integer(vals):
    """Rationals -> (integers, common denominator)."""
    den = 1
    for v in vals: den = den * v.denominator // math.gcd(den, v.denominator)
    return [int(v * den) for v in vals], den

def _sums(A, b, E, e, al, be):
    """Column sums of A^T alpha + E^T beta and b.alpha + e.beta, in integers (alpha, beta scaled by one denominator)."""
    nza = [i for i, v in enumerate(al) if v]; nzb = [i for i, v in enumerate(be) if v]
    ints, den = _integer([al[i] for i in nza] + [be[i] for i in nzb])
    ia = dict(zip(nza, ints[:len(nza)])); ib = dict(zip(nzb, ints[len(nza):]))
    nv = len(A[0]) if A else len(E[0])
    col = [sum(ia[i] * A[i][j] for i in nza) + sum(ib[i] * E[i][j] for i in nzb) for j in range(nv)]
    rhs = sum(ia[i] * b[i] for i in nza) + sum(ib[i] * e[i] for i in nzb)
    return col, rhs

def check_farkas(A, b, E, e, ray, names=None, scale=10**9):
    """Exact check: alpha (for A x <= b, must be >= 0) and beta (for E x = e, free) with A^T alpha + E^T beta >= 0
    componentwise and b.alpha + e.beta < 0. The solver's vector is made rational first by continued fractions (a vertex
    has small denominators), then, if that fails, by rounding with a repair: the triple rows are added with a common
    weight t (each column of degree d has C(d,3) > 0 triples, so every column sum rises) while the right-hand side stays
    negative. All checks are in integers after one common denominator. Returns the exact vector."""
    na, ne, nv = len(A), len(E), len(A[0])
    triple = [i for i in range(na) if names is None or names[i][0] == "triple"]
    for sgn in (1, -1):
        for mode in ("cf", "round"):
            if mode == "cf":
                al = [max(Fraction(sgn * v).limit_denominator(10**6), Fraction(0)) for v in ray[:na]]
                be = [Fraction(sgn * v).limit_denominator(10**6) for v in ray[na:]]
            else:
                al = [max(Fraction(round(sgn * v * scale), scale), Fraction(0)) for v in ray[:na]]
                be = [Fraction(round(sgn * v * scale), scale) for v in ray[na:]]
            if not any(al) and not any(be): continue
            col, rhs = _sums(A, b, E, e, al, be)
            if min(col) < 0 and mode == "round":
                _, den = _integer([v for v in al + be if v])
                w = [sum(A[i][j] for i in triple) for j in range(nv)]
                if min(w) <= 0: continue
                t = max(Fraction(-col[j], den * w[j]) for j in range(nv) if col[j] < 0)
                ts = set(triple); al = [a + t if i in ts else a for i, a in enumerate(al)]
                col, rhs = _sums(A, b, E, e, al, be)
            if min(col) >= 0 and rhs < 0:
                return True, {"alpha": [str(v) for v in al], "beta": [str(v) for v in be], "value": str(Fraction(rhs, _integer([v for v in al + be if v])[1]))}
    return False, None

def verify(A, b, E, e, cert):
    """Independent exact check of a stored certificate."""
    al = [Fraction(v) for v in cert["alpha"]]; be = [Fraction(v) for v in cert["beta"]]
    if any(v < 0 for v in al) or len(al) != len(A) or len(be) != len(E): return False
    for j in range(len(A[0])):
        if sum(al[i] * A[i][j] for i in range(len(A)) if A[i][j]) + sum(be[i] * E[i][j] for i in range(len(E)) if E[i][j]) < 0: return False
    return sum(al[i] * b[i] for i in range(len(A))) + sum(be[i] * e[i] for i in range(len(E))) < 0

def row_floor(m, n, T, profile, upper):
    """The least number of ones of any row: T - z(m-1, n) (deleting the row), and, from deleting the row and a column
    j together, T - z(m-1, n-1) - c_j for every column (the (1,1) mixed cut of satlean.mixed_cut_clauses)."""
    a = upper(m - 1, n); b = upper(m - 1, n - 1)
    return max([T - a] + ([T - b - c for c in profile] if b is not None else []))

def sparse_ray(A, b, E, e):
    """A Farkas vector with few nonzeros: min sum(alpha) + sum(|beta|) subject to A^T alpha + E^T beta >= 0 and
    b.alpha + e.beta = -1 (a vertex of this LP has at most as many nonzeros as there are variables of the system)."""
    import highspy, numpy as np
    na, ne, nv = len(A), len(E), len(A[0]); nx = na + 2 * ne
    h = highspy.Highs(); h.setOptionValue("output_flag", False); inf = highspy.kHighsInf
    lp = highspy.HighsLp(); lp.num_col_ = nx; lp.num_row_ = nv + 1
    lp.col_cost_ = np.ones(nx); lp.col_lower_ = np.zeros(nx); lp.col_upper_ = np.full(nx, inf)
    lp.row_lower_ = np.array([0.0] * nv + [-1.0]); lp.row_upper_ = np.array([inf] * nv + [-1.0])
    st, ix, va = [0], [], []
    for i in range(na):
        for j in range(nv):
            if A[i][j]: ix.append(j); va.append(float(A[i][j]))
        ix.append(nv); va.append(float(b[i])); st.append(len(ix))
    for sgn in (1, -1):
        for i in range(ne):
            for j in range(nv):
                if E[i][j]: ix.append(j); va.append(float(sgn * E[i][j]))
            ix.append(nv); va.append(float(sgn * e[i])); st.append(len(ix))
    lp.a_matrix_.format_ = highspy.MatrixFormat.kColwise; lp.a_matrix_.start_ = st; lp.a_matrix_.index_ = ix; lp.a_matrix_.value_ = va
    h.passModel(lp); h.run()
    if h.modelStatusToString(h.getModelStatus()) != "Optimal": return None
    x = list(h.getSolution().col_value)
    return x[:na] + [x[na + i] - x[na + ne + i] for i in range(ne)]

def to_sparse(cert):
    return {"alpha": {str(i): v for i, v in enumerate(cert["alpha"]) if v != "0"},
            "beta": {str(i): v for i, v in enumerate(cert["beta"]) if v != "0"}}

def verify_sparse(A, b, E, e, sp):
    """Exact check of a sparse certificate {"alpha": {row: "p/q"}, "beta": {row: "p/q"}} (rows by position), in
    integers after one common denominator."""
    al = {int(i): Fraction(v) for i, v in sp["alpha"].items()}; be = {int(i): Fraction(v) for i, v in sp["beta"].items()}
    if any(v < 0 for v in al.values()) or any(not 0 <= i < len(A) for i in al) or any(not 0 <= i < len(E) for i in be): return False
    ints, den = _integer(list(al.values()) + list(be.values()))
    ia = dict(zip(al, ints[:len(al)])); ib = dict(zip(be, ints[len(al):]))
    for j in range(len(A[0])):
        if sum(a * A[i][j] for i, a in ia.items()) + sum(x * E[i][j] for i, x in ib.items()) < 0: return False
    return sum(a * b[i] for i, a in ia.items()) + sum(x * e[i] for i, x in ib.items()) < 0

def refute(m, n, T, cut1, profile, pattern, supports):
    """The sub-cube's LP; (True, sparse certificate, meta) when it is infeasible and a Farkas vector checks exactly.
    The sparse vector (min L1) is tried first, the solver's ray second."""
    var, A, b, names, E, e, groups, size = build(m, n, T, cut1, profile, pattern, supports)
    status, ray = solve(var, A, b, E, e)
    meta = {"lp status": status, "variables": len(var), "inequalities": len(A), "equations": len(E), "cut1": cut1}
    if ray is None: return False, None, meta
    for vec in (sparse_ray(A, b, E, e), ray):
        if vec is None: continue
        ok, cert = check_farkas(A, b, E, e, vec, names)
        if ok:
            sp = to_sparse(cert)
            if verify_sparse(A, b, E, e, sp): return True, sp, meta
    return False, None, meta

if __name__ == "__main__":
    m, n, T, cut1 = map(int, sys.argv[1:5]); profile = tuple(json.loads(sys.argv[5]))
    pattern = {int(d): tuple(ms) for d, ms in json.loads(sys.argv[6]).items()}; supports = json.loads(sys.argv[7])
    var, A, b, names, E, e, groups, size = build(m, n, T, cut1, profile, pattern, supports)
    status, ray = solve(var, A, b, E, e)
    out = {"groups": {"".join(map(str, g)): size[g] for g in groups}, "variables": len(var), "inequalities": len(A), "equations": len(E), "status": status}
    if ray is not None:
        ok, cert = check_farkas(A, b, E, e, ray); out["exact Farkas check"] = ok
    print(json.dumps(out))
