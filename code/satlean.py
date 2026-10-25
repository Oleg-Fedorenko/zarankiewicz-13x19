# The column-profile case formula of satprofile, with the row cuts encoded lean (suggested by the Fable brainstorm of
# 2026-10-19): instead of one cardinality constraint per k-subset of rows (78 + 286 sequential counters for k = 2, 3 —
# about 93% of the variables), each row gets a totalizer over its negated cells, whose output u_i[t] means "row i has at
# least t+1 zeros", i.e. "row i has at most n-1-t ones". The cuts "every k rows hold at least cut_k ones" (cut_k =
# T - z(m-k, n)) then become: row i is not below cut_1 (a unit), and for k >= 2 no k rows take degrees p_1..p_k with
# p_1 + ... + p_k = cut_k - 1 at the most (each p >= cut_1; tuples a smaller cut already forbids are skipped) — one
# clause per k-subset and per such tuple. Same K3,3 encoding, same column degrees, same symmetry breaking (rows lex,
# equal-degree columns lex) as satprofile.case_formula, so every matrix of the case satisfies it exactly when it
# satisfies that one.
import itertools
from pysat.card import CardEnc, EncType, ITotalizer
from pysat.formula import IDPool
from satclass import lex_geq
import satprofile

def cut_tuples(cuts, k):
    """Non-decreasing k-tuples of row degrees (each >= cuts[1]) summing to cuts[k] - 1 that no smaller cut forbids."""
    lo = cuts.get(1, 0); out = []
    def ok(t):
        for j in range(2, k):
            if j in cuts and sum(sorted(t)[:j]) < cuts[j]: return False   # a smaller cut already excludes it
        return True
    def rec(prefix, left, slots):
        if slots == 0:
            if left == 0 and ok(prefix): out.append(tuple(prefix))
            return
        start = prefix[-1] if prefix else lo
        for d in range(start, left + 1):
            if d * slots > left: break
            rec(prefix + [d], left - d, slots - 1)
    if k in cuts: rec([], cuts[k] - 1, k)
    return out

def mixed_cut_clauses(m, n, T, profile, cuts, v, at_most):
    """Deleting a rows and b columns leaves an (m-a) x (n-b) matrix, so the a rows' degrees plus the b columns' degrees
    minus the ones where they cross is at least T - z(m-a, n-b). With the column degrees fixed by the profile:
      (1, 1)  deg(r) - x(r, j) >= K_j = T - z(m-1, n-1) - c_j  — every row has at least max_j K_j ones, and a row with a
              one in column j at least K_j + 1;
      (2, 2)  deg(r1) + deg(r2) - (ones of r1, r2 in columns j1, j2) >= T - z(m-2, n-2) - c_j1 - c_j2.
    A clause is written only where the bound is not already implied by the row cuts and the (1, 1) bounds; the clauses
    use the cells and the rows' totalizer outputs only (no new variables). Bounds from satprofile.upper."""
    out = []; c1, c2 = cuts.get(1, 0), cuts.get(2, 0)
    z11, z22 = satprofile.upper(m - 1, n - 1), satprofile.upper(m - 2, n - 2)
    if z11 is None: return out
    K = [T - z11 - c for c in profile]
    floor = max([c1] + K)
    if floor > c1:
        out += [[-at_most(i, floor - 1)] for i in range(m)]
    for j in range(n):
        if K[j] + 1 > floor:
            out += [[-v(i, j), -at_most(i, K[j])] for i in range(m)]
    if z22 is None: return out
    least = lambda U: max([floor] + [K[j] + 1 for j in U])
    for j1, j2 in itertools.combinations(range(n), 2):
        K22 = T - z22 - profile[j1] - profile[j2]
        subsets = [(), (j1,), (j2,), (j1, j2)]
        for U1 in subsets:
            for U2 in subsets:
                need = K22 + len(U1) + len(U2); L1, L2 = least(U1), least(U2)
                if max(L1 + L2, c2) >= need: continue
                for i1, i2 in itertools.combinations(range(m), 2):
                    for p1 in range(L1, need - L2):
                        p2 = need - 1 - p1
                        out.append([-v(i1, j) for j in U1] + [-v(i2, j) for j in U2] + [-at_most(i1, p1), -at_most(i2, p2)])
    return out

def case_formula_lean(m, n, T, profile, kmax, mixed=False):
    pool = IDPool(); v = lambda i, j: pool.id(("x", i, j))
    for i in range(m):
        for j in range(n): v(i, j)
    clauses = []
    for a, b, c in itertools.combinations(range(m), 3):
        ys = []
        for j in range(n):
            y = pool.id(("y", a, b, c, j)); ys.append(y)
            clauses.append([-v(a, j), -v(b, j), -v(c, j), y])
        clauses += CardEnc.atmost(lits=ys, bound=2, vpool=pool, encoding=EncType.seqcounter).clauses
    for j, d in enumerate(profile):
        clauses += CardEnc.equals(lits=[v(i, j) for i in range(m)], bound=d, vpool=pool, encoding=EncType.seqcounter).clauses
    cuts = {}
    for k in range(1, kmax + 1):
        U = satprofile.upper(m - k, n)
        if U is not None and T - U > 0: cuts[k] = T - U
    info = {"cuts": cuts, "clauses for k": {}}
    if cuts:
        # u[i][t] <=> row i has >= t+1 zeros <=> row i has <= n-1-t ones; "row i has <= p ones" is u[i][n-1-p]
        top = n - cuts.get(1, 1) + 1
        u = []
        for i in range(m):
            tot = ITotalizer(lits=[-v(i, j) for j in range(n)], ubound=min(n, top), top_id=pool.top)
            clauses += tot.cnf.clauses
            pool.occupy(pool.top + 1, tot.top_id); pool.top = tot.top_id
            u.append(tot.rhs)
        at_most = lambda i, p: u[i][n - 1 - p]
        if 1 in cuts:
            for i in range(m): clauses.append([-at_most(i, cuts[1] - 1)])
            info["clauses for k"][1] = m
        for k in range(2, kmax + 1):
            tuples = cut_tuples(cuts, k); added = 0
            for S in itertools.combinations(range(m), k):
                for t in tuples:
                    for perm in set(itertools.permutations(t)):
                        clauses.append([-at_most(i, p) for i, p in zip(S, perm)]); added += 1
            info["clauses for k"][k] = added
        if mixed:
            mc = mixed_cut_clauses(m, n, T, profile, cuts, v, at_most); clauses += mc; info["mixed cut clauses"] = len(mc)
    for i in range(m - 1): lex_geq(pool, clauses, [v(i, j) for j in range(n)], [v(i + 1, j) for j in range(n)], ("row", i))
    for j in range(n - 1):
        if profile[j] == profile[j + 1]:
            lex_geq(pool, clauses, [v(i, j) for i in range(m)], [v(i, j + 1) for i in range(m)], ("col", j))
    return pool, clauses, v, info
