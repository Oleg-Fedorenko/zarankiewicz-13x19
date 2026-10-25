# Redundant pair constraints for a case of the double split (every row and every column degree fixed). In a matrix with
# no all-ones 3x3 block, if two columns share the rows R, every other column has at most two ones in R (three would
# close a 3x3 block with the two), so the degrees of the rows in R sum to at most 2|R| + 2(n - 2); the |R| rows of
# least degree already sum to more than that once |R| passes a bound. The same holds for two rows with the roles
# exchanged. Every matrix of the case satisfies these, so adding them loses nothing; they only tell the solver early
# what it would otherwise have to find out by search.
#   pair_bound(degrees, other) -> the largest r with (sum of the r smallest degrees) <= 2r + 2(other - 2)
from pysat.card import CardEnc, EncType
from satprofile2 import case_formula

def pair_bound(degrees, other):
    d = sorted(degrees); best = 0
    for r in range(1, len(d) + 1):
        if sum(d[:r]) <= 2 * r + 2 * (other - 2): best = r
    return best

def case_formula_pairs(m, n, rows, cols):
    pool, clauses, v = case_formula(m, n, rows, cols)
    clauses = list(clauses)
    shared_columns = pair_bound(cols, m)        # two rows share at most this many columns
    shared_rows = pair_bound(rows, n)           # two columns share at most this many rows
    if shared_columns < n:
        for a in range(m):
            for b in range(a + 1, m):
                zs = []
                for j in range(n):
                    z = pool.id(("pr", a, b, j)); zs.append(z)
                    clauses.append([-v(a, j), -v(b, j), z])
                clauses += CardEnc.atmost(lits=zs, bound=shared_columns, vpool=pool, encoding=EncType.seqcounter).clauses
    if shared_rows < m:
        for a in range(n):
            for b in range(a + 1, n):
                ws = []
                for i in range(m):
                    w = pool.id(("pc", a, b, i)); ws.append(w)
                    clauses.append([-v(i, a), -v(i, b), w])
                clauses += CardEnc.atmost(lits=ws, bound=shared_rows, vpool=pool, encoding=EncType.seqcounter).clauses
    return pool, clauses, v, {"two rows share at most": shared_columns, "two columns share at most": shared_rows}

def row_sum_floor(m, n, T, kmax):
    """For each r, the least sum of the r smallest row degrees over every row profile the counting allows (satprofile2,
    k-row cuts with k <= kmax): a matrix of the cell has its row profile among them, so its r lightest rows hold at least
    this much."""
    from satprofile2 import row_profiles
    profiles = row_profiles(m, n, T, kmax)
    return {r: min(sum(sorted(p)[:r]) for p in profiles) for r in range(1, m + 1)}

def profile_formula_pairs(m, n, T, profile, kmax):
    """The column-profile case of satprofile (column degrees fixed, k-row cuts, lex) with the pair constraints added: two
    rows share at most pair_bound(profile, m) columns; two columns share at most the largest r whose least possible
    row sum (row_sum_floor) is <= 2r + 2(n - 2)."""
    from satprofile import case_formula as column_case
    pool, clauses, v = column_case(m, n, T, tuple(profile), kmax)
    clauses = list(clauses)
    floor = row_sum_floor(m, n, T, kmax)
    shared_columns = pair_bound(profile, m)
    shared_rows = max(r for r in range(1, m + 1) if floor[r] <= 2 * r + 2 * (n - 2))
    for a in range(m):
        for b in range(a + 1, m):
            zs = []
            for j in range(n):
                z = pool.id(("pr", a, b, j)); zs.append(z)
                clauses.append([-v(a, j), -v(b, j), z])
            clauses += CardEnc.atmost(lits=zs, bound=shared_columns, vpool=pool, encoding=EncType.seqcounter).clauses
    for a in range(n):
        for b in range(a + 1, n):
            ws = []
            for i in range(m):
                w = pool.id(("pc", a, b, i)); ws.append(w)
                clauses.append([-v(i, a), -v(i, b), w])
            clauses += CardEnc.atmost(lits=ws, bound=shared_rows, vpool=pool, encoding=EncType.seqcounter).clauses
    return pool, clauses, v, {"two rows share at most": shared_columns, "two columns share at most": shared_rows}
