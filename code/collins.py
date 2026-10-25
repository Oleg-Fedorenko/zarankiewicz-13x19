# Upper bounds on z(m, n; 3, 3) that rest on one refereed source only: Table 4 of A. Collins, A. Riasanovsky,
# J. Wallace, S. Radziszowski, "Zarankiewicz numbers and bipartite Ramsey numbers" (arXiv:1604.01257, 2016), for
# 6 <= m <= n <= 18, read off the paper's text on 2026-10-17; then closed under the deletion lemma (their Lemma 3: a
# lightest line holds at most floor(Z / lines) ones, so Z - floor(Z / n) <= z(m, n - 1), and the same for rows), which
# carries the bounds to n = 19 and beyond, and under monotonicity in each argument. `extra` adds bounds proven here,
# each named, so that a run can say exactly what it rests on.
#   collins_upper(m, n, extra=None) -> an upper bound on z(m, n; 3, 3), or None outside the closed range
TABLE4 = {
    6: [26, 29, 32, 36, 39, 42, 45, 48, 50, 53, 56, 58, 61],
    7: [33, 37, 40, 44, 47, 50, 53, 56, 60, 63, 66, 69],
    8: [42, 45, 50, 53, 57, 60, 64, 67, 70, 74, 78],
    9: [49, 54, 59, 64, 67, 70, 73, 77, 81, 85],
    10: [60, 64, 68, 73, 77, 81, 85, 90, 94],
    11: [69, 74, 80, 84, 88, 92, 96, 101],
    12: [80, 86, 91, 96, 99, 103, 109],
    13: [92, 98, 104, 107, 110, 116],
    14: [105, 112, 115, 118, 124],
    15: [120, 123, 126, 132],
    16: [128, 133, 140],
    17: [141, 148],
    18: [156],
}

def _table():
    hi = {}
    for m, row in TABLE4.items():
        for k, v in enumerate(row):
            n = m + k
            hi[m, n] = hi[n, m] = v
    return hi

def closure(extra=None, top=24):
    """Bounds for 6 <= m, n <= top: the table, `extra`, monotonicity, and the deletion lemma, to a fixed point."""
    hi = _table()
    for (m, n), v in (extra or {}).items():
        hi[m, n] = min(hi.get((m, n), v), v); hi[n, m] = hi[m, n]
    changed = True
    while changed:
        changed = False
        for m in range(6, top + 1):
            for n in range(6, top + 1):
                cands = []
                if (m, n - 1) in hi:
                    # largest Z with Z - floor(Z / n) <= z(m, n - 1)
                    cap = hi[m, n - 1]; Z = cap
                    while (Z + 1) - (Z + 1) // n <= cap: Z += 1
                    cands.append(Z)
                if (m - 1, n) in hi:
                    cap = hi[m - 1, n]; Z = cap
                    while (Z + 1) - (Z + 1) // m <= cap: Z += 1
                    cands.append(Z)
                for (a, b) in ((m + 1, n), (m, n + 1)):   # z is increasing in each argument
                    if (a, b) in hi: cands.append(hi[a, b])
                if not cands: continue
                best = min(cands)
                if (m, n) not in hi or best < hi[m, n]:
                    hi[m, n] = hi[n, m] = best; changed = True
    return hi

def collins_upper(m, n, extra=None):
    hi = closure(extra)
    return hi.get((m, n))
