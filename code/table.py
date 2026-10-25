# The results of the sweep against the frontier: what was in print, what followed from it, what the Laboratory found,
# and what follows once its finds are added. Also the check that nothing contradicts: a lower bound above an upper one
# would mean a mistake somewhere — in a matrix, in a bound read off a paper, or here.
#   python3 table.py            the table, in Markdown
#   python3 table.py --json     the same as data
import json, re, sys, pathlib
HERE = pathlib.Path(__file__).resolve().parent
ROWS = range(8, 17); COLS = range(16, 24)
# A. Norris, Improved lower bounds for Zarankiewicz numbers z(m,n;3,3) from simulated annealing (11 Sept 2026):
# the nineteen cells of his Table 1 — and (13,23) = 140 by a weight-3 column appended to the 13 x 22 witness of
# 2608.08154, as he notes; that one is not among his improvements
NORRIS = {(13, 19): 120, (13, 20): 125, (13, 21): 131, (14, 19): 128, (14, 20): 131, (14, 21): 136, (14, 22): 142, (14, 23): 146,
          (15, 19): 136, (15, 20): 139, (15, 21): 144, (15, 22): 149, (15, 23): 154, (16, 18): 137, (16, 19): 142, (16, 20): 147,
          (16, 21): 152, (16, 22): 157, (16, 23): 162}
NORRIS_NOTED = {(13, 23): 140}
# B. Borsik, Zarankiewicz-számok alsó becslése szemi random algoritmusokkal, BSc thesis, BME VIK (advisor T. Héger),
# 21 December 2025, Table 11; the matrices are in github.com/balazsborsik/Zarankiewicz, output/K33/graphs (pushed by
# 2025-12-23). Found on 2026-10-15 by the review of the note, after both passes: it has 150, 156, 158 and 163 in
# (15,22), (15,23), (16,22), (16,23) — the four values the search had taken for new. Every matrix below (the best of
# each cell) was checked here by a column-triple program: right size, 0/1, the stated count, no 3x3 block of ones.
BORSIK = {
          (8, 16): 70, (8, 17): 74, (8, 18): 77, (8, 19): 81, (8, 20): 84, (8, 21): 87, (8, 22): 90, (8, 23): 94,
          (9, 16): 77, (9, 17): 81, (9, 18): 85, (9, 19): 89, (9, 20): 93, (9, 21): 96, (9, 22): 100, (9, 23): 103,
          (10, 16): 85, (10, 17): 90, (10, 18): 94, (10, 19): 98, (10, 20): 102, (10, 21): 106, (10, 22): 110,
          (10, 23): 112, (11, 16): 92, (11, 17): 96, (11, 18): 101, (11, 19): 106, (11, 20): 111, (11, 21): 116,
          (11, 22): 121, (11, 23): 123, (12, 16): 99, (12, 17): 103, (12, 18): 108, (12, 19): 114, (12, 20): 120,
          (12, 21): 126, (12, 22): 132, (12, 23): 134, (13, 16): 107, (13, 17): 110, (13, 18): 116, (13, 19): 119,
          (13, 20): 125, (13, 21): 131, (13, 22): 137, (13, 23): 140, (14, 16): 115, (14, 17): 118, (14, 18): 124,
          (14, 19): 127, (14, 20): 131, (14, 21): 136, (14, 22): 142, (14, 23): 146, (15, 16): 123, (15, 17): 126,
          (15, 18): 132, (15, 19): 135, (15, 20): 139, (15, 21): 144, (15, 22): 150, (15, 23): 156, (16, 16): 127,
          (16, 17): 132, (16, 18): 137, (16, 19): 141, (16, 20): 147, (16, 21): 152, (16, 22): 158, (16, 23): 163}
# the thesis's cells just outside the table: they reach into it by deleting the lightest line
BORSIK_OUTSIDE = {
          (8, 24): 97, (9, 24): 106, (10, 24): 116, (11, 24): 127, (12, 24): 138, (13, 24): 145, (14, 24): 152,
          (15, 24): 160, (16, 24): 168, (17, 17): 138, (17, 18): 143, (17, 19): 149, (17, 20): 155, (17, 21): 161,
          (17, 22): 167, (17, 23): 171, (17, 24): 176}
# (upper, lower) per cell as Figure 2 of arXiv:2605.01120v3 prints them (read at full resolution on 2026-10-13);
# one number = a value established before that paper
FIG = {
 8:  [70, 74, 77, 81, 84, 87, 90, (94, 94)],
 9:  [77, 81, 85, 89, 93, 96, (100, 100), (104, 103)],
 10: [85, 90, 94, 98, (102, 99), (108, 106), (111, 110), (115, 112)],
 11: [92, 96, (101, 97), (108, 102), (112, 111), (116, 116), (121, 121), (125, 118)],
 12: [99, (108, 102), (113, 108), (118, 110), (122, 113), (127, 116), (132, 132), (136, 125)],
 13: [107, (116, 106), (121, 115), (125, 114), (130, 119), (135, 127), (140, 137), (145, 135)],
 14: [115, (124, 118), (129, 124), (135, 121), (140, 125), (145, 131), (150, 137), (155, 138)],
 15: [(123, 123), (132, 125), (138, 132), (143, 132), (149, 138), (154, 139), (160, 143), (165, 149)],
 16: [(128, 128), (141, 128), (146, 130), (152, 132), (158, 146), (164, 147), (169, 149), (175, 158)],
}

def frontier(extra=()):
    """Lower and upper bounds per cell: what is in print, plus `extra` lower bounds, closed under adding a line with two
    ones, deleting the lightest line, and the bound that deleting one puts above. Returns (lo, hi, src, printed)."""
    lo, hi, src = {}, {}, {}
    for m in ROWS:
        for n, cell in zip(COLS, FIG[m]):
            u, l = cell if isinstance(cell, tuple) else (cell, cell)
            lo[m, n], hi[m, n], src[m, n] = l, u, "Fig. 2 of 2605.01120"
    def exact(m, n, v, who):
        lo[m, n] = max(lo[m, n], v); hi[m, n] = min(hi[m, n], v); src[m, n] = who
    def lower(m, n, v, who):
        if v > lo[m, n]: lo[m, n] = v; src[m, n] = who
    for n in range(18, 23): exact(12, n, 6 * n, "2608.08154")
    for (m, n, v) in [(13, 22, 137), (13, 18, 116), (14, 18, 124), (15, 18, 132), (14, 17, 118), (15, 17, 126)]: exact(m, n, v, "2608.08154 / 2608.08549")
    exact(13, 17, 110, "2608.08549"); lower(16, 17, 132, "2608.08154"); hi[16, 17] = min(hi[16, 17], 133)
    exact(12, 17, 103, "published, per 2608.08549")
    # Table 3 of Tan, arXiv:2203.02283 (2022): the values printed in bold are exact, proven there; the others are upper
    # bounds. Read off the table's markup on 2026-10-15. Two of them are shown as open in Figure 2 of 2605.01120:
    # z(10,20) = 102 and z(11,18) = 101.
    TAN_EXACT = {9: {16: 77, 17: 81, 18: 85, 19: 89, 20: 93, 21: 96, 22: 100}, 10: {16: 85, 17: 90, 18: 94, 19: 98, 20: 102},
                 11: {16: 92, 17: 96, 18: 101}, 12: {16: 99}, 13: {16: 107}, 14: {16: 115}, 15: {16: 123}, 16: {16: 128}}
    TAN_UPPER = {9: {23: 104}, 10: {21: 108, 22: 112, 23: 116}, 11: {19: 109, 20: 113, 21: 117, 22: 121, 23: 125},
                 12: {17: 108, 18: 113, 19: 118, 20: 122, 21: 127, 22: 132, 23: 136},
                 13: {17: 117, 18: 122, 19: 126, 20: 131, 21: 136, 22: 140, 23: 145},
                 14: {17: 125, 18: 130, 19: 136, 20: 141, 21: 146, 22: 151, 23: 155},
                 15: {17: 134, 18: 139, 19: 144, 20: 150, 21: 155, 22: 160, 23: 166},
                 16: {17: 142, 18: 148, 19: 154, 20: 160, 21: 165, 22: 170, 23: 176}}
    for m, row in TAN_EXACT.items():
        for n, v in row.items():
            if lo[m, n] > v or hi[m, n] < v: raise SystemExit(f"Tan's exact z({m},{n}) = {v} contradicts the table: {lo[m, n]}..{hi[m, n]}")
            exact(m, n, v, "2203.02283 (Tan)")
    for m, row in TAN_UPPER.items():
        for n, v in row.items():
            hi[m, n] = min(hi[m, n], v)
    # dfield, finite-zarankiewicz-closures (GitHub, 2026): eight exact values with certificates, and Z(13,23) <= 144
    for (m, n, v) in [(9, 23, 103), (10, 21, 106), (10, 22, 110), (10, 23, 112), (11, 19, 106), (11, 20, 111), (11, 23, 123), (12, 23, 134)]:
        if lo[m, n] > v or hi[m, n] < v: raise SystemExit(f"the repository's exact z({m},{n}) = {v} contradicts the table: {lo[m, n]}..{hi[m, n]}")
        exact(m, n, v, "finite-zarankiewicz-closures")
    hi[13, 23] = min(hi[13, 23], 144)
    for (m, n), v in {**NORRIS, **NORRIS_NOTED}.items(): lower(m, n, v, "Norris, Sept 2026")
    for (m, n, v) in [(13, 19, 118), (14, 19, 126), (16, 18, 136), (14, 20, 126), (16, 19, 136)]: lower(m, n, v, "2608.26603")
    for (m, n), v in BORSIK.items(): lower(m, n, v, "Borsik, Dec 2025")
    for (m, n), v in BORSIK_OUTSIDE.items():
        if m == 17 and n <= 23: lower(16, n, v - v // 17, "Borsik, Dec 2025, a row deleted")
        if n == 24 and m <= 16: lower(m, 23, v - v // 24, "Borsik, Dec 2025, a column deleted")
    printed = dict(lo)
    for (m, n, v, who) in extra: lower(m, n, v, who)
    changed = True
    while changed:
        changed = False
        for m in ROWS:
            for n in COLS:
                cand_lo, cand_hi = lo[m, n], hi[m, n]
                if (n, m) in lo: cand_lo = max(cand_lo, lo[n, m]); cand_hi = min(cand_hi, hi[n, m])
                if (m, n - 1) in lo: cand_lo = max(cand_lo, lo[m, n - 1] + 2)
                if (m - 1, n) in lo: cand_lo = max(cand_lo, lo[m - 1, n] + 2)
                if (m, n + 1) in lo: cand_lo = max(cand_lo, lo[m, n + 1] - lo[m, n + 1] // (n + 1))
                if (m + 1, n) in lo: cand_lo = max(cand_lo, lo[m + 1, n] - lo[m + 1, n] // (m + 1))
                for (pm, pn, k) in [(m, n - 1, n), (m - 1, n, m)]:
                    if (pm, pn) in hi:
                        z = hi[pm, pn]
                        while (z + 1) - (z + 1) // k <= hi[pm, pn]: z += 1
                        cand_hi = min(cand_hi, z)
                if cand_lo != lo[m, n] or cand_hi != hi[m, n]:
                    if cand_lo > lo[m, n]: src[m, n] = "follows from a neighbour"
                    lo[m, n], hi[m, n] = cand_lo, cand_hi; changed = True
    return lo, hi, src, printed

def found():
    """The Laboratory's verified matrices: found/z-<m>-<n>-<ones>.json, the best of each cell."""
    best = {}
    for path in (HERE / "found").glob("z-*-*-*.json"):
        m, n, ones = map(int, re.match(r"z-(\d+)-(\d+)-(\d+)\.json", path.name).groups())
        best[m, n] = max(best.get((m, n), 0), ones)
    return best

if __name__ == "__main__":
    before_lo, before_hi, _, printed = frontier()
    lab = found()
    after_lo, after_hi, src, _ = frontier([(m, n, v, "the Laboratory") for (m, n), v in lab.items()])
    plain = {(r["m"], r["n"]): r["plain45s"] for r in json.loads((HERE / "sweep-table.json").read_text())}
    rows, trouble = [], []
    for m in ROWS:
        for n in COLS:
            if after_lo[m, n] > after_hi[m, n]: trouble.append(f"({m},{n}): lower {after_lo[m, n]} above upper {after_hi[m, n]}")
            if (m, n) not in lab and after_lo[m, n] == before_lo[m, n]: continue
            rows.append({"m": m, "n": n, "printed": printed[m, n], "known": before_lo[m, n], "upper": after_hi[m, n], "lab": lab.get((m, n)), "plain": plain.get((m, n)), "now": after_lo[m, n], "from": src[m, n], "exact": after_lo[m, n] == after_hi[m, n], "norris": NORRIS.get((m, n))})
    if "--json" in sys.argv:
        print(json.dumps({"rows": rows, "contradictions": trouble}, indent=1)); sys.exit(0)
    # "best known before" is the table of the sources closed under adding and deleting a line; the raw printed value is
    # in --json, and equals it in every row of this search
    print("| z(m,n;3,3) | best known before | this search | plain greedy, 45 s | now known | at most |")
    print("|---|---|---|---|---|---|")
    for r in rows:
        mark = " **(exact)**" if r["exact"] else ""
        new = r["now"] > r["known"]
        print(f"| ({r['m']},{r['n']}) | {r['known']} | {r['lab'] if r['lab'] is not None else '—'} | {r['plain'] if r['plain'] is not None else '—'} | {'**' + str(r['now']) + '**' if new else r['now']}{mark} | {r['upper']} |")
    better = [r for r in rows if r["now"] > r["known"]]
    settled_here = [r for r in rows if r["exact"] and r["known"] < r["upper"]]
    exact_rows = sum(1 for r in rows if r["exact"])
    settled = f"{len(settled_here)} settled by this search, {exact_rows - len(settled_here)} before it" if settled_here else f"none settled by this search; the {exact_rows} exact values were settled before it"
    print(f"\n{len(lab)} cells searched; {len(better)} with a lower bound above the best known before; {settled}.")
    print("contradictions:", trouble or "none")
