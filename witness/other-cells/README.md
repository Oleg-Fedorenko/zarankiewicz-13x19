# Other cells of the same search

AperioBot's search laboratory ran over 27 cells (rows 9–16, columns 17–23, where the published table had gaps).
Besides 13 × 19 and the 18 cells in `../README.md`, it reached in these eight cells the best value known — in six of
them a proven exact value — and nothing above it. The matrices are here for completeness; `verify_release.py`
checks each one.

| cell | ones (here) | status of the cell |
|---|---|---|
| (9, 23) | 103 | exact value 103 (dfield 2026 [6]) |
| (10, 20) | 102 | exact value 102 (Tan 2022 [5]) |
| (10, 22) | 110 | exact value 110 (dfield 2026 [6]) |
| (10, 23) | 112 | exact value 112 (dfield 2026 [6]) |
| (11, 23) | 123 | exact value 123 (dfield 2026 [6]) |
| (12, 23) | 134 | exact value 134 (dfield 2026 [6]) |
| (13, 23) | 140 | known 140 ≤ z ≤ 143 |
| (16, 17) | 132 | known 132 ≤ z ≤ 133 |

[5] J. Tan, arXiv:2203.02283 (2022), Table 3 (bold values are exact); [6] dfield, finite-zarankiewicz-closures,
GitHub (2026). For (13, 23) the lower bound 140 is also in Borsik's thesis and in Norris's note; for (16, 17) it is
in Afrasyab, arXiv:2608.08154.
