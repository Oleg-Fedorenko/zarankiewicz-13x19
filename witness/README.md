# Witness matrices

Each file is an m × n 0/1 matrix, one row per line, with no 3 × 3 submatrix of ones; the file name is z-m-n-ones.
`z-13-19-120.txt` is the lower bound of the main result. The other 18 are the cells next to it that A. Norris's
table covers; they were found by AperioBot's search laboratory (a language model writes the search programs) on
13–15 October 2026 (the search programs were not given the matrices of [7] or [8]), and `verify_release.py`
checks each one.

| cell | ones (here) | best of [1] (Fig. 2) and [2] | Norris [7] | Borsik [8] |
|---|---|---|---|---|
| (13, 20) | **125** | 119 | 125 | 125 |
| (13, 21) | **131** | 127 | 131 | 131 |
| (14, 19) | **128** | 126 | 128 | 127 |
| (14, 20) | **131** | 126 | 131 | 131 |
| (14, 21) | **136** | 131 | 136 | 136 |
| (14, 22) | **142** | 137 | 142 | 142 |
| (14, 23) | **146** | 138 | 146 | 146 |
| (15, 19) | **136** | 132 | 136 | 135 |
| (15, 20) | **139** | 138 | 139 | 139 |
| (15, 21) | **144** | 139 | 144 | 144 |
| (15, 22) | **150** | 143 | 149 | 150 |
| (15, 23) | **156** | 149 | 154 | 156 |
| (16, 18) | **137** | 136 | 137 | 137 |
| (16, 19) | **142** | 136 | 142 | 141 |
| (16, 20) | **147** | 146 | 147 | 147 |
| (16, 21) | **152** | 147 | 152 | 152 |
| (16, 22) | **158** | 149 | 157 | 158 |
| (16, 23) | **163** | 158 | 162 | 163 |

[1] Bhan, Nobili, Langer, arXiv:2605.01120v3, Figure 2; [2] Saurabh, arXiv:2608.26603; [7] Norris,
doi:10.5281/zenodo.22985558; [8] Borsik, BSc thesis, BME 2025. (15, 22) is the (15, 23) matrix with its lightest
column deleted.
