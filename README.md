# z(13, 19; 3, 3) = 120 — a certified proof

Oleg Fedorenko · research note and data: [doi:10.5281/zenodo.23637633](https://doi.org/10.5281/zenodo.23637633)

The Zarankiewicz number z(m, n; 3, 3) is the largest number of ones in an m × n 0/1 matrix with no 3 × 3 submatrix
of ones. This repository holds the proof that **z(13, 19; 3, 3) = 120**, everything it rests on, and a verifier that
checks it from this repository alone.

- **Research note:** [`paper/z13x19-120-note.pdf`](paper/z13x19-120-note.pdf) (5 pages; source `paper/note.html`).
- **Lower bound:** [`witness/z-13-19-120.txt`](witness/z-13-19-120.txt), a 13 × 19 matrix with 120 ones and no 3 × 3
  block of ones (row degrees 12, 9¹², column degrees 8, 7⁴, 6¹⁴).
- **Upper bound:** no such matrix has 121 ones. The best published upper bound before this work was 122.
- **Also:** witness matrices for the 18 neighbouring cells (`witness/README.md`) — for instance z(14, 23) ≥ 146,
  z(15, 22) ≥ 150, z(15, 23) ≥ 156 — each checked by the verifier. They were found independently; in every cell they
  reproduce the best bound of Norris (2026) and Borsik (2025), and they exceed the bounds of Bhan–Nobili–Langer and
  Saurabh (2026). Matrices for the eight other cells the same search covered are in `witness/other-cells/`.
- **Origin:** a test task for AperioBot, an add-on for AI agents created by the author, a lawyer at
  Aperio Law Firm (EDRPOU code 44031724); AI assistance is disclosed in §9 of the note.

## How the proof goes

1. **Bounds.** The cuts use upper bounds that follow from Table 4 of Collins, Riasanovsky, Wallace and Radziszowski
   (J. Algorithms Comput. 47 (2016) 63–78) closed under the deletion lemma, plus z(12, 18) ≤ 108, certified here
   (`data/z12x18-109.json`). Nothing else.
2. **30 column profiles.** Counting leaves 30 multisets of column degrees. 26 are refuted whole by SAT
   (Glucose 4.2.1, DRAT proofs verified by drat-trim) — `data/profiles-whole.json`.
3. **Anchor cubes.** The four most uniform profiles — A (8,7⁵,6¹³), B (8,7⁶,6¹¹,5), C (7⁸,6¹⁰,5), D (7⁷,6¹²) — are split
   by how the other columns meet a column of maximum degree into 203, 512, 1 254 and 509 cubes (`data/anchor/*/patterns.json`).
4. **Sub-cubes.** 698 cubes are split further by fixing columns in canonical order: 58 186 sub-cubes.
5. **Certificates.** Each sub-cube is refuted by an exact rational Farkas certificate of a linear relaxation
   (32 602, `data/anchor/*/farkas.jsonl.gz`) or by SAT with a proof — Kissat 4.0.4 + drat-trim, or CaDiCaL 3.0.1 with
   its LRAT proof checked while written by `lrat-check-strict` (25 584, records in `data/anchor/*/subcubes.jsonl`).
6. **Audit.** Every formula regenerated and compared byte for byte, every Farkas certificate re-verified in exact
   arithmetic, coverage re-enumerated, 72 random proofs re-checked: no problem (`audit/`).

## Verify it yourself

Requirements: Python ≥ 3.10 and [PySAT](https://pysathq.github.io) (`pip install python-sat`).

```
python3 verify_release.py --workers 8
```

checks, from this repository alone: the bounds (1); the 12 × 18 link — one profile, and its formula's SHA-256 equals
the certified one (2); the 30 profiles and the 26 whole ones (3); for every anchor profile, the patterns, every cube,
the coverage of every split cube by its sub-cubes, every Farkas certificate (exact arithmetic), and the SHA-256 of
every solver formula (4); the 27 witness matrices (5). About an hour on 8 cores. With `--resolve 12` it also solves 12 random parts
again with CaDiCaL and checks each LRAT proof while it is written; build the two tools first (`tools/BUILD.md`).
The verifier generates every formula with the Collins bounds only (`code/collins.py`), so a matching hash shows that
the certified formula is exactly the one these bounds give.

To check the witness alone, nothing but Python is needed:

```
python3 -c "import itertools as I;L=[l.strip() for l in open('witness/z-13-19-120.txt') if l.strip()];R=[{j for j,x in enumerate(l) if x=='1'} for l in L];print(len(L),all(len(l)==19 and set(l)<=set('01') for l in L),sum(map(len,R)),all(len(a&b&c)<3 for a,b,c in I.combinations(R,3)))"
```

prints `13 True 120 True`: 13 rows, each of 19 characters 0 or 1, 120 ones, and no three rows sharing three columns
(which is the same as no 3 × 3 block of ones).

## Layout

| path | contents |
|---|---|
| `paper/` | the research note (PDF and its HTML source) |
| `verify_release.py` | the standalone verifier |
| `code/` | the generator and the programs that produced and audited the certificates (Python; `collins.py` holds the 2016 table) |
| `data/z12x18-109.json` | the certificate record of z(12, 18) ≤ 108 (formula SHA-256, solver and checker output) |
| `data/profiles-whole.json` | the 26 profiles decided whole |
| `data/anchor/{A,B,C,D}/` | `patterns.json` (the cubes), `cubes.jsonl` (one record per cube), `subcubes.jsonl` (one per sub-cube a split cube lists), `farkas.jsonl.gz` (the Farkas certificates) |
| `audit/` | the cell audit of 25 October 2026 (`audit-13x19-121.json`, log `audit-13x19-121-final.txt`) and the per-profile audits |
| `tools/` | `lrat-check-strict.c` and its patch against drat-trim's `lrat-check`, and how to build the solvers and checkers |
| `witness/` | the 120-matrix, the matrices of the 18 neighbouring cells (`witness/README.md`), and of the eight other cells the same search covered (`witness/other-cells/`) |

A record of a solver part names the encoding, the solver, the checker and its verdict, the times, and the SHA-256 of
the DIMACS formula that was solved. The DRAT proofs of the 26 whole profiles and of the 12 × 18 link (3.4 GB, with
their formulas and a SHA-256 manifest) are in the Zenodo record, doi:10.5281/zenodo.23637633; the proofs of the cubes
and sub-cubes (577 GB compressed) are not published — the author keeps them and shares any on request. LRAT proofs were checked while being written and were not stored. Any part can be
regenerated (`code/anchor_cubes.py`, `code/subcubes.py`) and re-proved in minutes.

## A note on `lrat-check`

drat-trim's `lrat-check` (commit 2e3b2dc0ecf9) reports `c VERIFIED` for the satisfiable formula `p cnf 2 2 / 1 0 / 1 2 0`
with the one-line proof `3 0 0`; clause ids above 2³¹ wrap around. `tools/lrat-check-strict.c` makes every added clause,
the empty one included, follow by unit propagation through its hints, and rejects out-of-range numbers. The LRAT results
here were checked with it; the verifier's `--resolve` refuses to use a checker that accepts the bogus proof.

## Citation and licence

See `CITATION.cff`. Code: MIT (`LICENSE`); data, paper and witness: CC BY 4.0 (`LICENSE-DATA`).
<!-- The author, the repository URL and the DOI are filled in at publication. -->
