# Solvers and checkers

The certificates were made and checked with these programs, built from source on macOS 15 (Apple clang 17).
Nothing here is needed to run `verify_release.py` without `--resolve`.

| program | source | sha256 of the source | used for |
|---|---|---|---|
| Kissat 4.0.4 | `kissat-rel-4.0.4.tar.gz` (github.com/arminbiere/kissat, tag rel-4.0.4) | `c4ec54f5034ec096a2ce0dbb38ecd235e673c999d7073c771dcc21c4f32fc123` | anchor cubes and sub-cubes: `kissat -q --unsat <cnf> <proof>` (binary DRAT) |
| CaDiCaL 3.0.1 | `cadical-rel-3.0.1.tar.gz` (github.com/arminbiere/cadical, tag rel-3.0.1) | `0a8ea563b5a25f5aa064634814edab45cc0e45111ea0f5d412a565f806fd7e11` | sub-cubes from 23 Oct 2026: `cadical -q --lrat=true --binary=false <cnf> <fifo>` |
| Glucose 4.2.1 | `glucose-4.2.1.tar.gz` (github.com/audemard/glucose, release 4.2.1) | `a6d4af223e851b50ec6cdbd34b10ce7c8958e372b6c590c589b6d976a03c9a0d` | the 26 whole profiles and 12 x 18: `glucose_release -no-pre -certified [-vbyte] -certified-output=<proof> <cnf>` |
| drat-trim | `drat-trim.c`, github.com/marijnheule/drat-trim, commit 2e3b2dc0ecf9 | `d834b649f437e091597f5347f259b9f681087f89ca0844d0cee250a1a1a0c2ee` | DRAT checks: `drat-trim <cnf> <proof> -t 200000` |
| lrat-check | `lrat-check.c`, same commit | `bf07c2ac96b9035da1ebcc578cb95e956a2b795629d613154cdb307f8a8f4a95` | not used for any certificate (see below) |
| lrat-check-strict | `lrat-check-strict.c` (here) | `0161f444b7015382088eb2cd05593df48312d1e29cc1ec52b0300a92078ba98d` | LRAT checks, reading the proof from a FIFO while CaDiCaL writes it |

Build (each in its unpacked source folder):

```
./configure && make                                      # Kissat and CaDiCaL: build/kissat, build/cadical
cd simp && make rs                                       # Glucose: simp/glucose_release
cc -O2 -o drat-trim drat-trim.c
cc -O2 -std=gnu99 -o lrat-check-strict lrat-check-strict.c
```

For `verify_release.py --resolve N`, put (or link) `cadical` and `lrat-check-strict` in this folder.

## lrat-check-strict

`lrat-check-strict.c` is `lrat-check.c` of drat-trim (commit 2e3b2dc0ecf9) with two changes, both of which only make it
refuse more (`lrat-check-strict.patch`):

1. Every added clause, the empty clause included, must be RUP through its hints: the hints, taken in order, end in a
   conflict. The original also accepts a clause whose hints end in no conflict when no clause containing the negation
   of its first literal is known (a pure-literal test). For the empty clause that literal does not exist and the test
   succeeds, so `printf 'p cnf 2 2\n1 0\n1 2 0\n' > f.cnf; printf '3 0 0\n' > p.lrat; lrat-check f.cnf p.lrat` prints
   `c VERIFIED` although the formula is satisfiable. RAT steps are not accepted either; CaDiCaL's LRAT proofs here
   contain none.
2. Numbers are read as decimal 64-bit values and refused outside the int range (the original reads them with `%i`
   into an int: an id of 5000000000 wraps around and verifies, and `010` is read as octal).

The binaries used for the certificates had these sha256 prefixes, which every LRAT record names: CaDiCaL
`ff0f6c55a208f364`, lrat-check-strict `4002bd31677209c6` (a rebuild with another compiler gives other hashes).
