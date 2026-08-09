# Test suite

Regression tests for the Magma package in this repository. Each file
`tests/test_<module>.m` exercises the intrinsics of the corresponding source
file `<module>.m` and pins the bug fixes applied during the 2026-08 audit.

## Running the suite

From the repo root (the directory containing `magma.spec`):

```bash
./tests/run_tests.sh          # runs all tests/test_*.m, 4 at a time
./tests/run_tests.sh -j6      # override parallelism
```

Each test runs as `timeout 600 magma -b tests/test_<module>.m` with output
captured to `tests/logs/test_<module>.log`. A test **passes** iff its log
contains the line `ALL TESTS PASSED test_<module>.m`. The script prints a
summary table (test, PASS/FAIL, seconds) and exits nonzero on any failure.

Notes:
- Magma is single-threaded; on a 16-core box `-j6` is safe. Higher values
  mainly increase memory usage.
- Tests must run offline: any value derived from LMFDB or another oracle is
  hardcoded with a comment citing its source.
- `gl2classno.dat` is a cache file created in the repo root by the GL2
  machinery on first use; it is gitignored (as are `tests/logs/` and
  `tests/tmp_*`).

## Conventions for adding a test file

A test file `tests/test_<name>.m` must:

1. Start with `AttachSpec("magma.spec");` (tests are run from the repo root)
   and `SetSeed(1);` for reproducibility.
2. Consist of `assert` statements (use `try/catch` to assert that invalid
   input raises an error). Print short section headers with `print " ..."` so
   failures are easy to localize in the log.
3. End with exactly:
   ```
   print "ALL TESTS PASSED test_<name>.m";
   quit;
   ```
   (The runner greps for this line; nothing after a failed assert is printed,
   so a crashed test can never pass.)
4. Run in well under the 600 s timeout — target a few minutes at most.

## Current coverage (2026-08 audit)

| Test file            | Source file     | Highlights |
|----------------------|-----------------|------------|
| `test_utils.m`       | `utils.m`       | split/ReplaceCharacter trailing-delimiter fixes (Magma 2.29 Split drift), HurwitzClassNumber Zagier H(-u^2), atoiiii whitespace, getval on sequences, NormalizedIgusaClebschInvariants over GF(p), SmoothNumbers/Count boundary q=B, EasyFactorization(0), many doc fixes |
| `test_chars.m`       | `chars.m`       | IsCyclic(2^e), label-regexp anchoring, Conductor/CharacterOrder/Degree of Map characters, Conrey q=1 edge cases, ConreyCharacterOrbitRepIndexes filters, AssociatedCharacter 2-part, SquareRoots coercion, untyped-signature typos |
| `test_gl2base.m`     | `gl2base.m`     | GL1/SL2 level-1 constants, Borel/Triangular subgroup fixes (GL2Borel1PC, GL2Triangular1Subgroup), NegOne at N=2, permutation representations at level 1, similarity/Gassmann doc drift, GL2SubgroupKey old-style, GL2CartanNormalizer level |
| `test_mfdims.m`      | `mfdims.m`      | QDimension\* overloads (M vs S vs Eisenstein), NewTrace p^2\|n correction, FrickeNewTraces/ALNewTraces crashes, odd-weight guards, NumberOfNewspaces empty-sum universes |
| `test_gl2points.m`   | `gl2points.m`   | GL2FrobeniusMatrices supersingular trace -2p^(e/2), GL2PointCounts list-of-lists signature, precomputed-matrix path (-I inclusion, level 1, det-index traces), doc fixes |
| `test_gl2tab.m`      | `gl2tab.m`      | colsplit trailing-field fix, GL2/SL2LoadLattice lookup, LabelTable N filter on makegroups tables, gl2keytab Genus as integer, GL2Load short lines, label-comparison docs |
| `test_genus1.m`      | `genus1.m`      | PossiblyNonsurjectivePrimes over number fields (missing intrinsic + trace-0 witness bug), PrimitiveDivisionPolynomial n=2,3 guards, TorsionOrbits over finite fields |
| `test_genus2euler.m` | `genus2euler.m` | Genus2AlmostGoodEulerFactor return-value declarations, WhichTypeOnly at p=2 |
| `test_tracehash.m`   | `tracehash.m`   | TraceHash/TraceHashWindow, TwistHash semantics, TraceStats return order (LMFDB-pinned values) |
| `test_mfutils.m`     | `mfutils.m`     | CompareNewspaceLabels antisymmetry, HeckeOrbitCode 64-bit bound, Split\*Label return shapes |
| `test_polredabs.m`   | `polredabs.m`   | polredbestify DiscFactors passthrough, nfisincl variable-name robustness and degree-1 shape, global-ring print-name side effects |

Known limitations (flagged, not fixed — see the audit reports):
- `tracehash.m`: `SlowTraceHash(CrvHyp)` and `TraceHash(CrvPln)` call a
  `TracesOfFrobenius` signature that exists nowhere (the maintainer will
  address this upstream); the genus 2 fast path still needs an external
  `hashcurves` binary, but as of 2026-08-09 a missing binary raises a clean
  error instead of failing obscurely.

(The originally-flagged `GL2MinimalConjugate` non-minimality was fixed on
2026-08-09 after label-impact analysis — see
`reports/gl2minimalconjugate/investigation.md`; `test_gl2base.m` now
brute-forces all level-4 classes, the only affected modulus.)
