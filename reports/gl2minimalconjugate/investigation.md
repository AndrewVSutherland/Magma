# GL2MinimalConjugate: bug analysis, label-safety verification, and fix

**Date:** 2026-08-09 · **Method:** three parallel investigations (paper-repo comparison, level-scope brute force, label-impact analysis against LMFDB `gps_gl2zhat_fine`), all claims below verified by executed Magma (V2.29-9) transcripts.

## The bug

`GL2MinimalConjugate` (gl2base.m) enumerates the conjugates of `H` in `GL(2,Z/N)` (N = level of H) and returns the one whose `GL2MinimalGenerators` sequence is lex-minimal, where matrices compare as `Eltseq` quadruples `[a,b,c,d]`. To avoid computing minimal generators for every conjugate, a pruning step first discarded conjugates via `A := [Min([k:k in K]):K in S]` — **Magma's internal `GrpMatElt` ordering, not `Eltseq` ordering**. When the two orders disagree, the pruning can discard the conjugate containing the true Eltseq-minimal elements, and the returned generator sequence is not minimal.

## Mechanism and scope: only modulus 4, ever

Magma's element comparison over `Integers(4)` — and **only** `Integers(4)` among all moduli tested — is not Eltseq-lex: Z/4 matrix rows are stored packed (2 bits per entry) and compared little-endian *within* each row, so the effective sort key is `(b,a,d,c)` instead of `(a,b,c,d)`. Verified exhaustively on all 256 matrices / 16 vectors over Z/4; full inversion census at N = 2..16 finds discordance only at N = 4 (1440 unordered pairs); moduli 32, 49, 121, 169 and every modulus relevant to the RSZB data verified concordant (full vector sorts plus 20k–500k random pairs each).

Where the orders agree, the shipped pruning is provably equivalent to correct pruning. Empirically: **12 of 58** conjugacy classes of level-4 subgroups of `GL(2,Z/4)` returned non-minimal results (e.g. `sub<GL(2,Z/4)|[3,2,0,3]>` → `[[3,0,2,3]]` instead of `[[1,2,2,1]]`); **0 wrong out of ~38,000+ classes** at every other level tested (exhaustive N = 2..13, 15, 16; index ≤ 96 at N = 20, 24, 25, 27, 32; all RSZB-table groups at levels 25, 27, 49 and the level-32 tables). Since `GL2Level` reduces first, only groups of true level exactly 4 are affected — at any ambient modulus.

## Why no published or beta label is affected

1. **The RSZB paper labels were computed with different, correct code.** The paper repo's `GL2MinimalConjugate` (`ell-adic-galois-images/groups/gl2.m:1311–1324`) takes `Min([Sort([Eltseq(h):h in K]):K in S])` over all surviving conjugates — pure Eltseq, no pruning — and is byte-identical in every commit from 2021-06-21 through HEAD. The buggy pruning first appears in this repo's rewrite of 2024-12-19.
2. **The tiebreaker never fires at level 4.** In the RSZB `GL2Lattice` sort, `GL2MinimalConjugate` is the tiebreaker of last resort, consulted only when groups tie on (level, index, genus), parent-label list, orbit signature, *and* class signature. Among the 39 level-4 groups in the RSZB dataset, the only cohort tying through orbit signatures — {4.6.0.2, 4.6.0.3, 4.6.0.4} — is separated by class signatures.
3. **Where the tiebreaker does fire, buggy = fixed.** It fires for 1,103 labels in 446 tie-sets (levels 8–121, all prime-power; complete list in `tiebreaker-dependent-labels.txt`). In every one, the current code, the fixed code, and the paper code produce identical orderings that reproduce the published `.n` assignments exactly (concordant moduli).
4. **Beta LMFDB.** `gps_gl2zhat_fine`'s primary labels (`N.i.g.c.n` scheme) never consult `GL2MinimalConjugate` (no call sites, no stored minimal-conjugate data, and the RSZB pair 16.24.0.6/7 maps to 16.24.0.f.2/f.1 — opposite order — confirming an independent tiebreak). The `RSZBlabel` column (2-power levels ≤ 64) is immune: levels 8–64 are concordant, and the 39 level-4 rows never reach the tiebreaker.

## The fix

Prune by Eltseq order, excluding the identity (which is always present and carries no information):

```
A := [Min([Eltseq(k):k in K|k ne Identity(G)]):K in S]; a := Min(A);
S := [S[i]:i in [1..#S]|A[i] eq a];
```

Validated against brute force (min of `GL2MinimalGenerators` over *all* conjugates, no prefilter) with **zero disagreements** on every class tested, including all ~38k above. The test suite now brute-forces all level-4 classes exhaustively plus the prime-level checks.

## Related: one-line fix needed in the RSZB paper repo

Under current Magma (V2.29-9), the *paper repo's* `GL2MinimalConjugate` crashes whenever `H` is normal in `GL(2,Z/N)` and contains neither `[0,1,1,0]` nor `[0,1,1,1]` (8 of 58 level-4 classes): `Conjugates(GL2,H)` returns a SetEnum, which line 1322 then indexes as `S[1]`. Fix at `groups/gl2.m:1318`:

```
S := Conjugates(GL2,H);            // before
S := [K:K in Conjugates(GL2,H)];   // after
```

(Reproduced and fix verified on `sub<GL(2,Integers(4))|[-1,0,0,-1]>`; the patched code returns the correct `[[1,0,0,1],[3,0,0,3]]`, and `[[1,0,0,1],[1,2,2,1]]` on the audit example. Minor nit while there: the intrinsic is declared `-> GrpMat` but returns a sequence of Eltseqs.)

## Data

`tiebreaker-dependent-labels.txt`: the 446 tie-sets (1,103 labels) whose RSZB `.n` component was decided by the minimal-conjugate tiebreaker, format `FIRE|<det-namespace>|<N.i.g>|<comma-separated labels>`. None of them change under the fix.
