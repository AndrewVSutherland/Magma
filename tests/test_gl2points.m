AttachSpec("magma.spec");
SetSeed(1);
print "test_gl2points.m";

print "  GL2PointCounts genus 0";
// X_0(13) and X_0(8) have genus 0 with a rational cusp, so #X_H(Fq) = q+1 for all good q;
// this sweep exercises jNormalPointCount, j0FM, j1728FM, norm_equation and the supersingular
// corrections for every residue class of q (odd/even powers of p = 2,3, p = 1,5,7,11 mod 12)
Q13 := [q : q in PrimePowers(200) | GCD(q,13) eq 1];
assert GL2PointCounts(GL2Borel(13),Q13) eq [q+1 : q in Q13];
Q8 := [q : q in PrimePowers(200) | IsOdd(q)];
assert GL2PointCounts(GL2Borel(8),Q8) eq [q+1 : q in Q8];

print "  GL2PointCounts X0(11)";
// #X_0(11)(Fq) = #E(Fq) for E = 11a1 = X_0(11) (good reduction at all p != 11)
E11 := EllipticCurve("11a1");
H11 := GL2Borel(11);
Q11 := [q : q in PrimePowers(100) | GCD(q,11) eq 1];
assert GL2PointCounts(H11,Q11) eq [#ChangeRing(E11,GF(q)) : q in Q11];
assert GL2PointCount(H11,169) eq #ChangeRing(E11,GF(169)); // p = 13 = 1 mod 12, e even

print "  GL2PointCounts Xns+(11)";
// X_ns+(11) is isomorphic to the elliptic curve 121b1 (Ligozat; LMFDB modular curve 11.55.1.b.1)
E121b := EllipticCurve("121b1");
Hns := GL2NonsplitCartanNormalizer(11);
Qns := [q : q in PrimePowers(60) | GCD(q,11) eq 1];
assert GL2PointCounts(Hns,Qns) eq [#ChangeRing(E121b,GF(q)) : q in Qns];

print "  GL2PointCount vs SmallModularCurve";
// independent models of X_0(23), X_0(26) (genus 2) from Magma's small modular curve database
X23 := SmallModularCurve(23); B23 := GL2Borel(23);
assert &and[GL2PointCount(B23,p) eq #Points(ChangeRing(X23,GF(p))) : p in [3,5,7,13,29]];
X26 := SmallModularCurve(26); B26 := GL2Borel(26);
assert &and[GL2PointCount(B26,p) eq #Points(ChangeRing(X26,GF(p))) : p in [5,7,11,17]];

print "  GL2Traces";
T0 := TracesOfFrobenius(E11,31); P0 := PrimesInInterval(1,31);
assert GL2Traces(H11,31) eq [T0[i] : i in [1..#P0] | P0[i] ne 11];
assert GL2Traces(H11,31:ZeroFill:=true) eq [P0[i] eq 11 select 0 else T0[i] : i in [1..#P0]];
assert GL2Traces(H11,3,4) eq [3^i+1-GL2PointCount(H11,3^i) : i in [1..4]];
assert GL2Traces(H11,20:B0:=10) eq [T0[i] : i in [1..#P0] | P0[i] ge 10 and P0[i] le 20 and P0[i] ne 11];
// LMFDB gps_gl2zhat_fine 7.168.3.a.1: traces at p = 2,3,5,11,13,17,19,23,29 (level 7, genus 3)
H7 := GL2FromGenerators(7,168,[[5,0,0,2],[6,0,0,6]]);
assert GL2Traces(H7,29) eq [3,0,0,12,0,0,0,24,6];

print "  GL2PointCountsPrecompute";
Qp := [q : q in PrimePowers(60) | GCD(q,11) eq 1];
M11 := GL2PointCountsPrecompute(11,Qp);
assert GL2PointCounts(H11,Qp,M11) eq GL2PointCounts(H11,Qp);
assert GL2Traces(H11,Qp,M11) eq GL2Traces(H11,Qp);
M11b, Qb := GL2PointCountsPrecompute(11,60);
assert Qb eq [p : p in PrimesInInterval(1,60) | p ne 11];
assert GL2PointCounts(H11,Qb,M11b) eq GL2PointCounts(H11,Qb);
// level of H smaller than modulus of precomputed matrix
M33 := GL2PointCountsPrecompute(33,[2,7,13,29]);
assert GL2PointCounts(GL2Lift(H11,33),[2,7,13,29],M33) eq GL2PointCounts(H11,[2,7,13,29]);
// determinant index 2: X_H = X(1) over Q(sqrt(5)), so 2(q+1) points when q is a square mod 5, else 0
G5 := GL(2,Integers(5));
H2 := sub<G5|Generators(SL(2,Integers(5))),[1,0,0,4]>;
Q5 := [2,3,7,11,19,29,31];
assert GL2PointCounts(H2,Q5) eq [q mod 5 in {1,4} select 2*(q+1) else 0 : q in Q5];
M5 := GL2PointCountsPrecompute(5,Q5);
assert GL2PointCounts(H2,Q5,M5) eq GL2PointCounts(H2,Q5);
assert GL2Traces(H2,Q5) eq [0 : q in Q5];

print "  GL2PointCount direct";
htab := ClassNumberTable(4*97);
f11 := GL2PermutationCharacter(GL2IncludeNegativeOne(H11));
C11 := GL2RationalCuspCounts(H11);
assert &and[GL2PointCount(11,htab,f11,C11,q) eq GL2PointCount(H11,q) : q in [2,3,5,7,13,49,97]];

print "  GL2FrobeniusMatrices";
// for every finite field, the set of Frobenius matrices is the union over j of the per-j sets
MM := MatrixRing(Integers(),2);
for q in [8,9,13,25,27,49] do
    S := {MM!A : A in GL2FrobeniusMatrices(q)};
    T := {MM|};
    for j in GF(q) do T join:= {MM!A : A in GL2FrobeniusMatrices(j)}; end for;
    assert S eq T;
end for;
assert GL2FrobeniusMatrices(GF(9)) eq GL2FrobeniusMatrices(9);
assert MM![13,0,0,13] in GL2FrobeniusMatrices(169); // supersingular trace 2p, p = 13 = 1 mod 12
// Frobenius matrix determinant/trace sanity over F7
assert &and[Determinant(A) eq 7 : A in GL2FrobeniusMatrices(7)];
assert {Trace(MM!A) : A in GL2FrobeniusMatrices(GF(7)!6)} eq {TraceOfFrobenius(EE), -TraceOfFrobenius(EE)} where EE := EllipticCurveFromjInvariant(GF(7)!6);

print "  GL2jCounts";
// fiber counts over Y(1) sum to the point count minus rational cusps
for q in [9,13,25,169] do
    assert &+GL2jCounts(H11,q) + GL2RationalCuspCount(H11,q) eq GL2PointCount(H11,q);
end for;
assert GL2jCounts(H11,[13,25]) eq [GL2jCounts(H11,13),GL2jCounts(H11,25)];
assert GL2jCounts(GL2Ambient(5),7) eq [1 : j in GF(7)]; // X(1): one point above every j

print "  GL2jInvariants";
J13 := GL2jCounts(H11,13); F13 := [j : j in GF(13)];
assert GL2jInvariants(H11,13) eq [F13[i] : i in [1..13] | J13[i] gt 0];
JJ := GL2jInvariants(H11,[13,25]);
assert JJ[1] eq GL2jInvariants(H11,13) and JJ[2] eq GL2jInvariants(H11,25);

print "  GL2jInvariantTest";
assert &and[GL2jInvariantTest(H11,F13[i]) eq (J13[i] gt 0) : i in [1..13]];
// j = -121 is the j-invariant of a CM curve (D = -11) with a rational 11-isogeny (on X_0(11))
assert GL2jInvariantTest(H11,-121,50);
// j(11a1) is not the j-invariant of a curve with an 11-isogeny (class 11a has only 5-isogenies);
// already at p = 2 the charpoly x^2+2x+2 of Frobenius is irreducible mod 11
assert not GL2jInvariantTest(H11,jInvariant(E11),50);

print "  GL2QObstructions";
// LMFDB 7.168.3.a.1 has obstructions [2,11,23]; 8.96.3.a.1 has obstructions [0,5,29]
assert GL2QObstructions(H7) eq [2,11,23];
assert GL2QObstructions(H7:T:=GL2Traces(H7,23:ZeroFill:=true)) eq [2,11,23];
assert GL2QObstructions(H7:B:=10) eq [2];
assert GL2QObstructions(H7:g:=3,C:=GL2RationalCuspCounts(H7)) eq [2,11,23];
assert GL2PointCount(H7,2) eq 0 and GL2PointCount(H7,11) eq 0 and GL2PointCount(H7,23) eq 0;
H8 := GL2FromGenerators(8,96,[[1,4,4,5],[3,0,0,3],[5,6,2,7]]);
assert GL2QObstructions(H8) eq [0,5,29];
assert GL2QObstructions(GL2Borel(13)) eq [Integers()|]; // genus 0 with rational cusps
assert GL2QObstructions(GL2Ambient(5)) eq [Integers()|]; // X(1)

print "  GL2LPolynomial";
assert &and[GL2LPolynomial(H11,q) eq LPolynomial(ChangeRing(E11,GF(q))) : q in [3,4,5,9,25]];
assert GL2LPolynomial(GL2Borel(22),3) eq LPolynomial(ChangeRing(E11,GF(3)))^2; // J_0(22) ~ 11a^2
R<T> := PolynomialRing(Integers());
// J_0(23) = A_f for the newform 23.2.a.a with a_2 = (-1+sqrt(5))/2 (LMFDB): Euler factor at 2
assert GL2LPolynomial(B23,2) eq 4*T^4 + 2*T^3 + 3*T^2 + T + 1;
assert GL2LPolynomial(GL2Borel(13),7) eq R!1; // genus 0

print "  GL2IsogenyClass";
c,r := GL2IsogenyClass(H11); assert c eq "11a" and r eq 0;
c,r := GL2IsogenyClass(Hns); assert c eq "121b" and r eq 1; // X_ns+(11) = 121b1, rank 1

print "  GL2QInfinite";
assert not GL2QInfinite(H11);        // X_0(11): genus 1, rank 0
assert GL2QInfinite(GL2Borel(13));   // X_0(13): genus 0 with rational points
assert GL2QInfinite(Hns);            // X_ns+(11): genus 1, rank 1
assert not GL2QInfinite(H7);         // locally obstructed genus 3 curve
H1f := sub<G5|[1,1,0,1],[2,0,0,1]>;  // quadratic refinement related to X_1(5), without -I
assert GL2QInfinite(H1f) and not GL2QInfinite(H1f:MustContainNegativeOne:=true);

print "  GL2TraceHash";
// trace_hash values from LMFDB gps_gl2zhat_fine for 11.12.1.a.1 = X_0(11) and 7.168.3.a.1
assert GL2TraceHash(GL2Borel(11)) eq 1428752966040989219;
assert GL2TraceHash(H7) eq 978651484239690707;
assert GL2TraceHash(GL2Borel(13)) eq 0; // genus 0
assert GL2TraceHash(GL2Borel(4)) eq 0;  // level < 6

print "  GL2GonalityBounds";
assert GL2GonalityBounds(H11) eq [2,2,2,2];          // genus 1 with rational cusps
assert GL2GonalityBounds(GL2Borel(22)) eq [2,2,2,2]; // genus 2
assert GL2GonalityBounds(GL2Borel(13)) eq [1,1,1,1]; // genus 0 with rational cusps
gb := GL2GonalityBounds(H7); // LMFDB: qbar_gonality 3; X_H is pointless
assert gb[1] le gb[2] and gb[3] le gb[4] and gb[3] le 3 and 3 le gb[4];
// LMFDB groups with known Q- and Qbar-gonality (label, level, index, gens, q_gon, qbar_gon)
// SELECT label,level,index,generators,q_gonality,qbar_gonality FROM gps_gl2zhat_fine WHERE label IN (...)
gdata := [*
<"12.72.3.o.1",12,72,[[3,8,4,3],[5,6,0,11],[7,0,0,1],[9,4,10,9],[11,6,6,7]],2,2>,
<"16.48.3.p.1",16,48,[[7,12,0,11],[13,1,6,5],[13,15,10,5],[15,12,8,7]],4,2>,
<"16.96.3.ex.1",16,96,[[1,14,8,7],[13,1,14,13],[15,10,8,5]],4,2>,
<"10.120.5.a.1",10,120,[[7,6,4,1]],4,4>,
<"12.144.7.k.1",12,144,[[1,0,6,7],[1,2,4,1],[7,0,6,1]],4,4>
*];
for rec in gdata do
    gb := GL2GonalityBounds(GL2FromGenerators(rec[2],rec[3],rec[4]));
    assert gb[1] le rec[5] and rec[5] le gb[2] and gb[3] le rec[6] and rec[6] le gb[4];
end for;

// ------------------------------------------------------------------------
// Regression tests for bugs fixed in the 2026-08 audit
// ------------------------------------------------------------------------

print "  regression: GL2FrobeniusMatrices supersingular trace -2p^(e/2)";
// BUG (fixed): for p = 1 mod 12 and e even, GL2FrobeniusMatrices(q) omitted the
// supersingular Frobenius matrix with trace -2*p^(e/2) (only the +2*p^(e/2) scalar
// matrix was included).  Oracle: every supersingular E/F_13 has trace 0 over F_13,
// hence trace -26 over F_169, and its twist has trace +26.
assert MM![-13,0,0,-13] in GL2FrobeniusMatrices(169);
assert MM![37,0,0,37] in GL2FrobeniusMatrices(1369) and MM![-37,0,0,-37] in GL2FrobeniusMatrices(1369);
S169 := {MM!A : A in GL2FrobeniusMatrices(169)};
T169 := {MM|};
for j in GF(169) do T169 join:= {MM!A : A in GL2FrobeniusMatrices(j)}; end for;
assert S169 eq T169;

print "  regression: GL2PointCounts/GL2Traces list-of-lists dispatch";
// BUG (fixed): GL2PointCounts(H,Q::SeqEnum[RngIntElt]) rejected the list-of-lists
// inputs its body was written to handle, so GL2PointCounts(H,B:PrimePowers:=true),
// GL2Traces(H,B:PrimePowers:=true) and explicit list-of-lists inputs all crashed.
PP := [p : p in PrimesInInterval(1,32) | p ne 11];
assert GL2PointCounts(H11,32:PrimePowers:=true) eq [[#ChangeRing(E11,GF(p^i)) : i in [1..Floor(Log(p,32))]] : p in PP];
assert GL2Traces(H11,32:PrimePowers:=true) eq [[p^i+1-#ChangeRing(E11,GF(p^i)) : i in [1..Floor(Log(p,32))]] : p in PP];
assert GL2PointCounts(H11,[[2,4,8],[3,9,27]]) eq [[#ChangeRing(E11,GF(q)) : q in r] : r in [[2,4,8],[3,9,27]]];
assert GL2Traces(H11,[[2,4,8],[3,9,27]]) eq [[q+1-#ChangeRing(E11,GF(q)) : q in r] : r in [[2,4,8],[3,9,27]]];
zf := GL2PointCounts(H11,32:PrimePowers:=true,ZeroFill:=true);
assert #zf eq #PrimesInInterval(1,32) and zf[5] eq [Integers()|]; // 11 is the 5th prime

print "  regression: GL2PointCounts(H,Q,M) for fine groups";
// BUG (fixed): the precomputed-matrix path did not apply GL2IncludeNegativeOne, so for
// H not containing -I it returned counts that were not the point counts of X_H.
// H1f = <[1,1,0,1],[2,0,0,1]> mod 5 is fine; X_<H1f,-I> = P^1 so counts are q+1.
Q5f := [q : q in PrimePowers(60) | GCD(q,5) eq 1];
M5f := GL2PointCountsPrecompute(5,Q5f);
assert GL2PointCounts(H1f,Q5f,M5f) eq [q+1 : q in Q5f];
assert GL2PointCounts(H1f,Q5f,M5f) eq GL2PointCounts(H1f,Q5f);
assert GL2Traces(H1f,Q5f,M5f) eq GL2Traces(H1f,Q5f);

print "  regression: GL2Traces(H,Q,M) determinant-index correction";
// BUG (fixed): GL2Traces(H,Q,M) returned q+1-n unconditionally, ignoring the
// determinant-index correction applied by GL2Traces(H,Q).  For H2 (det index 2,
// X_H2 = X(1) over Q(sqrt 5)) all traces are 0.
assert GL2Traces(H2,Q5,M5) eq [0 : q in Q5];
assert GL2Traces(H2,Q5,M5) eq GL2Traces(H2,Q5);

print "  regression: GL2PointCounts(H,Q,M) for level-1 H";
// BUG (fixed): the M-path crashed with a sequence-index error for level-1 H
// (e.g. the full group GL(2,Z/N)) instead of returning q+1 as the direct path does.
assert GL2PointCounts(G5,Q5,M5) eq [q+1 : q in Q5];
assert GL2Traces(G5,Q5,M5) eq [0 : q in Q5];

print "  regression: GL2PointCountsPrecompute(N,Q) return value";
// BUG (fixed): the (N,Q) overload declared two return values but returned only one;
// it now declares (and returns) just the matrix.  The (N,B) overload returns both.
Mr := GL2PointCountsPrecompute(11,[2,3]);
assert NumberOfColumns(Mr) eq 2;
Mb2,Qb2 := GL2PointCountsPrecompute(11,20);
assert Qb2 eq [p : p in PrimesInInterval(1,20) | p ne 11] and NumberOfColumns(Mb2) eq #Qb2;

// DOC-BUGS also fixed (no behavioral change to assert):
// - GL2QObstructions docstring now says T:=GL2Traces(H,B:ZeroFill:=true); the T branch
//   consumes one entry per prime, so a non-zero-filled T is misaligned past the first
//   bad prime (tested above: zero-filled T reproduces [2,11,23] for 7.168.3.a.1).
// - GL2GonalityBounds docstring now states the actual upper bounds g+1 (g, if g > 1) / 2*g-2.
// - GL2jCounts/GL2jInvariants declared return types corrected (SeqEnum[RngIntElt]/List etc).
// - comment typo j=1278 -> j=1728 (twice).

print "ALL TESTS PASSED test_gl2points.m";
quit;
