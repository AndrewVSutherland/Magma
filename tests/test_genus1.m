AttachSpec("magma.spec");
SetSeed(1);
print "test_genus1.m";

print "  ModularPolynomial";
R2 := PolynomialRing(Integers(),2);
assert R2!ModularPolynomial(2) eq R2!ClassicalModularPolynomial(2);
assert R2!ModularPolynomial(13) eq R2!ClassicalModularPolynomial(13);
// FLAGGED (audit 2026-08-06): havemodpoly gate (n le 60) passes for 29 composite n <= 60 that
// ClassicalModularPolynomial does not know (e.g. 20), so IsogenyOrbits(E,20) fails with a raw
// file-not-found error from the phi_j_N.txt fallback instead of the require message.

print "  LMFDBLabel";
// Ground truth from LMFDB ec_curvedata: SELECT lmfdb_label,"Clabel" FROM ec_curvedata WHERE conductor IN (11,37,121,990,5077)
assert LMFDBLabel("11a1") eq "11.a2";
assert LMFDBLabel("11a2") eq "11.a1";
assert LMFDBLabel("11a3") eq "11.a3";
assert LMFDBLabel("37b1") eq "37.b2";
assert LMFDBLabel("990h1") eq "990.i1";
assert LMFDBLabel("121d3") eq "121.d1";
assert LMFDBLabel(EllipticCurve([0,0,1,-7,6])) eq "5077.a1";

print "  EllipticCurvesOfConductorDividing";
S := EllipticCurvesOfConductorDividing(37);
assert {Conductor(e) : e in S} eq {37};       // no curves of conductor 1
assert #{CremonaReference(e) : e in S} eq #S; // distinct curves
assert #EllipticCurvesOfConductorDividing(11) eq 1; // one representative per isogeny class (see docstring)

print "  EllipticCurvesOfNaiveHeightBoundedBy";
S := EllipticCurvesOfNaiveHeightBoundedBy(500);
// inline brute force: minimal short models of naive height <= 500
BF := {[a,b] : a in [-5..5], b in [-4..4] | 4*a^3+27*b^2 ne 0 and Max(4*Abs(a)^3,27*b^2) le 500
       and #[p : p in PrimeDivisors(GCD(a,b)) | Valuation(a,p) ge 4 and Valuation(b,p) ge 6] eq 0};
assert Set(S) eq BF;
assert [6,1] in EllipticCurvesOfNaiveHeightBoundedBy(4*6^3);   // boundary A
assert [0,7] in EllipticCurvesOfNaiveHeightBoundedBy(27*49);   // boundary B
assert [16,64] notin EllipticCurvesOfNaiveHeightBoundedBy(110592); // non-minimal (2^4|A, 2^6|B)

print "  MinimalShortWeierstrassModel + NaiveHeight";
M := MinimalShortWeierstrassModel(EllipticCurve([0,0,0,-48,320]));
assert Coefficients(M) eq [0,0,0,-3,5];
assert NaiveHeight(EllipticCurve([0,0,0,-48,320])) eq 675; // max(4*27,27*25)
E := EllipticCurve([1,1,1,-305,7888]); // 121.a1
M := MinimalShortWeierstrassModel(E);
assert IsIsomorphic(E,M);
a := Coefficients(M); A := Integers()!a[4]; B := Integers()!a[5];
assert &and[Valuation(A,p) lt 4 or Valuation(B,p) lt 6 : p in PrimeDivisors(GCD(A,B))];

print "  PrimitiveDivisionPolynomial";
E := EllipticCurve([0,0,0,1,1]);
for n in [2..12] do
    g := PrimitiveDivisionPolynomial(E,n);
    expected := n eq 2 select 3 else &+[MoebiusMu(n div d)*d^2 : d in Divisors(n)] div 2;
    assert Degree(g) eq expected;                       // number of x-coords of points of exact order n
    assert IsDivisibleBy(DivisionPolynomial(E,n),g);
    for m in [m : m in Divisors(n) | m ne n and m gt 1] do
        assert Degree(GCD(g,DivisionPolynomial(E,m))) eq 0;  // no lower-order roots
    end for;
end for;

print "  PrimitiveDivisionPolynomial2/3";
E1728 := EllipticCurve([1,0]); E0 := EllipticCurve([0,1]);
R := PolynomialRing(Rationals()); x := R.1;
for n in [3,4,5] do assert Evaluate(PrimitiveDivisionPolynomial2(E1728,n),x^2) eq R!PrimitiveDivisionPolynomial(E1728,n); end for;
for n in [2,4,5,7] do assert Evaluate(PrimitiveDivisionPolynomial3(E0,n),x^3) eq R!PrimitiveDivisionPolynomial(E0,n); end for;
// REGRESSION (audit 2026-08-06 fix): PrimitiveDivisionPolynomial2(E,2) silently returned the zero
// polynomial (psi_2 = 4x(x^2+a) is not a polynomial in x^2); now a require rejects n=2.
ok := false; try _ := PrimitiveDivisionPolynomial2(E1728,2); catch e ok := true; end try; assert ok;
// REGRESSION (audit 2026-08-06 fix): PrimitiveDivisionPolynomial3(E,3) silently returned the zero
// polynomial (psi_3^prim = 3x(x^3+4b) is not a polynomial in x^3); now a require rejects n=3.
ok := false; try _ := PrimitiveDivisionPolynomial3(E0,3); catch e ok := true; end try; assert ok;

print "  IsogenyOrbits/IsogenyDegree/IsogenyGaloisGroup";
E11 := EllipticCurve([0,-1,1,-10,-20]); E37 := EllipticCurve([0,0,1,-1,0]);
assert IsogenyOrbits(E11,5) eq {* 1^^2, 4 *};    // 11a1 has two rational 5-isogenies
assert IsogenyDegree(E11,5) eq 1;
assert IsogenyOrbits(E37,5) eq {* 6 *};          // 37a1 mod-5 surjective: transitive on P^1(F5)
assert IsogenyDegree(E37,5) eq 6;
assert #IsogenyGaloisGroup(E37,2) eq 6;          // S3 on the three 2-isogenies
for E in [E11,E37], n in [2,3,5,7] do assert IsogenyDegree(E,n) eq Min(IsogenyOrbits(E,n)); end for;

print "  KummerOrbits/TorsionOrbits/TorsionDegree";
assert KummerOrbits(E11,5) eq {* 1^^2, 2, 4^^2 *};  // x(P),x(2P) rational for the 5-torsion point
assert TorsionOrbits(E11,5) eq {* 1^^4, 4^^5 *};    // 4 rational points of order 5
assert TorsionDegree(E11,5) eq 1;
assert TorsionDegree(E37,2) eq 3;  // irreducible 2-division cubic
assert TorsionDegree(E37,3) eq 8;  // orbit size 8 for surjective mod-3 image
// oracle cross-check on a small sample incl. bad reduction at 2,3:
// points above each irreducible factor g of the primitive n-division polynomial of y^2=f(x)
// form two orbits of size deg g if f is a square in Q[x]/(g), else one orbit of size 2 deg g
for c in [[0,-1,1,-10,-20],[0,0,0,1,1],[1,1,1,0,0],[0,0,0,-48,0],[0,0,0,6,-27]] do
    E := EllipticCurve([Rationals()|z : z in c]);
    W := WeierstrassModel(E); f := HyperellipticPolynomials(W);
    for n in [2..6] do
        Fac := Factorization(PrimitiveDivisionPolynomial(W,n));
        oracle := n eq 2 select {* Degree(a[1])^^a[2] : a in Fac *}
                 else {* IsSquare(quo<Parent(f)|a[1]>!f) select Degree(a[1])^^(2*a[2]) else (2*Degree(a[1]))^^a[2] : a in Fac *};
        assert TorsionOrbits(E,n) eq oracle;
        assert TorsionOrbits(E,n:slow:=true) eq oracle;
        dor := n eq 2 select Min([Degree(a[1]) : a in Fac])
               else Min([(IsSquare(quo<Parent(f)|a[1]>!f) select 1 else 2)*Degree(a[1]) : a in Fac]);
        assert TorsionDegree(E,n) eq dor;
    end for;
end for;
// REGRESSION (audit 2026-08-06 fix): sqmodtest compared BaseRing(g) eq Rationals(), which throws
// 'Bad argument types FldFin, FldRat' for curves over finite fields; TorsionOrbits/TorsionDegree
// crashed over Fq.  Now sqmodtest skips the number-field pretest for other base fields.
// Expected values below verified against brute-force Frobenius-orbit computation on
// TorsionSubgroupScheme points over GF(q^d) (audit script, 2026-08-06).
EF := EllipticCurve([GF(5)|1,1]);
assert TorsionOrbits(EF,2) eq {* 3 *};
assert TorsionOrbits(EF,3) eq {* 1^^2, 2^^3 *};
assert TorsionOrbits(EF,4) eq {* 6^^2 *};
assert TorsionOrbits(EF,6) eq {* 3^^2, 6^^3 *};
assert TorsionDegree(EF,4) eq 6;
EF7 := EllipticCurve([GF(7)|2,3]);
assert TorsionOrbits(EF7,5) eq {* 2^^2, 4^^5 *};
assert TorsionOrbits(EF7,6) eq {* 1^^2, 2^^2, 3^^2, 6^^2 *};
// number-field base still works
K5 := QuadraticField(5); EK5 := EllipticCurve([K5|1,1]);
assert TorsionOrbits(EK5,5) eq {* 24 *};
assert TorsionDegree(EK5,4) eq 12;
// FLAGGED (audit 2026-08-06): n=1 edge cases: IsogenyOrbits/KummerOrbits/TorsionOrbits return the
// integer 1 (not {* 1 *}), and TorsionGaloisGroup(E,1)/FullTorsionDegree(E,1) crash because
// PrimitiveTorsionPolynomial(E,1) returns the integer 1 (GaloisGroup of an integer).

print "  PrimitiveTorsionPolynomial/TorsionGaloisGroup/FullTorsionDegree/TorsionField";
assert #TorsionGaloisGroup(E37,2) eq 6;
assert FullTorsionDegree(E37,2) eq 6;         // GL2(F2)
assert Degree(TorsionField(E37,2)) eq 6;
assert FullTorsionDegree(E37,3) eq 48;        // GL2(F3), 37a1 is surjective mod 3

print "  EndomorphismRingData";
// exhaustive over small q: trace, norm equation, and End ring discriminant via Hilbert class polynomial
for q in [q : q in [2..49] | IsPrimePower(q)] do
    F := GF(q);
    for j in F do
        for E in Twists(EllipticCurveFromjInvariant(j)) do
            a,b,D := EndomorphismRingData(E);
            assert a eq TraceOfFrobenius(E);
            assert a^2 - b^2*D eq 4*q;
            if D eq 1 then assert a^2 eq 4*q;
            else
                assert D lt 0 and D mod 4 in {0,1};
                assert Evaluate(ChangeRing(HilbertClassPolynomial(D),F),j) eq 0;
            end if;
        end for;
    end for;
end for;
// deep branch: q=587, a=6: D=-2312=-8*17^2, v=17 prime with v^2>8|D0| -> IsHCPRoot/Weber path.
// Deuring: #{j : disc -8} = h(-8) = 1, #{j : disc -2312} = h(-2312) = 16
F := GF(587); n1 := 0; n2 := 0;
for j in F do
    if j eq 0 or j eq F!1728 then continue; end if;
    E := EllipticCurveFromjInvariant(j);
    if Abs(TraceOfFrobenius(E)) ne 6 then continue; end if;
    if TraceOfFrobenius(E) ne 6 then E := QuadraticTwist(E); end if;
    a,b,D := EndomorphismRingData(E);
    assert a eq 6 and a^2-b^2*D eq 4*587;
    assert Evaluate(ChangeRing(HilbertClassPolynomial(D),F),j) eq 0;
    if D eq -8 then n1 +:= 1; else assert D eq -2312; n2 +:= 1; end if;
end for;
assert n1 eq 1 and n2 eq 16;
// FldRat,q signature
a,b,D := EndomorphismRingData(EllipticCurve([0,0,1,-1,0]),101);
assert a eq TraceOfFrobenius(ChangeRing(EllipticCurve([0,0,1,-1,0]),GF(101))) and a^2-b^2*D eq 4*101;

print "  PrecomputeEndomorphismRingData";
Z := PrecomputeEndomorphismRingData(12);
assert Type(Z) eq SeqEnum; // doc fix (audit 2026-08-06): declared return type is now SeqEnum, not Assoc
for p in [5,7,11] do
    for j in [1..p-1] do
        if GF(p)!j eq GF(p)!1728 then continue; end if;
        r := PrimitiveRoot(p);
        A := GF(p)!(3*j*(1728-j)); B := GF(p)!(2*j*(1728-j)^2);
        if not IsSquare(B) then A *:= r^2; B *:= r^3; end if;
        a,b,D := EndomorphismRingData(EllipticCurve([A,B]));
        assert Z[p][j] eq [a,b,D];
    end for;
end for;

print "  FrobeniusMatrix/FrobeniusMatrices";
for q in [q : q in [3..25] | IsPrimePower(q)] do
    for j in GF(q) do
        for E in Twists(EllipticCurveFromjInvariant(j)) do
            A := FrobeniusMatrix(E);
            assert Determinant(A) eq q and Trace(A) eq TraceOfFrobenius(E);
        end for;
    end for;
end for;
E := EllipticCurve([0,-1,1,-10,-20]);
AQ := FrobeniusMatrices(E,50);
assert [Determinant(a) : a in AQ] eq [p : p in PrimesInInterval(1,50) | p ne 11];
assert &and[Trace(a) eq TraceOfFrobenius(E,Integers()!Determinant(a)) : a in AQ];
K := QuadraticField(-1);
AK := FrobeniusMatrices(ChangeRing(E,K),50);
assert Sort([Determinant(a) : a in AK]) eq [2,5,5,9,13,13,17,17,29,29,37,37,41,41,49]; // split/inert primes of Q(i), norm <= 50, good reduction

print "  PossiblyNonsurjectivePrimes";
// LMFDB ec_curvedata nonmax_primes must be contained in the output (provable guarantee)
PNPtests := [
    <[0,-1,1,-7820,-263580],[5]>,          // 11.a1
    <[1,-1,1,-3,3],[7]>,                   // 26.b2
    <[0,-1,1,-912,10919],[13]>,            // 147.b1
    <[1,1,1,-76013,8034781],[17]>,         // 14450.bh2
    <[1,1,0,-254901700,1566310159625],[37]>, // 1225.f1
    <[1,0,1,-1,-2],[2,3,5]>,               // 50.a3
    <[1,-1,1,-9695,-364985],[2,3,7]>,      // 162.c1
    <[0,0,0,-1129345880,-86028258620304],[11]> // 232544.f1, mod-11 image 11.55.1.b.1 (nonsplit normalizer)
];
for t in PNPtests do
    E := EllipticCurve([Rationals()|z : z in t[1]]);
    S := PossiblyNonsurjectivePrimes(E);
    assert Set(t[2]) subset Set(S);
    assert Set(S) subset Set(PossiblyNonsurjectivePrimes(E:Fast:=true));
end for;
assert PossiblyNonsurjectivePrimes(EllipticCurve([0,-1,1,-7820,-263580])) eq [5];
assert PossiblyNonsurjectivePrimes(EllipticCurve([0,0,0,-1129345880,-86028258620304])) eq [11];
assert PossiblyNonsurjectivePrimes(EllipticCurve([0,0,1,-1,0])) eq []; // 37.a1 surjective everywhere
// FldNum version
EK := ChangeRing(EllipticCurve([0,-1,1,-10,-20]),QuadraticField(5));
SK := PossiblyNonsurjectivePrimes(EK:A:=FrobeniusMatrices(EK,256));
assert 5 in SK; // 11a1 retains its 5-isogeny over Q(sqrt 5)

print "  PossiblyNonsurjectivePrimes regressions";
// REGRESSION (audit 2026-08-06 fix): the FldNum version called the nonexistent signature
// GL2FrobeniusMatrices(E,256) when A was not supplied, so the default-A path always crashed.
// Now it calls FrobeniusMatrices(E,256).
SK := PossiblyNonsurjectivePrimes(EK); // default-A path
assert SK eq [5];
// REGRESSION (audit 2026-08-06 fix): the ell >= 11 loop used Frobenius elements with trace = 0 mod ell
// as witnesses; such elements lie in both Cartan normalizers (and give u = 0, the projective
// involution present in every exceptional subgroup), so they silently eliminated genuinely
// non-surjective primes.  232544.f1 has mod-11 image 11.55.1.b.1 (nonsplit Cartan normalizer,
// LMFDB nonmax_primes=[11]); its base change to Q(sqrt 5) has image contained in the image over Q,
// hence is still non-surjective at 11, but the buggy code returned [] here.
E2K := ChangeRing(EllipticCurve([0,0,0,-1129345880,-86028258620304]),QuadraticField(5));
S2K := PossiblyNonsurjectivePrimes(E2K:A:=FrobeniusMatrices(E2K,1024));
assert 11 in S2K;
// and primes are still eliminated for surjective curves after the fix
E3K := ChangeRing(EllipticCurve([0,0,1,-1,0]),QuadraticField(5)); // 37.a1 base-changed
assert PossiblyNonsurjectivePrimes(E3K:A:=FrobeniusMatrices(E3K,1024)) eq [];

print "ALL TESTS PASSED test_genus1.m";
quit;
