AttachSpec("magma.spec");
SetSeed(1);
print "test_mfdims.m";

ZZmf := Integers();

print "  QDimensionGamma1";  // vs Magma's independent builtin formulas
for N in [1..50] do for k in [2..7] do
    assert QDimensionModularFormsGamma1(N,k) eq Dimension(ModularForms(Gamma1(N),k));
    assert QDimensionCuspFormsGamma1(N,k) eq DimensionCuspFormsGamma1(N,k);
    assert QDimensionNewCuspFormsGamma1(N,k) eq DimensionNewCuspFormsGamma1(N,k);
    assert QDimensionEisensteinFormsGamma1(N,k) eq Dimension(ModularForms(Gamma1(N),k)) - DimensionCuspFormsGamma1(N,k);
    assert QDimensionOldCuspFormsGamma1(N,k) eq DimensionCuspFormsGamma1(N,k) - DimensionNewCuspFormsGamma1(N,k);
end for; end for;
// old space = sum of new spaces at proper divisor levels with multiplicity #Divisors(N/M)
for N in [1..30] do for k in [2..6] do
    assert QDimensionOldCuspFormsGamma1(N,k) eq
        &+[ZZmf|#Divisors(N div M)*QDimensionNewCuspFormsGamma1(M,k):M in Divisors(N)|M ne N];
end for; end for;

print "  DimensionCuspForms";
// Cohen-Oesterle with Conrey characters vs Magma's independent built-in implementation
for N in [1..32] cat [64,81] do
    for chi in GaloisConjugacyRepresentatives(FullDirichletGroup(N)) do
        n := ConreyIndex(chi);
        for k in [2..5] do
            d := DimensionCuspForms(N,n,k);
            assert d eq DimensionCuspForms(MinimalBaseRingCharacter(chi),k);
            assert QDimensionCuspForms(N,n,k) eq d*Degree(N,n);
        end for;
    end for;
end for;
assert QDimensionCuspForms("13.4",3) eq QDimensionCuspForms(13,4,3);
// deeper weights on levels exercising CO_delta/CO_nu branches (13.3 has chi(z4)=1, 13.12 has chi(z4)=-1, chi(z3)=1)
for t in [<13,3>,<13,12>,<25,7>,<16,3>,<27,26>,<36,35>,<32,3>] do
    chi := DirichletCharacter(t[1],t[2]);
    for k in [2..9] do assert QDimensionCuspForms(t[1],t[2],k) eq Dimension(CuspForms(chi,k)); end for;
end for;
// sum over character orbits = Gamma1 dimension
for N in [1..24] do for k in [2..5] do
    assert &+[ZZmf|QDimensionCuspForms(N,ConreyCharacterOrbitRep(N,i),k) : i in [1..NumberOfCharacterOrbits(N)]]
        eq QDimensionCuspFormsGamma1(N,k);
end for; end for;

print "  DimensionNewCuspForms";
for N in [1..30] do
    for chi in GaloisConjugacyRepresentatives(FullDirichletGroup(N)) do
        n := ConreyIndex(chi);
        for k in [2..4] do
            d := DimensionNewCuspForms(N,n,k);
            assert d eq DimensionNewCuspForms(MinimalBaseRingCharacter(chi),k);
            assert QDimensionNewCuspForms(N,n,k) eq d*Degree(N,n);
        end for;
    end for;
end for;
assert QDimensionNewCuspForms("13.4",3) eq QDimensionNewCuspForms(13,4,3);
assert QDimensionNewCuspForms("13.3.4") eq QDimensionNewCuspForms(13,4,3); // newspace-style label N.k.n
// vs Magma NewSubspace
for N in [1..20] do for n in [m:m in [1..N]|GCD(m,N) eq 1] do
    chi := DirichletCharacter(N,n);
    for k in [2..4] do
        d := Dimension(NewSubspace(CuspForms(chi,k)));
        assert QDimensionNewCuspForms(N,n,k) eq d;
        assert QDimensionNewCuspForms(chi,k) eq d;
    end for;
end for; end for;

print "  QDimensionOldCuspForms";
for N in [1..30] do
    for chi in GaloisConjugacyRepresentatives(FullDirichletGroup(N)) do
        n := ConreyIndex(chi);
        for k in [2,3] do
            o := QDimensionOldCuspForms(N,n,k);
            assert o eq QDimensionCuspForms(N,n,k) - QDimensionNewCuspForms(N,n,k);
            assert o eq QDimensionOldCuspForms(chi,k); // GrpDrchElt variant agrees
        end for;
    end for;
end for;
assert QDimensionOldCuspForms(45,2) eq QDimensionOldCuspForms(45,1,2);
assert QDimensionOldCuspForms("45.1",2) eq QDimensionOldCuspForms(45,1,2);
for N in [1..60] do for k in [2..8] do  // Gamma0 old space vs builtin formulas
    assert QDimensionOldCuspForms(N,k) eq DimensionCuspFormsGamma0(N,k) - DimensionNewCuspFormsGamma0(N,k);
end for; end for;

print "  QDimensionEisensteinForms";
for N in [1..24] do
    for chi in GaloisConjugacyRepresentatives(FullDirichletGroup(N)) do
        n := ConreyIndex(chi);
        for k in [2..5] do
            e := QDimensionEisensteinForms(chi,k);
            assert e eq QDimensionEisensteinForms(N,n,k);
            assert e eq Dimension(EisensteinSubspace(ModularForms(chi,k)));
        end for;
        // weight 1 (Buzzard: half the weight >= 3 dimension)
        if IsOdd(chi) then
            e := QDimensionEisensteinForms(chi,1);
            assert e eq QDimensionEisensteinForms(N,n,1);
            assert e eq Dimension(EisensteinSubspace(ModularForms(chi,1)));
        else
            assert QDimensionEisensteinForms(chi,1) eq 0;
        end if;
    end for;
end for;
assert QDimensionEisensteinForms("13.4",3) eq QDimensionEisensteinForms(13,4,3);
assert QDimensionEisensteinForms(12,2) eq 5; // = dim E_2(Gamma0(12)), LMFDB mf_newspaces 12.2.a eis_dim
assert QDimensionEisensteinForms("11.10",1) eq Dimension(EisensteinSubspace(ModularForms(DirichletCharacter(11,10),1)));

print "  QDimensionNewEisensteinForms";
// new/old divisor-sum identity (valid away from the weight-2 trivial-character anomaly)
for N in [1..36] do
    for chi in GaloisConjugacyRepresentatives(FullDirichletGroup(N)) do
        n := ConreyIndex(chi); C := Conductor(N,n);
        for k in [1..5] do
            d1 := QDimensionNewEisensteinForms(chi,k);
            assert d1 eq QDimensionNewEisensteinForms(N,n,k);
            if k eq 2 and n eq 1 then continue; end if;
            assert QDimensionEisensteinForms(N,n,k) eq
                &+[ZZmf|QDimensionNewEisensteinForms(M,AssociatedCharacter(M,N,n),k)*#Divisors(N div M) where M:=C*d : d in Divisors(N div C)];
        end for;
    end for;
end for;
// weight-2 trivial character vs LMFDB eis_new_dim
// (SELECT level,eis_new_dim FROM mf_newspaces WHERE weight=2 AND char_orbit_index=1 AND level<=36)
lmneweis2 := [0,1,1,0,1,0,1,0,1,0,1,0,1,0,0,1,1,0,1,0,0,0,1,0,3,0,0,0,1,0,1,0,0,0,0,0];
for N in [1..36] do assert QDimensionNewEisensteinForms(N,1,2) eq lmneweis2[N]; end for;
assert QDimensionNewEisensteinForms(144,2) eq 1; // LMFDB 144.2.a eis_new_dim
// LMFDB spot checks: 25.2.d (25.6) eis_new=8, 16.3.f (16.3) eis_new=4, 25.1.f (25.2) eis_new=8, 24.1.h (24.5) eis_new=2
assert QDimensionNewEisensteinForms(25,6,2) eq 8;
assert QDimensionNewEisensteinForms(16,3,3) eq 4;
assert QDimensionNewEisensteinForms(25,2,1) eq 8;
assert QDimensionNewEisensteinForms(24,5,1) eq 2;
assert QDimensionNewEisensteinForms("25.6",2) eq 8;
// weight 1 new Eisenstein: LMFDB 23.1.b has eis_new_dim=1
assert QDimensionNewEisensteinForms(23,22,1) eq 1;
assert QDimensionNewEisensteinForms("23.22",1) eq 1;
assert QDimensionNewEisensteinForms(DirichletCharacter(23,22),1) eq 1;

print "  NumberOfGamma0CuspSpaces";
for B in [1,7,100] do
    assert NumberOfGamma0CuspSpaces(B) eq #[<N,k>:N in [1..B],k in [1..B]|N*k^2 le B];
end for;

print "  NumberOfGamma1CuspSpaces";
for B in [1,7,100] do
    assert NumberOfGamma1CuspSpaces(B) eq &+[NumberOfCharacterOrbits(N)*#[k:k in [1..B]|N*k^2 le B]:N in [1..B]];
end for;

print "  NumberOfNewspaces";
for B in [4,10,100] do
    assert NumberOfNewspaces(B) eq &+[NumberOfCharacterOrbits(N)*#[k:k in [1..B]|N*k^2 le B]:N in [1..B]];
    assert NumberOfNewspaces(B:SkipWeightOne:=true) eq &+[NumberOfCharacterOrbits(N)*#[k:k in [2..B]|N*k^2 le B]:N in [1..B]];
    assert NumberOfNewspaces(B:TrivialCharOnly:=true) eq #[<N,k>:N in [1..B],k in [1..B]|N*k^2 le B];
    assert NumberOfNewspaces(B:Maxk:=3) eq &+[NumberOfCharacterOrbits(N)*#[k:k in [1..3]|N*k^2 le B]:N in [1..B]];
    assert NumberOfNewspaces(B:MaxN:=7) eq &+[NumberOfCharacterOrbits(N)*#[k:k in [1..B]|N*k^2 le B]:N in [1..Min(7,B)]];
end for;

print "  QDimension";
assert QDimension(CuspidalSubspace(ModularSymbols(DirichletCharacter(11,1),2,-1))) eq 1; // genus X_0(11)
assert QDimension(CuspidalSubspace(ModularSymbols(DirichletCharacter(13,4),2,-1))) eq 2; // LMFDB 13.2.e cusp Q-dim
assert QDimension(ModularSymbols(11,2)) eq 3; // 2g+e = 3 (g=1, one Eisenstein class)
assert QDimension(ModularSymbols(DirichletCharacter(5,2),3)) eq 4; // sign-0 dim 2 over Q(chi), degree 2

print "  CharacterLabelVariants";
assert QDimensionCuspForms("23.1",2) eq 2;         // genus X_0(23) = 2
assert QDimensionCuspForms("13.3",4) eq Dimension(CuspForms(DirichletCharacter(13,3),4));
assert QDimensionNewCuspForms("23.2.a") eq 2;      // LMFDB newspace 23.2.a has dim 2
assert QDimensionNewCuspForms("23.1",2) eq 2;
assert QDimensionOldCuspForms("46.1",2) eq DimensionCuspFormsGamma0(46,2) - DimensionNewCuspFormsGamma0(46,2);

print "  SturmBound";
// Values from LMFDB mf_newspaces.sturm_bound (char_orbit_index=1); SturmBound = Floor(k*Index(Gamma0(N))/12)
assert [SturmBound(11,k):k in [1..6]] eq [1,2,3,4,5,6];
assert SturmBound(1,12) eq 1 and SturmBound(2,4) eq 1 and SturmBound(6,2) eq 2 and SturmBound(12,7) eq 14;
assert SturmBound(25,3) eq 7 and SturmBound(49,3) eq 14 and SturmBound(60,12) eq 144 and SturmBound(100,7) eq 105;

print "  QDimensionCuspFormsGamma0";
// tomo1 = dim S_k(Gamma0(N)) (the FULL cusp space)
for N in [1..40] do for k in [2,4,6,8,12] do
    assert QDimensionCuspForms(N,k) eq Dimension(CuspForms(N,k));
    assert QDimensionNewCuspForms(N,k) eq Dimension(NewSubspace(CuspForms(N,k)));
end for; end for;

print "  CuspTrace";  // exercises popa1/sz1 -> H12, h6, CN/CNp/CN2, SNbase, Gpk, sigma1N
for N in [1..12] do for k in [2,4,6] do
    S := CuspForms(N,k); dS := Dimension(S);
    assert CuspTrace(N,k,1) eq dS;
    if dS gt 0 then
        for n in [2..10] do assert CuspTrace(N,k,n) eq Trace(HeckeOperator(S,n)); end for;
    end if;
end for; end for;
// trace of T_1 = dimension
for N in [1..60] do for k in [2,4,6] do assert CuspTrace(N,k,1) eq Dimension(CuspForms(N,k)); end for; end for;
assert [CuspTrace(1,12,n):n in [1..6]] eq [1,-24,252,-1472,4830,-6048]; // Ramanujan tau

print "  CuspTrace1";
assert [CuspTrace1(12,p):p in [2,3,5,7]] eq [-24,252,4830,-16744]; // tau(p)
assert CuspTrace1(16,2) eq 216; // trace of T_2 on S_16(1), LMFDB 1.16.a.a
for k in [12,16,18,20,22,26,28,30] do for p in [2,3,5,7,11] do
    assert CuspTrace1(k,p) eq CuspTrace(1,k,p);
end for; end for;
assert CuspTrace1(10,2) eq 0; // S_10(1) = 0

print "  NewTrace";  // includes n with GCD(N,n)>1 and n=p^e, p||N (newpopa1 bug fixed 2026-08-06)
for N in [1..12] do for k in [2,4] do
    NS := NewSubspace(CuspidalSubspace(ModularSymbols(N,k,1)));
    for n in [1..10] do
        t := NewTrace(N,k,n);
        assert t eq (Dimension(NS) eq 0 select 0 else Trace(HeckeOperator(NS,n)));
    end for;
end for; end for;
// new space dimension = trace of T_1
for N in [1..60] do for k in [2,4,6] do assert NewTrace(N,k,1) eq Dimension(NewSubspace(CuspForms(N,k))); end for; end for;
// LMFDB mf_newforms trace sums (char_order=1)
assert [NewTrace(11,2,n):n in [1..12]] eq [1,-2,-1,2,1,2,-2,0,-2,-2,1,-2]; // 11.2.a.a
assert NewTrace(10,4,10) eq 10;   // 10.4.a.a
assert NewTrace(22,4,11) eq 11;   // 11+(-11)+11 over 22.4.a.a-c
assert NewTrace(20,2,10) eq 0;    // 20.2.a.a
assert NewTrace(24,2,6) eq 0;     // 24.2.a.a
assert NewTrace(23,2,6) eq -5;    // 23.2.a.a
assert NewTrace(6,4,6) eq 6;      // 6.4.a.a
assert NewTrace(27,4,10) eq -54;  // 45+45-144 over 27.4.a.a-c

print "  NewTraces";
for N in [1..30] do for k in [2,4,6] do
    assert NewTraces(N,k,20) eq [NewTrace(N,k,p):p in PrimesInInterval(1,20)];
end for; end for;

print "  FrickeCuspTrace";  // exercises popaN, phiD1, psk, h6
for N in [2..12] do for k in [2,4,6] do
    S := CuspForms(N,k); dS := Dimension(S);
    if dS eq 0 then
        for n in [1..6] do assert FrickeCuspTrace(N,k,n) eq 0; end for;
    else
        W := AtkinLehnerOperator(S,N);
        for n in [1..6] do assert FrickeCuspTrace(N,k,n) eq Trace(HeckeOperator(S,n)*W); end for;
    end if;
end for; end for;
// squareful levels exercise the newpopaN1 branches via sign-0 modular symbols (traces double)
for N in [36,45,48,49,50] do
    M := ModularSymbols(N,2); S := CuspidalSubspace(M);
    if Dimension(S) eq 0 then
        for n in [1..4] do assert FrickeCuspTrace(N,2,n) eq 0; end for;
        continue;
    end if;
    W := AtkinLehnerOperator(S,N);
    for n in [1..4] do assert 2*FrickeCuspTrace(N,2,n) eq Trace(HeckeOperator(S,n)*W); end for;
    Snew := NewSubspace(S);
    if Dimension(Snew) gt 0 then
        Wn := AtkinLehnerOperator(Snew,N);
        assert 2*FrickeNewTrace(N,2,1) eq Trace(Wn);
        pl,mi := FrickeNewDims(N,2);
        assert pl+mi eq Dimension(Snew) div 2 and 2*(pl-mi) eq Trace(Wn);
    else
        assert FrickeNewTrace(N,2,1) eq 0;
    end if;
end for;

print "  FrickeNewDims";  // exercises newpopaN1, popaN1 vs LMFDB plus_dim
// SELECT level,weight,dim,plus_dim FROM mf_newspaces WHERE char_orbit_index=1 AND level<=30 AND weight IN (2,4,6) AND dim>0
lmfricke := [<3,6,1,0>,<4,6,1,0>,<5,4,1,1>,<5,6,1,0>,<6,4,1,1>,<6,6,1,0>,<7,4,1,1>,<7,6,3,1>,
    <8,4,1,1>,<8,6,1,0>,<9,4,1,1>,<9,6,1,0>,<10,4,1,1>,<10,6,3,1>,<11,2,1,0>,<11,4,2,2>,<11,6,4,1>,
    <12,4,1,1>,<13,4,3,2>,<13,6,5,2>,<14,2,1,0>,<14,4,2,2>,<14,6,2,0>,<15,2,1,0>,<15,4,2,2>,<15,6,4,1>,
    <16,4,1,1>,<16,6,2,1>,<17,2,1,0>,<17,4,4,3>,<17,6,6,2>,<18,4,1,1>,<18,6,3,1>,<19,2,1,0>,<19,4,4,3>,
    <19,6,8,3>,<20,2,1,0>,<20,4,1,1>,<20,6,1,0>,<21,2,1,0>,<21,4,4,3>,<21,6,4,1>,<22,4,3,2>,<22,6,5,2>,
    <23,2,2,0>,<23,4,5,4>,<23,6,9,3>,<24,2,1,0>,<24,4,1,1>,<24,6,3,1>,<25,4,3,2>,<25,6,7,3>,<26,2,2,0>,
    <26,4,3,3>,<26,6,5,1>,<27,2,1,0>,<27,4,4,3>,<27,6,7,3>,<28,4,2,1>,<28,6,2,1>,<29,2,2,0>,<29,4,7,5>,
    <29,6,11,4>,<30,2,1,0>,<30,4,2,2>,<30,6,2,0>];
for r in lmfricke do
    a,b := FrickeNewDims(r[1],r[2]);
    assert a eq r[4] and b eq r[3]-r[4];
    assert FrickeNewTrace(r[1],r[2],1) eq 2*r[4]-r[3]; // trace of Fricke involution on new space
end for;
for N in [1..30] do for k in [2,4,6] do
    a,b := FrickeNewDims(N,k);
    assert a ge 0 and b ge 0 and a+b eq NewTrace(N,k,1);
end for; end for;

print "  FrickeNewTrace";  // exercises newpopaNp -> popaNp, pskp, WNp
for N in [6,10,12,15,18] do for k in [2,4] do
    NS := NewSubspace(CuspidalSubspace(ModularSymbols(N,k,1)));
    for p in [2,3,5] do
        t := FrickeNewTrace(N,k,p);
        assert t eq (Dimension(NS) eq 0 select 0 else Trace(HeckeOperator(NS,p)*AtkinLehnerOperator(NS,N)));
    end for;
end for; end for;
// LMFDB: sum of fricke_eigenval*traces[n] over newform orbits (char_order=1)
assert [FrickeNewTrace(11,2,n):n in [1..12]] eq [-1,2,1,-2,-1,-2,2,0,2,2,-1,2];
assert FrickeNewTrace(11,6,11) eq -484;  // 1*(-121) + (-1)*363
assert FrickeNewTrace(14,2,2) eq 1 and FrickeNewTrace(14,2,7) eq -1;
assert FrickeNewTrace(25,6,5) eq 0;
assert FrickeNewTrace(9,6,3) eq 0;
assert FrickeNewTrace(15,6,4) eq -186;   // -28 - 17 - 141 (n=4 coprime composite: newsz path)
assert FrickeNewTrace(23,2,6) eq 5;

print "  ALNewTrace";
// LMFDB: sum of w_Q(orbit)*traces[n]
assert ALNewTrace(21,4,2,3) eq 4 and ALNewTrace(21,4,2,7) eq 10;
assert [ALNewTrace(15,2,n,3):n in [1,2,4,7,8,11]] eq [1,-1,-1,0,3,-4];  // w_3 = +1 on 15.2.a.a
assert [ALNewTrace(15,2,n,5):n in [1,2,4,7,8,11]] eq [-1,1,1,0,-3,4];   // w_5 = -1
for N in [10,15,21,26] do for k in [2,4] do for n in [1,2,4,9,11] do
    if GCD(N,n) eq 1 then
        assert ALNewTrace(N,k,n,1) eq NewTrace(N,k,n);
        assert ALNewTrace(N,k,n,N) eq FrickeNewTrace(N,k,n);
    end if;
end for; end for; end for;

print "  ALNewDims";
// LMFDB atkin_lehner_eigenvals; list is lex-ordered +..+, ..., -..- with i-th sign for i-th smallest prime
assert ALNewDims(15,2) eq [0,1,0,0];       // 15.2.a.a: w_3=+1, w_5=-1
assert ALNewDims(15,6) eq [1,2,1,0];
assert ALNewDims(21,4) eq [1,1,0,2];
assert ALNewDims(30,2) eq [0,0,1,0,0,0,0,0]; // 30.2.a.a: (w_2,w_3,w_5) = (+,-,+)
s,p,m := ALNewDims(1,12); assert s eq [1] and p eq 1 and m eq 0;
for N in [2..30] do for k in [2,4] do
    s,p,m := ALNewDims(N,k); a,b := FrickeNewDims(N,k);
    assert p eq a and m eq b and &+s eq a+b and &and[d ge 0:d in s];
end for; end for;

print "  TraceForm";
assert TraceForm(1,12,5) eq [1,-24,252,-1472,4830];        // tau
assert TraceForm(30,2,10) eq [1,-1,1,1,-1,-1,-4,-1,1,1];   // LMFDB 30.2.a.a traces (trace form of the NEW space)
assert TraceForm(11,2,10) eq [NewTrace(11,2,n):n in [1..10]];
assert TraceForm(22,2,5) eq [0,0,0,0,0];                   // S_2^new(22) = 0

// ================================================================
// Regression tests for bugs fixed in the 2026-08-06 audit
// ================================================================
print "  Regression: QDimensionModularForms";
// BUG (fixed): both overloads returned Dimension(ModularSymbols(...,-1)), which is not dim M_k
// (e.g. old code gave 1 for (9,2) where dim M_2(Gamma0(9)) = 3, and 2 for (chi_7.3,3) where Q-dim M_3 = 4)
for N in [1..16] do
    for chi in GaloisConjugacyRepresentatives(FullDirichletGroup(N)) do
        for k in [1..4] do
            assert QDimensionModularForms(chi,k) eq Dimension(ModularForms(chi,k));
        end for;
    end for;
end for;
for N in [1..30] do for k in [1..6] do
    assert QDimensionModularForms(N,k) eq Dimension(ModularForms(Gamma0(N),k));
end for; end for;
assert QDimensionModularForms(9,2) eq 3 and QDimensionModularForms(1,4) eq 1;
assert QDimensionModularForms(DirichletCharacter(7,3),3) eq 4;

print "  Regression: weight-1 QDimensionCuspForms";
// BUG (fixed): QDimensionCuspForms(chi,1) returned Dimension(ModularForms(chi,1)) (the FULL space
// including Eisenstein) instead of the cuspidal dimension.  LMFDB oracle values:
assert QDimensionCuspForms(DirichletCharacter(23,22),1) eq 1;  // LMFDB 23.1.b cusp_dim=1 (eis_dim=1)
assert QDimensionCuspForms(DirichletCharacter(46,45),1) eq 2;  // LMFDB 46.1.b cusp_dim=2 (eis_dim=2)
assert QDimensionCuspForms(DirichletCharacter(47,46),1) eq 2;  // LMFDB 47.1.b cusp_dim=2 (eis_dim=1)
assert QDimensionCuspForms(DirichletCharacter(39,38),1) eq 1;  // LMFDB 39.1.d cusp_dim=1 (eis_dim=2)
assert QDimensionCuspForms(DirichletCharacter(11,10),1) eq 0;  // S_1(11,chi_11) = 0
assert QDimensionNewCuspForms(DirichletCharacter(23,22),1) eq 1; // LMFDB 23.1.b dim=1
assert QDimensionOldCuspForms(DirichletCharacter(46,45),1) eq 2; // two copies of the level-23 newform

print "  Regression: NumberOfNewspaces small B";
// BUG (fixed): NumberOfNewspaces(B:SkipWeightOne:=true) crashed with 'Illegal null sequence' for B<4
assert NumberOfNewspaces(1:SkipWeightOne:=true) eq 0;
assert NumberOfNewspaces(3:SkipWeightOne:=true) eq 0;
assert NumberOfNewspaces(3:SkipWeightOne:=true,TrivialCharOnly:=true) eq 0;
assert NumberOfNewspaces(4:SkipWeightOne:=true) eq 1;

print "  Regression: QDimensionNewEisensteinForms arity";
// BUG (fixed): the parity-mismatch branch of QDimensionNewEisensteinForms(chi,k) did 'return 0,0;'
assert QDimensionNewEisensteinForms(FullDirichletGroup(3)!1,1) eq 0;

print "  Regression: NewTrace with p||N and p^2|n (newpopa1)";
// BUG (fixed): newpopa1 mishandled the d>1 terms of the Child21 Lemma 10 divisor sum
// (old code: NewTrace(6,4,4)=36, NewTrace(3,6,9)=19764, NewTrace(12,6,9)=-35235)
assert NewTrace(6,4,4) eq 4;      // a_2^2 with a_2=-2 on 6.4.a.a (ModSym oracle: 4)
assert NewTrace(3,6,9) eq 81;     // a_3^2 = 3^4 on 3.6.a.a (ModSym oracle: 81)
assert NewTrace(12,6,9) eq 0;     // S_6^new(12) = 0 (LMFDB 12.6.a dim 0)
assert NewTrace(8,12,4) eq 0;     // v_2(8)=3: d-range must exclude 2 (ModSym oracle: 0)
assert NewTrace(14,2,4) eq 1;     // ModSym oracle (old code gave 3)
assert NewTrace(6,6,9) eq 81;     // ModSym oracle (old code gave 19764? level-6 analogue)
// live oracle sweep over the previously-broken class
for c in [<6,4,4>,<6,4,8>,<10,2,4>,<14,2,8>,<15,2,9>,<21,2,9>,<22,2,4>,<26,2,4>,<20,4,4>,<18,4,4>] do
    NS := NewSubspace(CuspidalSubspace(ModularSymbols(c[1],c[2],1)));
    t := Dimension(NS) eq 0 select 0 else ZZmf!Trace(HeckeOperator(NS,c[3]));
    assert NewTrace(c[1],c[2],c[3]) eq t;
end for;

print "  Regression: FrickeNewTraces";
// BUG (fixed): FrickeNewTraces called the 3-argument local newpopaNp with 2 arguments and always crashed
assert FrickeNewTraces(11,2,10) eq [FrickeNewTrace(11,2,p):p in PrimesInInterval(1,10)];
assert FrickeNewTraces(45,4,10) eq [FrickeNewTrace(45,4,p):p in PrimesInInterval(1,10)];
assert FrickeNewTraces(20,4,12) eq [FrickeNewTrace(20,4,p):p in PrimesInInterval(1,12)];
assert FrickeNewTraces(11,2,10) eq [2,1,-1,2]; // = -a_p of 11.2.a.a (fricke_eigenval=-1)

print "  Regression: ALNewTraces";
// BUG (fixed): default PrimesOnly:=true crashed (newszp arity); PrimesOnly:=false returned primes only;
// also the k=2 non-square branch of skp had its squarefree/non-squarefree bodies swapped
for c in [<11,2,11>,<15,2,3>,<15,2,5>,<20,2,4>,<24,2,8>,<18,2,9>,<21,4,3>,<45,2,9>,<20,4,4>] do
    N := c[1]; k := c[2]; Q := c[3];
    assert ALNewTraces(N,k,12,Q) eq [ALNewTrace(N,k,p,Q):p in PrimesInInterval(1,12)|GCD(N,p) eq 1];
    assert ALNewTraces(N,k,12,Q:PrimesOnly:=false) eq [ALNewTrace(N,k,n,Q):n in [1..12]|GCD(N,n) eq 1];
end for;
assert ALNewTraces(11,2,10,11) eq [2,1,-1,2];
assert ALNewTraces(11,2,10,11:PrimesOnly:=false) eq [-1,2,1,-2,-1,-2,2,0,2,2]; // n=1..10 (all coprime to 11), = Fricke traces

print "  Regression: odd weight Gamma0 dimensions";
// BUG (fixed): QDimensionCuspForms(N,k)/QDimensionNewCuspForms(N,k) returned garbage for odd k
// (tomo1/newtomo1 assume even weight; S_k(Gamma0(N)) = 0 for odd k since -I in Gamma0(N))
assert QDimensionCuspForms(13,3) eq 0 and QDimensionNewCuspForms(13,3) eq 0;
assert QDimensionCuspForms(11,1) eq 0 and QDimensionNewCuspForms(11,1) eq 0;
assert QDimensionCuspForms(45,2) eq 3 and QDimensionNewCuspForms(45,2) eq 1; // even k unchanged
for N in [1..20] do for k in [1,3,5,7] do
    assert QDimensionCuspForms(N,k) eq 0 and QDimensionNewCuspForms(N,k) eq 0;
    assert QDimensionModularForms(N,k) eq 0;
end for; end for;

// FLAGGED (audit 2026-08-06): childmin (local function, unused) has a leftover debug print,
//   passes t instead of t^2 to Gpk, and returns wrong values for its documented purpose; left as-is.
// FLAGGED (audit 2026-08-06): newersz1p (local function, unused) is marked '// TODO: currently broken'
//   by the author and was not audited further.
// NOTE (audit 2026-08-06): dead local functions popa1p (double SNbase factor in k>2 branch) and
//   nutl (m(1-m) typo in the v=4 branch) were fixed; they are unreachable from any intrinsic, so no
//   intrinsic-level regression test is possible.

print "ALL TESTS PASSED test_mfdims.m";
quit;
