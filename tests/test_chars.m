AttachSpec("magma.spec");
SetSeed(1);
print "test_chars.m";

// helper used by the regression section to check that invalid inputs are rejected
function mustfail(f)
    try v := f(); return false; catch e return true; end try;
end function;

//=============================================================================
// Section 1: chars.m lines 1-626 (orbit machinery, labels, Conrey logs/values)
//=============================================================================

print "  IsCyclicParityDegree";
// IsCyclic(N) vs group-theoretic truth (includes 2-power moduli: regression for IsCyclic bug)
assert &and[IsCyclic(N) eq IsCyclic(MultiplicativeGroup(Integers(N))) : N in [1..200]];
for N in [1..30] do
    for chi in CharacterOrbitReps(N) do
        assert Parity(chi) eq (IsEven(chi) select 1 else -1);      // parity = chi(-1)
        assert IsReal(chi) eq (Order(chi) le 2);
        assert Degree(chi) eq EulerPhi(Order(chi));                 // [Q(chi):Q] = phi(ord(chi))
    end for;
end for;
assert Parity(1,1) eq 1 and Parity(2,1) eq 1 and Parity(4,3) eq -1;

print "  UnitGenerators";
for N in [1..40] do
    u := UnitGenerators(N);
    assert UnitGeneratorOrders(N) eq [Order(Integers(N)!x) : x in u];
    assert UnitGenerators(DirichletGroup(N)!1) eq u;
    f := UnitGeneratorsLogMap(N,u);
    for x in [x:x in [1..N]|GCD(x,N) eq 1] do
        e := f(x);
        assert &*[Integers(N)| Integers(N)!u[i]^e[i] : i in [1..#u]] eq Integers(N)!x;
    end for;
end for;

print "  FactorizationProduct";
assert Modulus(Product([* *])) eq 1;
for N in [1..36] do
    for chi in CharacterOrbitReps(N) do
        F := Factorization(chi);
        if N eq 1 then assert #F eq 0; continue; end if;
        assert &and[IsPrimePower(Modulus(psi)) : psi in F];
        psi := Product(F);
        assert Modulus(psi) eq N and Parent(psi)!chi eq psi;
    end for;
end for;

print "  IsMinimal";
// fast implementation vs brute-force BLS definition (IsMinimalSlow); modulus 1 included (regression for IsMinimalSlow crash)
for N in [1..48] cat [64,81,96] do
    for chi in CharacterOrbitReps(N) do assert IsMinimal(chi) eq IsMinimalSlow(chi); end for;
end for;

print "  CharacterOrbits";
for N in [1..30] do
    G,T := CharacterOrbitReps(N:RepTable:=true);
    assert #G eq NumberOfCharacterOrbits(N);
    assert CharacterOrbitLabels(N) eq [CharacterOrbitLabel(N,i) : i in [1..#G]];
    // orbits sorted strictly by (order, trace vector), sizes sum to phi(N)
    assert &and[CompareCharacters(G[i],G[i+1]) lt 0 : i in [1..#G-1]];
    assert &+[Degree(G[i]) : i in [1..#G]] eq EulerPhi(N);
    for i:=1 to #G do
        assert CharacterOrbitOrder(N,i) eq Order(G[i]);
        assert CharacterOrbitIndex(G[i]) eq i;
    end for;
    for chi in Elements(FullDirichletGroup(N)) do
        i := T[chi];
        assert Order(chi) eq Order(G[i]) and IsConjugate(chi,G[i]);
        if N le 24 then assert CharacterOrbitIndex(chi) eq i; end if;
    end for;
    assert NumberOfTrivialCharacterOrbits(N) eq #[i : i in [1..#G] | Order(G[i]) le 2];
    for B in [1,3] do
        assert NumberOfCharacterOrbits(N:OrderBound:=B) eq #[i : i in [1..#G] | Order(G[i]) le B];
    end for;
end for;

print "  Labels";
assert IsCharacterLabel("13.3") and IsConreyLabel("13.3");
b,q,n := IsCharacterLabel("13.3"); assert b and q eq 13 and n eq 3;
assert not IsCharacterLabel("13.14");   // n > q
assert not IsCharacterLabel("13.13");   // gcd(q,n) != 1
b,q,i := IsCharacterOrbitLabel("13.c"); assert b and q eq 13 and i eq 3;
assert not IsCharacterOrbitLabel("13.g");   // only 6 orbits mod 13
assert not IsCharacterOrbitLabel("13.aa");  // leading 'a' only allowed for "a" itself
assert SplitCharacterOrbitLabel("13.f") eq [13,6];
assert SplitCharacterLabel("13.c") eq [13,3];   // orbit label -> minimal Conrey rep 13.3
assert SplitCharacterLabel("13.9") eq [13,9];
assert CharacterOrbitLabel(13,6) eq "13.f";
assert CharacterOrbitLabel("13.11") eq "13.f" and CharacterOrbitLabel("13.f") eq "13.f";
assert ConreyCharacterOrbitLabel(13,11) eq "13.f" and ConreyCharacterOrbitLabel("13.11") eq "13.f";
assert CharacterOrbitIndex("13.f") eq 6 and CharacterOrbitIndex("13.11") eq 6;
assert CharacterOrbitOrder("13.f") eq 12 and CharacterOrbitDegree("13.f") eq 4;
assert CompareCharacterOrbitLabels("13.b","13.f") lt 0 and CompareCharacterOrbitLabels("13.f","13.b") gt 0;
assert CompareCharacterOrbitLabels("13.c","13.c") eq 0 and CompareCharacterOrbitLabels("2.a","13.a") lt 0;
assert ConreyCharacterOrbitRep("13.c") eq "13.3" and ConreyCharacterOrbitRep("13.9") eq "13.3";
assert CharacterOrbitLabel(CharacterOrbitRep("13.f")) eq "13.f";

print "  ConreyConjugatesMinMax";
assert MinimalConreyConjugate(1,1) eq 1 and MaximalConreyConjugate(1,1) eq 1 and IsConreyConjugate(1,1,1);
for q in [2..30] do
    U := [n : n in [1..q] | GCD(n,q) eq 1];
    for n in U do
        m := Order(Integers(q)!n);
        C := {Integers()!((Integers(q)!n)^k) : k in [1..m] | GCD(k,m) eq 1};
        C := {c eq 0 select 1 else c : c in C};   // brute-force Galois orbit of q.n
        assert MinimalConreyConjugate(q,n) eq Min(C);
        assert MaximalConreyConjugate(q,n) eq Max(C);
        assert &and[IsConreyConjugate(q,n,n2) eq (n2 in C) : n2 in U];
    end for;
end for;
assert MinimalConreyConjugate("13.9") eq "13.3" and MaximalConreyConjugate("13.3") eq "13.9";

print "  ConreyOrbitMachinery";
// LMFDB char_dirichlet rows <modulus,orbit,conductor,order,degree,first,last,parity,is_minimal,is_primitive>
// (SELECT ... FROM char_dirichlet WHERE modulus IN (13,24,25,32,36,40,45,48,49,50) ORDER BY modulus,orbit; LMFDB 2026-08-06)
X := [
    <13,1,1,1,1,1,1,1,true,false>,<13,2,13,2,1,12,12,1,true,true>,<13,3,13,3,2,3,9,1,true,true>,
    <13,4,13,4,2,5,8,-1,true,true>,<13,5,13,6,2,4,10,1,true,true>,<13,6,13,12,4,2,11,-1,true,true>,
    <24,1,1,1,1,1,1,1,true,false>,<24,2,8,2,1,19,19,-1,true,false>,<24,3,12,2,1,23,23,1,false,false>,
    <24,4,8,2,1,13,13,1,true,false>,<24,5,3,2,1,17,17,-1,true,false>,<24,6,24,2,1,11,11,1,true,true>,
    <24,7,4,2,1,7,7,-1,false,false>,<24,8,24,2,1,5,5,-1,true,true>,<25,1,1,1,1,1,1,1,true,false>,
    <25,2,5,2,1,24,24,1,false,false>,<25,3,5,4,2,7,18,-1,true,false>,<25,4,25,5,4,6,21,1,true,true>,
    <25,5,25,10,4,4,19,1,true,true>,<25,6,25,20,8,2,23,-1,true,true>,<32,1,1,1,1,1,1,1,true,false>,
    <32,2,8,2,1,17,17,1,false,false>,<32,3,4,2,1,31,31,-1,true,false>,<32,4,8,2,1,15,15,-1,false,false>,
    <32,5,16,4,2,9,25,1,false,false>,<32,6,16,4,2,7,23,-1,false,false>,<32,7,32,8,4,5,29,1,true,true>,
    <32,8,32,8,4,3,27,-1,true,true>,<36,1,1,1,1,1,1,1,true,false>,<36,2,12,2,1,35,35,1,true,false>,
    <36,3,3,2,1,17,17,-1,true,false>,<36,4,4,2,1,19,19,-1,true,false>,<36,5,9,3,2,13,25,1,true,false>,
    <36,6,36,6,2,7,31,-1,true,true>,<36,7,9,6,2,5,29,-1,true,false>,<36,8,36,6,2,11,23,1,true,true>,
    <40,1,1,1,1,1,1,1,true,false>,<40,2,4,2,1,31,31,-1,false,false>,<40,3,5,2,1,9,9,1,true,false>,
    <40,4,8,2,1,21,21,1,true,false>,<40,5,40,2,1,19,19,-1,true,true>,<40,6,40,2,1,29,29,1,true,true>,
    <40,7,8,2,1,11,11,-1,true,false>,<40,8,20,2,1,39,39,-1,false,false>,<40,9,40,4,2,13,37,-1,true,true>,
    <40,10,20,4,2,7,23,1,false,false>,<40,11,40,4,2,3,27,1,true,true>,<40,12,5,4,2,17,33,-1,true,false>,
    <45,1,1,1,1,1,1,1,true,false>,<45,2,5,2,1,19,19,1,true,false>,<45,3,3,2,1,26,26,-1,true,false>,
    <45,4,15,2,1,44,44,-1,true,false>,<45,5,9,3,2,16,31,1,true,false>,<45,6,15,4,2,8,17,1,true,false>,
    <45,7,5,4,2,28,37,-1,true,false>,<45,8,45,6,2,14,29,-1,true,true>,<45,9,9,6,2,11,41,-1,true,false>,
    <45,10,45,6,2,4,34,1,true,true>,<45,11,45,12,4,7,43,-1,true,true>,<45,12,45,12,4,2,38,1,true,true>,
    <48,1,1,1,1,1,1,1,false,false>,<48,2,8,2,1,7,7,-1,false,false>,<48,3,12,2,1,47,47,1,true,false>,
    <48,4,8,2,1,25,25,1,false,false>,<48,5,3,2,1,17,17,-1,false,false>,<48,6,24,2,1,23,23,1,false,false>,
    <48,7,4,2,1,31,31,-1,true,false>,<48,8,24,2,1,41,41,-1,false,false>,<48,9,48,4,2,5,29,-1,true,true>,
    <48,10,16,4,2,13,37,1,true,false>,<48,11,48,4,2,11,35,1,true,true>,<48,12,16,4,2,19,43,-1,true,false>,
    <49,1,1,1,1,1,1,1,true,false>,<49,2,7,2,1,48,48,-1,true,false>,<49,3,7,3,2,18,30,1,false,false>,
    <49,4,7,6,2,19,31,-1,false,false>,<49,5,49,7,6,8,43,1,true,true>,<49,6,49,14,6,6,41,-1,true,true>,
    <49,7,49,21,12,2,46,1,true,true>,<49,8,49,42,12,3,47,-1,true,true>,<50,1,1,1,1,1,1,1,true,false>,
    <50,2,5,2,1,49,49,1,false,false>,<50,3,5,4,2,7,43,-1,true,false>,<50,4,25,5,4,11,41,1,true,false>,
    <50,5,25,10,4,9,39,1,true,false>,<50,6,25,20,8,3,47,-1,true,false>
];
for r in X do
    q := r[1]; o := r[2];
    assert ConreyCharacterOrbitRep(q,o) eq r[6];                        // LMFDB "first"
    assert MaximalConreyConjugate(q,r[6]) eq r[7];                      // LMFDB "last"
    assert ConreyCharacterOrbitIndex(q,r[6]) eq o and ConreyCharacterOrbitIndex(q,r[7]) eq o;
    assert CharacterOrbitOrder(q,o) eq r[4];
    assert CharacterOrbitDegree(CharacterOrbitLabel(q,o)) eq r[5];
    assert Parity(q,r[6]) eq r[8];
    assert IsMinimal(DirichletCharacter(q,r[6])) eq r[9];               // LMFDB is_minimal (BLS)
    assert ConreyCharacterOrbitLabel(q,r[6]) eq CharacterOrbitLabel(q,o);
end for;
for q in [13,24,25,32,36,40,45,48,49,50] do
    R := ConreyCharacterOrbitRepIndexes(q);
    assert R eq [r[6] : r in X | r[1] eq q];
    assert ConreyCharacterOrbitReps(q) eq [Sprintf("%o.%o",q,m) : m in R];
end for;
// optional-parameter filters against LMFDB data
assert ConreyCharacterOrbitRepIndexes(40:ParityEquals:=-1) eq [r[6] : r in X | r[1] eq 40 and r[8] eq -1];
assert ConreyCharacterOrbitRepIndexes(40:DegreeBound:=1) eq [r[6] : r in X | r[1] eq 40 and r[5] le 1];
assert ConreyCharacterOrbitRepIndexes(45:PrimitiveOnly:=true) eq [r[6] : r in X | r[1] eq 45 and r[10]];
assert ConreyCharacterOrbitRepIndexes(45:ConductorDivides:=15) eq [r[6] : r in X | r[1] eq 45 and 15 mod r[3] eq 0];
assert ConreyCharacterOrbitRepIndexes(45:ConductorBound:=9) eq [r[6] : r in X | r[1] eq 45 and r[3] le 9];
// OrderBound filter (regression: used to call builtin Order(q,n) and crash)
assert ConreyCharacterOrbitRepIndexes(40:OrderBound:=2) eq [r[6] : r in X | r[1] eq 40 and r[4] le 2];
assert ConreyCharacterOrbitRepIndexes(13:OrderBound:=2) eq [1,12];
// modulus 455 has 100 orbits: exercises the trace-fiber (IndexFibers) branch; spot values = LMFDB "first"
Y := ConreyCharacterOrbitRepIndexes(455);
assert #Y eq 100 and NumberOfCharacterOrbits(455) eq 100;
assert Y[1] eq 1 and Y[2] eq 181 and Y[9] eq 211 and Y[13] eq 148 and Y[25] eq 159 and Y[53] eq 318
   and Y[80] eq 3 and Y[99] eq 2 and Y[100] eq 227;
// string-label variants
assert ConreyCharacterOrbitIndex("13.9") eq 3;
assert ConreyCharacterValue("13.3",3) eq ConreyCharacterValue(13,3,3);
assert ConreyCharacterTrace("13.3",3) eq ConreyCharacterTrace(13,3,3);
assert ConreyCharacterTraces("13.3",[1..13]) eq ConreyCharacterTraces(13,3,[1..13]);
// RepTable combined with OrderBound (modulus 40 has 8 orbits of order <= 2 per LMFDB)
G8,T8 := CharacterOrbitReps(40:RepTable:=true,OrderBound:=2);
assert #G8 eq 8 and #Keys(T8) eq 8 and &and[Order(k) le 2 and IsConjugate(k,G8[T8[k]]) : k in Keys(T8)];
assert ConreyCharacterOrbitReps(4:PrimitiveOnly:=true) eq ["4.3"];

print "  Kronecker";
assert #KroneckerCharacterOrbits(1) eq 0 and #KroneckerCharacterOrbits(2) eq 0;
assert KroneckerCharacterOrbits(12) eq [<12,2>,<-3,3>,<-4,4>];  // LMFDB 12.b,12.c,12.d have conductors 12,3,4
assert KroneckerDiscriminant(DirichletGroup(1)!1) eq 1;
assert KroneckerDiscriminant(CyclotomicConreyCharacter(5,2)) eq 0;  // order 4 character
for M in [1..40] do
    P := KroneckerCharacterOrbits(M);
    DD := {d : d in [-M..M] | d ne 0 and IsFundamentalDiscriminant(d) and M mod Abs(d) eq 0};
    assert {r[1] : r in P} eq DD;
    G := DirichletGroup(M);
    for r in P do
        chi := G!KroneckerCharacter(r[1]);
        assert CharacterOrbitIndex(chi) eq r[2];
        assert KroneckerCharacterOrbit(r[1],M) eq r[2];
        assert KroneckerDiscriminant(chi) eq r[1];
    end for;
end for;

print "  ConreyLogs";
// least primitive roots mod p^2 (Conrey generators): standard values
assert [ConreyGenerator(p) : p in [3,5,7,11,13,23]] eq [2,2,3,2,2,5];
for e in [3..8] do
    R := Integers(2^e);
    for n in [n : n in [1..2^e-1] | IsOdd(n)] do
        a,s := ConreyLogModEvenPrimePower(e,n);
        assert s in {-1,1} and a ge 0 and a lt 2^(e-2) and R!n eq (R!s)*(R!5)^a;
    end for;
end for;
for p in [3,5,7], e in [1..3] do
    r := ConreyGenerator(p); R := Integers(p^e);
    for n in [n : n in [1..p^e] | n mod p ne 0] do
        x := ConreyLogModOddPrimePower(p,e,n);
        assert x ge 0 and x lt EulerPhi(p^e) and (R!r)^x eq R!n;
    end for;
end for;

print "  ConreyValues";
for q in [1..24] do
    U := [n : n in [1..q] | GCD(n,q) eq 1];
    S := [1..q+2];
    for n in U do
        chi := CyclotomicConreyCharacter(q,n);
        assert &and[ConreyCharacterValue(q,n,m) eq chi(m) : m in [1..q]];  // matches Magma Dirichlet character
        assert CharacterOrder(q,n) eq Order(chi) and Conductor(q,n) eq Conductor(chi);
        A := ConreyCharacterAngles(q,n,S);
        assert A eq [ConreyCharacterAngle(q,n,m) : m in S];                // batch = single
        T := ConreyCharacterTraces(q,n,S);
        assert T eq [ConreyCharacterTrace(q,n,m) : m in S];
        assert T eq [Integers()|Trace(ConreyCharacterValue(q,n,m)) : m in S];
        W := ConreyCharacterValues(q,n,S);
        assert &and[W[i] eq ConreyCharacterValue(q,n,S[i]) : i in [1..#S]];
        assert ConreyCharacterValues(q,n) eq [chi(u) : u in UnitGenerators(q)];
        assert CharacterValues(q,n) eq ConreyCharacterValues(q,n);
        assert CharacterValues(chi) eq [chi(u) : u in UnitGenerators(q)];
        if q gt 2 then assert CharacterAngles(chi) eq ConreyCharacterAngles(q,n); end if;
        // total multiplicativity and Conrey symmetry
        assert &and[ConreyCharacterValue(q,n,m) eq ConreyCharacterValue(q,m,n) : m in U];
        assert &and[ConreyCharacterValue(q,n,m1)*ConreyCharacterValue(q,n,m2) eq ConreyCharacterValue(q,n,m1*m2) : m1 in [1..q], m2 in [q-2..q]];
        // parity = chi(-1)
        if q gt 1 then assert ConreyCharacterValue(q,n,q-1) eq Codomain(chi)!Parity(q,n); end if;
    end for;
end for;

print "  Angles";
assert NormalizedAngle(0/1) eq 1 and NormalizedAngle(1/1) eq 1;
assert NormalizedAngle(-3/4) eq 1/4 and NormalizedAngle(7/4) eq 3/4;
// LMFDB chi_5(2,.): values at 2,3,4 are i,-i,-1, i.e. angles 1/4,3/4,1/2
assert ConreyCharacterAngle(5,2,2) eq 1/4 and ConreyCharacterAngle(5,2,3) eq 3/4 and ConreyCharacterAngle(5,2,4) eq 1/2;
assert ConreyCharacterAngle(4,3,3) eq 1/2;   // chi_4(3,3) = -1
assert Set(ConjugateAngles(ConreyCharacterAngles(7,3))) eq {ConreyCharacterAngles(7,3),ConreyCharacterAngles(7,5)};
assert #ConjugateAngles([1/13,3/13]) eq 12;  // acted on by (Z/13)^*, which has order 12

print "  CompareConreyCharacters";
for q in [7,9,15,16,21] do
    U := [n : n in [1..q] | GCD(n,q) eq 1];
    for n1 in U, n2 in U do
        c := CompareConreyCharacters(q,n1,n2);
        assert Sign(c) eq -Sign(CompareConreyCharacters(q,n2,n1));
        assert (c eq 0) eq IsConreyConjugate(q,n1,n2);
        if Order(Integers(q)!n1) eq Order(Integers(q)!n2) then
            assert Sign(CompareConreyCharacters(q,n1,n2,2)) eq Sign(c);
        end if;
    end for;
end for;

//=============================================================================
// Section 2: chars.m lines 627-1252 (values, invariants, products, twists, maps)
//=============================================================================

print "  ConreyCharacterAngles";
// fast (sequence) path must agree with single-value path, including m <= 0 and m not coprime
for q in [3,4,5,8,9,12,16,21,24,36,40] do
    S := [-7..12];
    for n in [n : n in [1..q] | GCD(q,n) eq 1] do
        assert ConreyCharacterAngles(q,n,S) eq [ConreyCharacterAngle(q,n,m) : m in S];
    end for;
end for;
// Conrey symmetry chi_q(n,m) = chi_q(m,n) and total multiplicativity
for q in [3..30] do
    U := [n : n in [1..q] | GCD(q,n) eq 1];
    for n in U, m in U do
        assert ConreyCharacterAngle(q,n,m) eq ConreyCharacterAngle(q,m,n);
    end for;
    n := U[#U];
    for m1 in U, m2 in U do
        assert ConreyCharacterAngle(q,n,(m1*m2) mod q) eq NormalizedAngle(ConreyCharacterAngle(q,n,m1)+ConreyCharacterAngle(q,n,m2));
    end for;
end for;
assert ConreyCharacterAngles("13.3") eq ConreyCharacterAngles(13,3);
assert CharacterAngles("13.3") eq ConreyCharacterAngles(13,3);
assert CharacterAngles(13,3) eq ConreyCharacterAngles(13,3);
assert ConreyCharacterAngles(16,5) eq ConreyCharacterAngles(16,5,UnitGenerators(16));

print "  ConreyCharacterComplexValue/RealValue/ComplexValues";
CC := ComplexField(30);  RR := RealField(30);
for q in [5,8,13,16,21] do
    for n in [n : n in [1..q] | GCD(q,n) eq 1] do
        for m in [-3..10] do
            a := ConreyCharacterAngle(q,n,m);
            z := ConreyCharacterComplexValue(q,n,m,CC);
            r := ConreyCharacterRealValue(q,n,m,RR);
            if GCD(q,m) eq 1 then
                assert Abs(z - Exp(2*Pi(CC)*CC.1*a)) lt 1e-20;
                assert Abs(r - Re(z)) lt 1e-20;
            else
                assert z eq 0 and r eq 0;
            end if;
        end for;
    end for;
end for;
V := ConreyCharacterComplexValues(13,3,[1..12],CC);
assert &and[Abs(V[m]-ConreyCharacterComplexValue(13,3,m,CC)) lt 1e-20 : m in [1..12]];

print "  ComplexConreyCharacter";
for q in [1..25] do
    for n in [n : n in [1..q] | GCD(q,n) eq 1] do
        xi := ComplexConreyCharacter(q,n,CC);  // has internal consistency assert
        for m in [2,3,5] do
            if GCD(q,m) eq 1 then assert Abs(xi(m) - ConreyCharacterComplexValue(q,n,m,CC)) lt 1e-20; end if;
        end for;
    end for;
end for;
xi := ComplexConreyCharacter("13.3",CC);
assert Abs(xi(2) - ConreyCharacterComplexValue(13,3,2,CC)) lt 1e-20;

print "  ConreyIndex/ConreyLabel roundtrip";
for q in [1..24] do
    for n in [n : n in [1..q] | GCD(q,n) eq 1] do
        chi := DirichletCharacter(q,n);
        assert Modulus(chi) eq q and ConreyIndex(chi) eq n;
        assert ConreyLabel(chi) eq Sprintf("%o.%o",q,n);
        assert DirichletCharacter(Sprintf("%o.%o",q,n)) eq chi;
        assert CyclotomicConreyCharacter(q,n) eq chi;
        assert CyclotomicConreyCharacter(Sprintf("%o.%o",q,n)) eq chi;
        assert DirichletCharacter(chi) eq chi;
    end for;
end for;

print "  CharacterOrder/Degree/IsReal/Parity/Conductor vs Magma builtins";
for q in [1..36] do
    for n in [n : n in [1..q] | GCD(q,n) eq 1] do
        chi := DirichletCharacter(q,n);
        assert Conductor(q,n) eq Conductor(chi);
        assert CharacterOrder(q,n) eq Order(chi);
        assert Parity(q,n) eq (IsOdd(chi) select -1 else 1);
        assert IsEven(q,n) eq IsEven(chi);
        assert IsOdd(q,n) eq IsOdd(chi);
        assert Degree(q,n) eq EulerPhi(Order(chi));
        assert IsReal(q,n) eq (Order(chi) le 2);
        assert IsPrimitiveCharacter(q,n) eq IsPrimitive(chi);
        s := Sprintf("%o.%o",q,n);
        assert CharacterOrder(s) eq Order(chi) and Parity(s) eq Parity(q,n);
        assert Conductor(s) eq Conductor(q,n) and Degree(s) eq Degree(q,n);
        assert IsReal(s) eq IsReal(q,n) and Modulus(s) eq q;
    end for;
end for;

print "  LMFDB char_dirichlet sample";
// SELECT modulus,conductor,"order",degree,first,is_even,is_minimal,is_primitive,is_real
// FROM char_dirichlet WHERE modulus IN (13,16,32,36,40,45,75,100) ORDER BY modulus,orbit; (LMFDB 2026-08-06)
// columns: [modulus,conductor,order,degree,first(=min Conrey index in orbit),is_even,is_minimal,is_primitive,is_real]
lmfdb := [
[13,1,1,1,1,1,1,0,1],[13,13,2,1,12,1,1,1,1],[13,13,3,2,3,1,1,1,0],[13,13,4,2,5,0,1,1,0],
[13,13,6,2,4,1,1,1,0],[13,13,12,4,2,0,1,1,0],[16,1,1,1,1,1,0,0,1],[16,8,2,1,9,1,0,0,1],
[16,4,2,1,15,0,1,0,1],[16,8,2,1,7,0,0,0,1],[16,16,4,2,5,1,1,1,0],[16,16,4,2,3,0,1,1,0],
[32,1,1,1,1,1,1,0,1],[32,8,2,1,17,1,0,0,1],[32,4,2,1,31,0,1,0,1],[32,8,2,1,15,0,0,0,1],
[32,16,4,2,9,1,0,0,0],[32,16,4,2,7,0,0,0,0],[32,32,8,4,5,1,1,1,0],[32,32,8,4,3,0,1,1,0],
[36,1,1,1,1,1,1,0,1],[36,12,2,1,35,1,1,0,1],[36,3,2,1,17,0,1,0,1],[36,4,2,1,19,0,1,0,1],
[36,9,3,2,13,1,1,0,0],[36,36,6,2,7,0,1,1,0],[36,9,6,2,5,0,1,0,0],[36,36,6,2,11,1,1,1,0],
[40,1,1,1,1,1,1,0,1],[40,4,2,1,31,0,0,0,1],[40,5,2,1,9,1,1,0,1],[40,8,2,1,21,1,1,0,1],
[40,40,2,1,19,0,1,1,1],[40,40,2,1,29,1,1,1,1],[40,8,2,1,11,0,1,0,1],[40,20,2,1,39,0,0,0,1],
[40,40,4,2,13,0,1,1,0],[40,20,4,2,7,1,0,0,0],[40,40,4,2,3,1,1,1,0],[40,5,4,2,17,0,1,0,0],
[45,1,1,1,1,1,1,0,1],[45,5,2,1,19,1,1,0,1],[45,3,2,1,26,0,1,0,1],[45,15,2,1,44,0,1,0,1],
[45,9,3,2,16,1,1,0,0],[45,15,4,2,8,1,1,0,0],[45,5,4,2,28,0,1,0,0],[45,45,6,2,14,0,1,1,0],
[45,9,6,2,11,0,1,0,0],[45,45,6,2,4,1,1,1,0],[45,45,12,4,7,0,1,1,0],[45,45,12,4,2,1,1,1,0],
[75,1,1,1,1,1,1,0,1],[75,5,2,1,49,1,0,0,1],[75,3,2,1,26,0,1,0,1],[75,15,2,1,74,0,0,0,1],
[75,15,4,2,32,1,1,0,0],[75,5,4,2,7,0,1,0,0],[75,25,5,4,16,1,1,0,0],[75,75,10,4,14,0,1,1,0],
[75,25,10,4,4,1,1,0,0],[75,75,10,4,11,0,1,1,0],[75,25,20,8,13,0,1,0,0],[75,75,20,8,2,1,1,1,0],
[100,1,1,1,1,1,1,0,1],[100,4,2,1,51,0,1,0,1],[100,5,2,1,49,1,0,0,1],[100,20,2,1,99,0,0,0,1],
[100,20,4,2,7,1,1,0,0],[100,5,4,2,57,0,1,0,0],[100,25,5,4,21,1,1,0,0],[100,100,10,4,19,0,1,1,0],
[100,25,10,4,9,1,1,0,0],[100,100,10,4,11,0,1,1,0],[100,25,20,8,13,0,1,0,0],[100,100,20,8,3,1,1,1,0]];
for r in lmfdb do
    q := r[1]; n := r[5];
    assert Conductor(q,n) eq r[2] and CharacterOrder(q,n) eq r[3] and Degree(q,n) eq r[4];
    assert IsEven(q,n) eq (r[6] eq 1) and IsMinimal(q,n) eq (r[7] eq 1);
    assert IsPrimitiveCharacter(q,n) eq (r[8] eq 1) and IsReal(q,n) eq (r[9] eq 1);
    assert IsPrimitiveCharacter(Sprintf("%o.%o",q,n)) eq (r[8] eq 1);  // regression: label version used to call builtin IsPrimitive(q,n)
    C := ConreyConjugates(q,n);
    assert #C eq r[4] and Min(C) eq n;
end for;

print "  IsMinimalConrey";
for q in [3..30] do
    for n in [n : n in [1..q] | GCD(q,n) eq 1] do
        chi := DirichletCharacter(q,n);
        b := IsMinimalSlow(chi);
        assert IsMinimal(q,n) eq b and IsMinimal(chi) eq b and IsMinimal(Sprintf("%o.%o",q,n)) eq b;
    end for;
end for;
assert IsMinimal(1,1) and IsMinimal("1.1");
// LMFDB: 8.7,24.7,25.24,27.10,40.31 are non-minimal; 8.3,8.5,16.15 are minimal
assert not IsMinimal(8,7) and not IsMinimal(24,7) and not IsMinimal(25,24) and not IsMinimal(27,10) and not IsMinimal(40,31);
assert IsMinimal(8,3) and IsMinimal(8,5) and IsMinimal(16,15);

print "  Factorization";
assert Factorization(1,1) eq [];
for q in [2..48] do
    for n in [n : n in [1..q] | GCD(q,n) eq 1] do
        F := Factorization(q,n);
        assert &*[Integers()|f[1]:f in F] eq q;
        assert &and[IsPrimePower(f[1]) and f[2] eq n mod f[1] : f in F];
        for m in [x : x in [1..q] | GCD(q,x) eq 1] do
            assert ConreyCharacterAngle(q,n,m) eq NormalizedAngle(&+[Rationals()|ConreyCharacterAngle(f[1],f[2],m):f in F]);
        end for;
    end for;
end for;
assert Factorization("45.2") eq ["9.2","5.2"];
// product of prime-power factors recovers q.n
for q in [12,40,45,72,100] do
    for n in [m:m in [1..q]|GCD(m,q) eq 1][1..4] do
        F := Factorization(q,n);
        qq := 1; nn := 1;
        for f in F do qq,nn := ConreyCharacterProduct(qq,nn,f[1],f[2]); end for;
        assert qq eq q and nn eq n mod q;
    end for;
end for;

print "  AssociatedCharacter";
assert AssociatedCharacter(12,4,3) eq 7;
assert AssociatedCharacter(12,"4.3") eq "12.7";
psi := AssociatedCharacter(12,DirichletCharacter("4.3"));
assert Modulus(psi) eq 12 and ConreyIndex(psi) eq 7;
for q in [4,5,8,9,16,25,27] do
    for n in [n : n in [1..q] | GCD(q,n) eq 1] do
        c := Conductor(q,n);
        for qq in [m : m in [1..60] | m mod c eq 0] do
            nn := AssociatedCharacter(qq,q,n);
            assert nn ge 1 and GCD(qq,nn) eq 1 and Conductor(qq,nn) eq c;
            L := LCM(q,qq);
            assert &and[ConreyCharacterAngle(qq,nn,m) eq ConreyCharacterAngle(q,n,m) : m in [1..L] | GCD(L,m) eq 1];
        end for;
    end for;
end for;
assert AssociatedCharacter(3,9,8) eq 2;   // restriction of conductor-3 char mod 9
assert AssociatedCharacter(4,16,15) eq 3; // restriction of conductor-4 char mod 16
assert AssociatedCharacter(8,16,15) eq 7; // 8.7 is induced from 4.3

print "  AssociatedPrimitiveCharacter";
for q in [1..40] do
    for n in [n : n in [1..q] | GCD(q,n) eq 1] do
        qq,nn := AssociatedPrimitiveCharacter(q,n);
        assert qq eq Conductor(q,n) and Conductor(qq,nn) eq qq;
        assert &and[ConreyCharacterAngle(qq,nn,m) eq ConreyCharacterAngle(q,n,m) : m in [1..q] | GCD(q,m) eq 1];
    end for;
end for;
assert AssociatedPrimitiveCharacter("45.2") eq "45.2";
assert AssociatedPrimitiveCharacter("45.a") eq "1.a";
assert AssociatedPrimitiveCharacter("100.57") eq "5.2";  // conductor 5, 57 mod 5 = 2

print "  ConreyCharacterProduct/ConductorProduct/ConductorProductBound";
for q1 in [1,4,5,8,9,16,27,36] do
    for q2 in [1,3,8,25,32] do
        for n1 in [n : n in [1..q1] | GCD(q1,n) eq 1] do
            for n2 in [n : n in [1..q2] | GCD(q2,n) eq 1] do
                q,n := ConreyCharacterProduct(q1,n1,q2,n2);
                assert q eq LCM(q1,q2) and GCD(q,n) eq 1;
                // product character has correct values
                assert &and[ConreyCharacterAngle(q,n,m) eq
                            NormalizedAngle(ConreyCharacterAngle(q1,n1,m)+ConreyCharacterAngle(q2,n2,m)) : m in [1..q] | GCD(q,m) eq 1];
                c := ConductorProduct(q1,n1,q2,n2);
                assert c eq Conductor(q,n);
                b := ConductorProductBound(Conductor(q1,n1),Conductor(q2,n2));
                assert c mod b eq 0;  // bound divides conductor as documented
            end for;
        end for;
    end for;
end for;
assert ConreyCharacterProduct("4.3","3.2") eq "12.11";
assert ConductorProduct("4.3","3.2") eq 12;
assert ConductorProduct("8.3","8.3") eq 1;

print "  PrimitiveConductorProduct";
prims := [[q,n] : n in [1..q], q in [1..24] | GCD(q,n) eq 1 and Conductor(q,n) eq q];
for r1 in prims, r2 in prims do
    assert PrimitiveConductorProduct(r1[1],r1[2],r2[1],r2[2]) eq ConductorProduct(r1[1],r1[2],r2[1],r2[2]);
end for;
assert PrimitiveConductorProduct("4.3","3.2") eq 12;

print "  ConreyInverse";
for q in [2..40] do
    for n in [n : n in [1..q] | GCD(q,n) eq 1] do
        ni := ConreyInverse(q,n);
        assert ni ge 1 and ni le q and (n*ni) mod q eq 1 mod q;
    end for;
end for;
assert ConreyInverse("5.2") eq "5.3";

print "  Twist";
// twisting level formula: twist of 11.1 by 4.3 has modulus LCM(11,4*4)=176 (level of quadratic twist of X_0(11) by -4)
q,n := Twist(11,1,4,3);
assert q eq 176 and n eq 1;
assert Twist("11.1","4.3") eq "176.1";
for pair in [[5,2,3,2],[7,3,4,3],[8,5,3,2],[9,2,8,3],[12,5,5,2],[16,3,5,3],[7,3,7,3]] do
    q1 := pair[1]; n1 := pair[2]; q2 := pair[3]; n2 := pair[4];
    q,n := Twist(q1,n1,q2,n2);
    assert Twist(Sprintf("%o.%o",q1,n1),Sprintf("%o.%o",q2,n2)) eq Sprintf("%o.%o",q,n);
    tchi := Twist(DirichletCharacter(q1,n1),DirichletCharacter(q2,n2));
    assert Modulus(tchi) eq q and ConreyIndex(tchi) eq n;
    // twisted character is chi*psi^2 (as characters, on integers coprime to everything)
    L := LCM([q1,q2,q]);
    assert &and[ConreyCharacterAngle(q,n,m) eq
                NormalizedAngle(ConreyCharacterAngle(q1,n1,m)+2*ConreyCharacterAngle(q2,n2,m)) : m in [1..L] | GCD(L,m) eq 1];
end for;

print "  Conjugates/ConreyConjugates/ConreyIndexes/ConreyLabels";
// LMFDB modulus 13 orbits: 13.a={1} 13.b={12} 13.c={3,9} 13.d={5,8} 13.e={4,10} 13.f={2,6,7,11}
assert ConreyConjugates(13,1) eq [1] and ConreyConjugates(13,12) eq [12];
assert ConreyConjugates(13,3) eq [3,9] and ConreyConjugates(13,5) eq [5,8];
assert ConreyConjugates(13,4) eq [4,10] and ConreyConjugates(13,2) eq [2,6,7,11];
assert ConreyConjugates("13.9") eq [3,9];
assert ConreyIndexes("13.f") eq [2,6,7,11];
assert ConreyLabels("13.c") eq ["13.3","13.9"];
assert ConreyConjugates(2,1) eq [1];
for q in [3..24] do
    seen := {};
    for n in [n : n in [1..q] | GCD(q,n) eq 1] do
        C := ConreyConjugates(q,n);
        assert n in C;
        chi := DirichletCharacter(q,n);
        assert ConreyIndexes(chi) eq C;
        conj := Conjugates(chi);
        assert #conj eq #C and Sort([ConreyIndex(c):c in conj]) eq C;
        assert ConreyLabels(chi) eq [Sprintf("%o.%o",q,m):m in C];
        assert ConreyIndexes(Sprintf("%o.%o",q,n)) eq C;
        seen join:= Set(C);
    end for;
    assert #seen eq EulerPhi(q);  // Galois orbits partition the characters
end for;
assert #Conjugates(DirichletCharacter("1.1")) eq 1;

print "  ConreyConjugates(chi,xi)";
for s in ["7.3","13.2","16.3","15.2"] do
    chi := DirichletCharacter(s);
    K := Codomain(chi);
    xi := map<Integers()->K|m:->chi(m)>;
    T := ConreyConjugates(chi,xi);
    q := Modulus(chi);
    assert #T eq Degree(K);
    for j in [1..#T], u in UnitGenerators(chi) do
        assert Abs(Conjugates(xi(u):Precision:=30)[j] - ConreyCharacterComplexValue(q,T[j],u,CC)) lt 1e-20;
    end for;
end for;
// bigger codomain than Q(chi): all embeddings still labeled correctly
chi := DirichletCharacter("5.2");
K := CyclotomicField(12);
xi12 := map<Integers()->K|m:->K!chi(m)>;
T := ConreyConjugates(chi,xi12);
assert #T eq 4 and Sort(SetToSequence(Set(T))) eq [2,3];

print "  TranslatedCharacterAngles";
for N in [3..20] do
    U := UnitGenerators(N);
    gm,pi := UnitGroup(Integers(N));
    for n in [n : n in [1..N] | GCD(N,n) eq 1] do
        V := ConreyCharacterAngles(N,n,U);
        assert TranslatedCharacterAngles(N,U,V,U) eq V;
        S := [Random(gm):i in [1..#U]];
        while sub<gm|S> ne gm do S := [Random(gm):i in [1..#U]]; end while;
        u := [Integers()!pi(s):s in S];
        if &and[(x mod N) ne 1:x in u] then
            assert TranslatedCharacterAngles(N,u,ConreyCharacterAngles(N,n,u),U) eq V;
        end if;
    end for;
end for;
// FLAGGED (audit 2026-08-06): the "if N le 2" early return in TranslatedCharacterAngles is
// unreachable (the require on generators fires first for N <= 2); dead code, no behavioral impact.

print "  DirichletCharacterFromAngles";
for N in [3..24] do
    U := UnitGenerators(N);
    for n in [n : n in [1..N] | GCD(N,n) eq 1] do
        v := ConreyCharacterAngles(N,n);
        chi := DirichletCharacterFromAngles(N,U,v);
        assert chi eq DirichletCharacterFromAngles(N,v);
        assert ConreyIndex(chi) eq n;
    end for;
end for;
// non-standard generators: 6 generates (Z/13)*, [7,3] generates (Z/16)*
chi := DirichletCharacterFromAngles(13,[6],ConreyCharacterAngles(13,2,[6]));
assert ConreyIndex(chi) eq 2;
chi := DirichletCharacter(16,3);
psi := DirichletCharacterFromAngles(16,[7,3],ConreyCharacterAngles(16,3,[7,3]));
assert &and[psi(m) eq chi(m):m in [1..16]];
assert DirichletCharacterFromAngles(1,[Integers()|],[Rationals()|]) eq DirichletGroup(1)!1;

print "  SquareRoots";
for N in [3..16] do
    G := FullDirichletGroup(N);
    E := Elements(G);
    for chi in E do
        S := SquareRoots(chi);
        assert #S eq #[psi : psi in E | psi^2 eq chi];
        assert &and[psi^2 eq chi : psi in S];
    end for;
end for;

print "  CharacterFromValues";
for s in ["7.3","13.2","16.3","15.14","5.4"] do
    chi := DirichletCharacter(s);
    N := Modulus(chi);
    u := UnitGenerators(N);
    psi, o := CharacterFromValues(N,u,[chi(x):x in u]:Orbit:=true);
    assert &and[psi(m) eq chi(m) : m in [1..N]];
    assert o eq CharacterOrbitIndex(chi);
end for;
psi,o := CharacterFromValues(2,[Integers()|],[Rationals()|]:Orbit:=true);
assert o eq 1 and psi(3) eq 1 and psi(2) eq 0;

print "  CharacterOrder/Conductor/Parity/IsReal for maps";
for s in ["7.3","13.2","16.3","15.14","9.8","13.12","13.1","16.15","11.2"] do
    chi := DirichletCharacter(s);
    N := Modulus(chi);
    xi := map<Integers()->Codomain(chi)|m:->chi(m)>;
    assert CharacterOrder(xi,N) eq Order(chi);
    assert Conductor(xi,N) eq Conductor(chi);
    assert Parity(xi) eq (IsOdd(chi) select -1 else 1);
    assert IsReal(xi,N) eq (Order(chi) le 2);
    assert Degree(xi,N) eq EulerPhi(Order(chi));
end for;
// Degree(xi,N) for cyclotomic codomain of degree > 1
chi := DirichletCharacter("7.3");  // order 6, Q(chi)=Q(zeta_6) has degree 2
xi := map<Integers()->Codomain(chi)|m:->chi(m)>;
assert Degree(xi,7) eq 2;

print "  ConreyOrbitTable/ConreyOrbitLabelTable";
// orbit data for modulus 13 from LMFDB char_dirichlet (verified 2026-08-06)
fn := "/tmp/test_chars_orbit_table_input.txt";
Write(fn,"13:1:[1]\n13:2:[12]\n13:3:[3,9]\n13:4:[5,8]\n13:5:[4,10]\n13:6:[2,6,7,11]\n14:1:[1]\n":Overwrite:=true);
T := ConreyOrbitTable(fn,13);
assert T[13][1] eq 1 and T[13][12] eq 2 and T[13][3] eq 3 and T[13][9] eq 3;
assert T[13][5] eq 4 and T[13][8] eq 4 and T[13][4] eq 5 and T[13][10] eq 5;
assert &and[T[13][n] eq 6 : n in [2,6,7,11]];
TL := ConreyOrbitLabelTable(fn,13);
assert TL[13][1] eq "13.a" and TL[13][12] eq "13.b" and TL[13][3] eq "13.c" and TL[13][9] eq "13.c";
assert TL[13][5] eq "13.d" and TL[13][4] eq "13.e" and &and[TL[13][n] eq "13.f" : n in [2,6,7,11]];
System("rm -f " cat fn);

print "  ConreyCharacterFromLabel/Modulus";
q,n := ConreyCharacterFromLabel("13.3");  assert q eq 13 and n eq 3;
q,n := ConreyCharacterFromLabel("13.c");  assert q eq 13 and n eq 3;  // minimal rep of orbit {3,9}
assert Modulus("13.3") eq 13 and Modulus("13.c") eq 13 and Modulus("1.1") eq 1;
assert CharacterOrder("13.c") eq 3 and CharacterOrder("13.f") eq 12;
assert Degree("13.f") eq 4 and Conductor("13.c") eq 13 and Parity("13.f") eq -1;
assert Parity("13.b") eq 1;  // quadratic character mod 13 is even (13 = 1 mod 4)
assert IsReal("13.b") and not IsReal("13.c");

print "  NewModularSymbols";
M := NewModularSymbols("11.1",2);   // S_2(Gamma_0(11))^new has dimension 1 (11.2.a.a)
assert Dimension(M) eq 1;
assert Dimension(NewModularSymbols("11.2.a")) eq 1;
assert Dimension(NewModularSymbols("23.2.a")) eq 2;  // S_2(Gamma_0(23))^new has dimension 2

//=============================================================================
// Section 3: regressions for bugs fixed in the 2026-08-06 audit
//=============================================================================

print "  RegressionIsCyclic";
// BUG (fixed): IsCyclic(N) returned true for N = 2^e >= 8 ((Z/2^eZ)* = C2 x C2^(e-2) is not cyclic)
assert not IsCyclic(8) and not IsCyclic(16) and not IsCyclic(32) and not IsCyclic(64) and not IsCyclic(128);
assert IsCyclic(1) and IsCyclic(2) and IsCyclic(4) and IsCyclic(27) and IsCyclic(54) and IsCyclic(23);
assert &and[IsCyclic(N) eq IsCyclic(MultiplicativeGroup(Integers(N))) : N in [201..300]];

print "  RegressionIsMinimalSlowModulus1";
// BUG (fixed): IsMinimalSlow crashed on the modulus-1 trivial character (IsPrimePower(1) error)
assert IsMinimalSlow(DirichletGroup(1)!1);

print "  RegressionLabelAnchors";
// BUG (fixed): unanchored Regexp accepted any string containing a label substring
assert not IsCharacterLabel("x13.5y") and not IsCharacterLabel("13.5.7") and not IsCharacterLabel(" 13.5");
assert not IsCharacterOrbitLabel("13.c.7") and not IsCharacterOrbitLabel("x13.c");
assert IsCharacterLabel("13.5") and IsCharacterOrbitLabel("13.c");

print "  RegressionOrderBound1Container";
// BUG (fixed): CharacterOrbitReps with OrderBound=1 returned a SeqEnum instead of a List
assert Type(CharacterOrbitReps(20:OrderBound:=1)) eq List;
GG,TT := CharacterOrbitReps(20:OrderBound:=1,RepTable:=true);
assert Type(GG) eq List and #GG eq 1 and Order(GG[1]) eq 1 and TT[GG[1]] eq 1;

print "  RegressionIsConreyConjugateLabels";
// BUG (fixed): label version passed 4 arguments to the 3-argument intrinsic (always errored on equal moduli)
assert IsConreyConjugate("7.2","7.4") and not IsConreyConjugate("7.2","7.3");
assert not IsConreyConjugate("7.2","5.2");
assert IsConjugate("7.2","7.4") and not IsConjugate("7.2","7.6");

print "  RegressionPrimitiveOnlyRequires";
// BUG (fixed): PrimitiveOnly sanity requires were vacuous (ConductorBound) and inverted (ConductorDivides)
assert ConreyCharacterOrbitReps(5:PrimitiveOnly:=true,ConductorDivides:=10) eq ConreyCharacterOrbitReps(5:PrimitiveOnly:=true);
assert ConreyCharacterOrbitReps(5:PrimitiveOnly:=true,ConductorBound:=5) eq ConreyCharacterOrbitReps(5:PrimitiveOnly:=true);
assert mustfail(func<|ConreyCharacterOrbitReps(5:PrimitiveOnly:=true,ConductorDivides:=3)>);
assert mustfail(func<|ConreyCharacterOrbitReps(5:PrimitiveOnly:=true,ConductorBound:=3)>);
// BUG (fixed): q=2 with PrimitiveOnly returned [2.1], but 2.1 has conductor 1 (no primitive character mod 2)
assert ConreyCharacterOrbitReps(2:PrimitiveOnly:=true) eq [];
assert ConreyCharacterOrbitReps(1:PrimitiveOnly:=true) eq ["1.1"];

print "  RegressionOrderBoundFilter";
// BUG (fixed): OrderBound filter called builtin Order(q,n) (order of q mod n) instead of CharacterOrder(q,n)
assert ConreyCharacterOrbitRepIndexes(13:OrderBound:=2) eq [1,12];
assert ConreyCharacterOrbitReps(40:OrderBound:=2) eq [s : s in ConreyCharacterOrbitReps(40) | CharacterOrder(s) le 2];

print "  RegressionConreyCharacterValuesUniverse";
// BUG (fixed): q=1 returned a sequence with universe Z instead of a cyclotomic field
assert Type(Universe(ConreyCharacterValues(1,1,[1,2,3]))) eq FldCyc;
assert ConreyCharacterValues(1,1,[1,2,3]) eq [1,1,1];

print "  RegressionIsPrimitiveCharacterLabel";
// BUG (fixed): label version called builtin IsPrimitive(q,n) (primitive-root test) and always errored
assert IsPrimitiveCharacter("5.4") and IsPrimitiveCharacter("8.5") and IsPrimitiveCharacter("1.1");
assert not IsPrimitiveCharacter("8.7") and not IsPrimitiveCharacter("2.1") and not IsPrimitiveCharacter("45.44");

print "  RegressionMapIntrinsicsSmallModulus";
// BUG (fixed): CharacterOrder(xi,N) and Conductor(xi,N) crashed for N <= 2 (empty generator list)
xi1 := CharacterFromValues(1,[Integers()|],[Rationals()|]);
xi2 := CharacterFromValues(2,[Integers()|],[Rationals()|]);
assert CharacterOrder(xi1,1) eq 1 and CharacterOrder(xi2,2) eq 1;
assert Conductor(xi1,1) eq 1 and Conductor(xi2,2) eq 1;
assert IsReal(xi1,1) and IsReal(xi2,2);

print "  RegressionConductorMap";
// BUG (fixed): Conductor(xi,N) rejected the true conductor M when some u+r*M was not coprime to N
// (e.g. returned 15 instead of 5 for the character 15.4), and leaked Min's second return value
for s in ["15.4","45.19","45.29","21.4","33.4","35.13"] do
    chi := DirichletCharacter(s);
    N := Modulus(chi);
    U := UnitGenerators(N);
    xi := CharacterFromValues(N,U,[Codomain(chi)|chi(u):u in U]);
    assert Conductor(xi,N) eq Conductor(chi);
end for;
// exhaustive check against Magma's builtin Conductor for all characters of modulus <= 40
for N in [3..40] do
    U := UnitGenerators(N);
    for chi in Elements(FullDirichletGroup(N)) do
        xi := CharacterFromValues(N,U,[Codomain(chi)|chi(u):u in U]);
        assert Conductor(xi,N) eq Conductor(chi);
    end for;
end for;

print "  RegressionDegreeMapRationalCodomain";
// BUG (fixed): Degree(xi,N) returned 2 for a nontrivial character with rational codomain
// (image {1,-1} generates Q, which has degree 1, matching Degree(q,n) and the general branch)
chi := DirichletCharacter(16,15);
U := UnitGenerators(16);
xiQ := CharacterFromValues(16,U,[Rationals()|chi(u):u in U]);
assert Degree(xiQ,16) eq 1;
xiK := CharacterFromValues(16,U,[CyclotomicField(4)|chi(u):u in U]);
assert Degree(xiK,16) eq 1;

print "  RegressionAssociatedCharacter2Adic";
// BUG (fixed): for n = -5^0 mod 2^e (conductor 4, e.g. 8.7, 16.15) the divisibility require passed
// vacuously and a wrong index was returned for target moduli with v_2(qq) <= 1
assert mustfail(func<|AssociatedCharacter(1,8,7)>);
assert mustfail(func<|AssociatedCharacter(2,8,7)>);
assert mustfail(func<|AssociatedCharacter(3,8,7)>);
assert mustfail(func<|AssociatedCharacter(6,8,7)>);
assert mustfail(func<|AssociatedCharacter(3,16,15)>);
assert mustfail(func<|AssociatedCharacter(6,24,23)>);
assert AssociatedCharacter(4,8,7) eq 3 and AssociatedCharacter(12,24,23) eq 11;
// exhaustive: call succeeds iff conductor divides target modulus, and the result is correct
for q in [4,8,16,32] do
    for n in [n:n in [1..q]|GCD(q,n) eq 1] do
        c := Conductor(q,n);
        for qq in [1..48] do
            ok := true;
            try nn := AssociatedCharacter(qq,q,n); catch e ok := false; end try;
            assert ok eq IsDivisibleBy(qq,c);
            if ok then assert GCD(qq,nn) eq 1 and Conductor(qq,nn) eq c; end if;
        end for;
    end for;
end for;

print "  RegressionConreyInverseModulus1";
// BUG (fixed): ConreyInverse(1,1) crashed (negative power of zero element in Integers(1))
assert ConreyInverse(1,1) eq 1 and ConreyInverse("1.1") eq "1.1";

print "  RegressionComplexValuesNonCoprime";
// BUG (fixed): ConreyCharacterComplexValues returned 1 instead of 0 at m with gcd(m,q) > 1
V := ConreyCharacterComplexValues(5,2,[1,2,5,10],CC);
assert V[3] eq 0 and V[4] eq 0 and Abs(V[1]-1) lt 1e-20 and Abs(V[2]-CC.1) lt 1e-20;
for t in [<7,3>,<16,3>,<40,7>] do
    W := ConreyCharacterComplexValues(t[1],t[2],[1..t[1]],CC);
    assert &and[Abs(W[m]-ConreyCharacterComplexValue(t[1],t[2],m,CC)) lt 1e-20 : m in [1..t[1]]];
end for;

print "  RegressionSquareRootsAmbientGroup";
// BUG (fixed): SquareRoots crashed instead of returning only square roots in the ambient group
G := DirichletGroup(5);   // rational coefficient ring: quadratic character has no square root here
assert SquareRoots(G.1) eq [Parent(G.1)|];
G12 := DirichletGroup(12);
assert Set(SquareRoots(G12!1)) eq {psi : psi in Elements(G12) | psi^2 eq G12!1};

print "  RegressionTypedSignatures";
// BUG (fixed): DirichletCharacter(chi:GrpDrchElt), ConreyCharacterAngles(s:MonStgEt) and
// CharacterAngles(s:MonStgEt) had untyped arguments (single colon / typo) and accepted anything
assert mustfail(func<|DirichletCharacter(42)>);
assert mustfail(func<|ConreyCharacterAngles(1.5)>);
assert mustfail(func<|CharacterAngles([1,2,3])>);
assert DirichletCharacter(DirichletCharacter("13.3")) eq DirichletCharacter(13,3);

print "  RegressionConreyConjugatesModulus1";
// BUG (fixed): ConreyConjugates(1,1) crashed (Order of zero element of Integers(1))
assert ConreyConjugates(1,1) eq [1] and ConreyConjugates("1.1") eq [1];
assert ConreyIndexes("1.1") eq [1] and ConreyLabels("1.1") eq ["1.1"];

print "ALL TESTS PASSED test_chars.m";
quit;
