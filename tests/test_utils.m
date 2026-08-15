AttachSpec("magma.spec");
SetSeed(1);
print "test_utils.m";

//
// ===== Auditor fragments (lines 1-660) =====
//

print "  ProfileTimes";
SetProfile(true); _ := &+[n^2 : n in [1..1000]];
assert Type(ProfileTimes()) eq SeqEnum; // also calls SetProfile(false)

print "  Factorization(FldRatElt)";
assert Factorization(3/4) eq [<2,-2>,<3,1>];
assert Factorization(-6/35) eq [<2,1>,<3,1>,<5,-1>,<7,-1>];
assert Factorization(7/2) eq [<2,-1>,<7,1>];

print "  GSp";
assert #GSp(4,3) eq #Sp(4,3)*2;    // |GSp(2g,q)| = (q-1)*|Sp(2g,q)|
assert #GSp(2,5) eq #SL(2,5)*4;

print "  PlaneCurve";
c := [1,0,0,1,0,0,0,0,1,1];        // 10 = binom(3+2,2) coefficients: a cubic
C := PlaneCurve(c);
assert Degree(C) eq 3 and Coefficients(C) eq c;   // documented roundtrip
c2 := [Rationals()|1,2,3,4,5,6];
assert Coefficients(PlaneCurve(c2)) eq c2;
RQ<u,v,w> := PolynomialRing(Rationals(),3);
assert Genus(PlaneCurve(u^4+v^4+w^4)) eq 3;

print "  Eltseq(SetMulti)";
assert Eltseq({*3,1,1,2*}) eq [<1,2>,<2,1>,<3,1>];

print "  ReplaceCharacter";
assert ReplaceCharacter("a:b",":",";;") eq "a;;b";
assert ReplaceCharacter(":ab",":","") eq "ab";
assert ReplaceCharacter("abc","z","w") eq "abc";
// REGRESSION (audit 2026-08-06): trailing delimiter used to yield an extra copy of d
// (double-append of trailing empty, Split:IncludeEmpty already includes it as of Magma 2.29),
// and the empty string used to crash (s[#s] out of range).
assert ReplaceCharacter("a:b:",":",";") eq "a;b;";
assert ReplaceCharacter("a:",":","XY") eq "aXY";
assert ReplaceCharacter("","a","b") eq "";

print "  ReplaceString";
assert ReplaceString("aaa","aa","a") eq "aa";     // python "aaa".replace("aa","a")
assert ReplaceString("abcabc","bc","X") eq "aXaX";
assert ReplaceString("abc","c","XY") eq "abXY";
assert ReplaceString("abc","q","X") eq "abc";

print "  djb2";
assert djb2("a":b:=8) eq (5381*33+97) mod 256;
assert djb2("":b:=16) eq 5381 mod 2^16;
h := 5381; for ch in Eltseq("hello world") do h := (33*h + StringToCode(ch)) mod 2^64; end for;
assert djb2("hello world") eq h;

print "  PySplit";
assert PySplit("a:b:c",":") eq ["a","b","c"];       // python 'a:b:c'.split(':')
assert PySplit("aaa","aa") eq ["","a"];             // python 'aaa'.split('aa')
assert PySplit("a::b","::") eq ["a","b"];
assert PySplit(":a:",":") eq ["","a",""];
assert PySplit("","x") eq [""];
assert PySplit("a:b:c:d",":":limit:=2) eq ["a","b","c:d"];  // maxsplit=2
// NOTE (audit 2026-08-06): PySplit with limit < -1 behaves as limit 0, whereas Python
// treats any negative maxsplit as unlimited (limit is an undocumented optional).

print "  split";
assert split("a:b:c",":") eq ["a","b","c"];
assert split("a::b",":") eq ["a","","b"];
assert split(":a",":") eq ["","a"];
// REGRESSION (audit 2026-08-06): strings ending in the delimiter used to gain a spurious
// extra empty field (double-append of trailing empty), and split("",d) used to crash.
// Python semantics per the docstring:
assert split("a:b:",":") eq ["a","b",""];   // python 'a:b:'.split(':')
assert split(":",":") eq ["",""];           // python ':'.split(':')
assert split("",":") eq [""];               // python ''.split(':')
assert split("::","::") eq ["","",""];      // Magma Split treats d as a set of delimiter chars

print "  getrecs/putrecs";
tmpf_aud1 := "/tmp/test_utils_recs.txt";
recs := [["a","b","c"],["1","","3"]];
putrecs(tmpf_aud1,recs);
assert getrecs(tmpf_aud1) eq recs;
// REGRESSION (audit 2026-08-06): records with a trailing empty field used to gain a
// spurious extra column on read (consequence of the split bug above).
recs := [["a","b",""],["1","","2"],["x","",""]];
putrecs(tmpf_aud1,recs);
assert getrecs(tmpf_aud1) eq recs;

print "  maxcerts";
S4 := {1,2,3,4};
for Ts in [[{1,2},{3},{2,4}],[{1,2,3}],[{1},{2},{3},{4}]] do
    A := maxcerts(S4,Ts:Limit:=4);
    allsub := &cat[[s:s in Subsets(S4,i)]:i in [0..4]];
    cert := func<s|&and[not s subset T:T in Ts]>;
    B := [s:s in allsub|cert(s) and &and[not cert(t):t in allsub|t subset s and t ne s]];
    assert Set(A) eq Set(B) and #A eq #B;   // exactly the minimal certificates
end for;

print "  StringToStrings";
assert StringToStrings("[cat,dog]") eq ["cat","dog"];
assert StringToStrings(" [ a , b ] ") eq ["a","b"];

print "  sum/prod";
assert sum([Integers()|]) eq 0 and sum([]) eq 0 and sum([1,2,3]) eq 6 and sum([1/2,1/3]) eq 5/6;
assert prod([Integers()|]) eq 1 and prod([]) eq 1 and prod([2,3,4]) eq 24;
assert sum(Vector([1,2,3])) eq 6 and prod(Vector([2,3])) eq 6;

print "  strip/sprint";
assert strip(" a b c ") eq "abc";
assert sprint([1,2,3]) eq "[1,2,3]";
AS := AssociativeArray(Universe(["x"])); AS["b"]:="2"; AS["a"]:="1";
assert sprint(AS) eq "a=1:b=2";

print "  atoi/itoa/StringToReal/atof";
assert atoi("-123") eq -123 and atoi("") eq 0 and itoa(-45) eq "-45";
assert StringToReal("123.456") eq 123.456;
assert Abs(StringToReal("1.23456e-10")-1.23456e-10) lt 1e-25;
assert Abs(StringToReal("-12.034")+12.034) lt 1e-9;   // fractional digits with leading zero
assert StringToReal("-0.5") eq -0.5 and StringToReal("1e3") eq 1000.0 and StringToReal("") eq 0.0;
assert atof("2.5") eq 2.5;

print "  StringsToAssociativeArray";
DA := atod(["a=1","b=2","junk","c=d=e"]);
assert Keys(DA) eq {"a","b"} and DA["a"] eq "1" and DA["b"] eq "2";

print "  IntegerArrayParsing";
assert StringToIntegerArray("[4,5]") eq [4,5];
assert atoii("[]") eq [Integers()|] and atoii("[-1,2,3]") eq [-1,2,3] and atoii(" [ 1 , -2 ]") eq [1,-2];
assert iitoa([-1,2]) eq "[-1,2]" and atoii(iitoa([-5,0,7])) eq [-5,0,7];
assert atoiii("[]") eq [] and atoiii("[[]]") eq [[Integers()|]];
assert atoiii("[[1,2],[3]]") eq [[1,2],[3]] and atoiii("[[],[-1]]") eq [[Integers()|],[-1]];
assert atoiii("[<1,2>,<3,4>]") eq [[1,2],[3,4]] and atoiii("[<1>,<>]") eq [[1],[Integers()|]];
assert atoiii(sprint([[1],[2,3]])) eq [[1],[2,3]];
// REGRESSION (audit 2026-08-06): atoiii("[<>]") used to fail the length assertion (#t gt 4)
// even though the tuple branch parses it fine.
assert atoiii("[<>]") eq [[Integers()|]];
assert atoiiii("[[[1,2],[3]],[[4]]]") eq [[[1,2],[3]],[[4]]];
assert atoiiii(sprint(xx)) eq xx where xx := [[[1],[2,3]],[[4,5],[6]],[[7]]];
assert atoiiii("[]") eq [] and atoiiii("[[]]") eq [[Integers()|]] and atoiiii("[[[]]]") eq [[[Integers()|]]];
// REGRESSION (audit 2026-08-06): atoiiii parsed the unstripped string, so interior
// whitespace silently collapsed the nesting depth (wrong shape, no error).
assert atoiiii("[[[1]], [[2]]]") eq [[[1]],[[2]]];
assert atoiiii(" [ [[1,2],[3]], [[4]] ] ") eq [[[1,2],[3]],[[4]]];

print "  RealRationalArrayParsing";
assert StringToRationalArray("[1/2,-3,4/6]") eq [1/2,-3,2/3];
assert StringToRationalArray("[]") eq [];
assert StringToRealArray("[0.5,1.25]") eq [0.5,1.25];
assert atoff("[1.5,-2.25]") eq [1.5,-2.25];
assert atofff("[[1.5],[-2.0,0.5]]") eq [[1.5],[-2.0,0.5]] and atofff("[[]]") eq [[RealField()|]];

print "  goodp";
Rx<x> := PolynomialRing(Integers());
assert goodp(x^2+1,2) eq false and goodp(x^2+1,3) eq true;         // disc = -4
assert goodp((x-1)*(x-3),2) eq false and goodp(x^3-x+1,23) eq false; // disc(x^3-x+1) = -23
assert goodp(x^3-x+1,5) eq true;

print "  Base26";
assert Base26Encode(0) eq "a" and Base26Encode(25) eq "z" and Base26Encode(26) eq "ba";
assert Base26Encode(675) eq "zz" and Base26Encode(676) eq "baa" and Base26Encode(702) eq "bba";
assert forall{n : n in [0..1000] | Base26Decode(Base26Encode(n)) eq n};

print "  PolycyclicPresentation";
U,pi := UnitGroup(Integers(117));
pgens := [pi(U.i):i in [1..Ngens(U)]];
r,fexp := PolycyclicPresentation(pgens,func<a,b|a*b>,Integers(117)!1);
assert &*r eq #U;
assert forall{uu : uu in U | &*[pgens[i]^vv[i]:i in [1..#pgens]] eq xu where vv := fexp(xu) where xu := pi(uu)};

print "  OrderStats";
for invs in [[2,4],[3,9],[2,2,2],[4,6],[2,4,8]] do    // exercises the abelian fast path
    G := AbelianGroup(GrpPerm,invs);
    assert OrderStats(G) eq {* Order(g) : g in G *};
end for;
assert OrderStats(SymmetricGroup(4)) eq {* Order(g) : g in Sym(4) *};  // generic path
assert OrderStats(CyclicGroup(1)) eq {*1*};
assert OrderStats(AbelianGroup([2,4])) eq {* 1, 2^^3, 4^^4 *};         // GrpAb input

print "  CyclicGenerators";
for invs in [[2,4],[4,6],[8],[2,2,2],[2,4,4]] do
    G := AbelianGroup(invs);
    cg := CyclicGenerators(G);
    assert #cg eq #{sub<G|g>:g in G} and #{sub<G|g>:g in cg} eq #cg;  // one generator per cyclic subgroup
end for;

print "  ConjugateIntersectionCompositum";
G := SymmetricGroup(4);
H1 := Sylow(G,2); H2 := sub<G|(1,2,3)>;
assert #ConjugateIntersection(G,H1,H2) eq Max([#(a meet b):a in Conjugates(G,H1), b in Conjugates(G,H2)]);
assert #ConjugateCompositum(G,H1,H2) eq Min([#sub<G|a,b>:a in Conjugates(G,H1), b in Conjugates(G,H2)]);

print "  getval";
AA := AssociativeArray(); AA[1] := 10;
assert getval(AA,1) eq 10 and getval(AA,2) eq [] and getval(AA,3:missing:=-7) eq -7;
// REGRESSION (audit 2026-08-06): getval crashed on sequences (two-value IsDefined only
// exists for associative arrays), contradicting the X::Any signature and Python-get docs.
assert getval([1,2,3],2) eq 2;
assert getval([1,2,3],7) eq [];
assert getval([1,2,3],7:missing:=-1) eq -1;

print "  IndexFibers";
FI := IndexFibers([1..20],func<n|n mod 3>);
assert FI[0] eq [3..18 by 3] and FI[1] eq [1..19 by 3];
assert IndexFibers([1..5],func<n|n>:Unique)[3] eq 3;
assert IndexFibers([1..10],func<n|n mod 2>:Project:=func<n|n^2>)[1] eq [1,9,25,49,81];
assert IndexFibers([* "a","bb","cc" *],func<s|#s>)[2] eq ["bb","cc"];

print "  IndexFile";
putrecs(tmpf_aud1,[["a","1","x"],["b","2","y"]]);
assert IndexFile(tmpf_aud1,1:Unique)["a"] eq ["a","1","x"];
assert IndexFile(tmpf_aud1,1:Unique,data:=2)["b"] eq "2";
assert IndexFile(tmpf_aud1,[1,2]:Unique,data:=3)[["a","1"]] eq "x";

print "  ReduceToRepsClassify";
E5 := func<a,b|a mod 5 eq b mod 5>;
RR := ReduceToReps([1..20],E5);
assert #RR eq 5 and Sort([r mod 5:r in RR]) eq [0..4];
assert Sort(ReduceToReps([1..20],E5:min:=func<a,b|Min(a,b)>)) eq [1..5];
assert ReduceToReps([3,8],E5:min:=func<a,b|Min(a,b)>) eq [3];
CL := Classify([1..20],E5);
assert #CL eq 5 and forall{cc:cc in CL|#cc eq 4} and Sort(&cat CL) eq [1..20];
assert Classify([Integers()|],E5) eq [] and Classify([7],E5) eq [[7]];

print "  DihedralGroupGrpAb";
for n in [3..6] do assert IsIsomorphic(DihedralGroup(AbelianGroup([n])),DihedralGroup(n)); end for;
DD := DihedralGroup(AbelianGroup([2,2]));   // inversion trivial: get G x Z/2
assert #DD eq 8 and IsIsomorphic(DD,AbelianGroup(GrpPerm,[2,2,2]));
assert not IsAbelian(DihedralGroup(AbelianGroup([2,4])));

print "  Quotients";
assert [#q:q in Quotients(SymmetricGroup(3))] eq [2];
assert Sort([#q:q in Quotients(DihedralGroup(4))]) eq [2,2,2,4];
assert #Quotients(DihedralGroup(4):Order:=2) eq 3;

print "  RandomizeForms";
R3<x3,y3,z3> := PolynomialRing(Integers(),3);
f3 := x3^4+y3^4+z3^4; g3 := x3^2*y3^2-z3^4;
FF := RandomizeForms([f3,g3,f3+g3]);
assert FF[3] eq FF[1]+FF[2];                            // same transform applied to all
assert forall{hh:hh in FF|IsHomogeneous(hh) and TotalDegree(hh) eq 4};
h3 := RandomizeForm(f3); assert IsHomogeneous(h3) and TotalDegree(h3) eq 4 and h3 ne 0;

print "  MinimizeGenerators";
G := AbelianGroup(GrpPerm,[2,4,8]);
assert #MinimizeGenerators(G) eq #G;
G2 := DirectProduct(SymmetricGroup(3),CyclicGroup(4));
H2m := MinimizeGenerators(G2); assert #H2m eq #G2 and Ngens(H2m) le 2;

print "  RegularRepresentation";
for G in [CyclicGroup(6),SymmetricGroup(4)] do
    H := RegularRepresentation(G);
    assert Degree(H) eq #G and IsIsomorphic(H,G);
end for;

print "  HurwitzClassNumber";
// literature values in Zagier's convention (H(0)=-1/12, H(3)=1/3, H(4)=1/2)
assert [HurwitzClassNumber(n):n in [0,3,4,7,8,11,12,15,16,19,20,23,24]] eq [-1/12,1/3,1/2,1,1,1,4/3,2,3/2,1,2,3,2];
assert HurwitzClassNumber(1) eq 0 and HurwitzClassNumber(2) eq 0 and HurwitzClassNumber(100) eq 5/2;
// Hurwitz-Kronecker/Eichler relation: sum_{t^2<=4n} H(4n-t^2) = 2*sigma_1(n) - sum_{d|n} min(d,n/d)
for n in [1..40] do
    b := Floor(2*Sqrt(n));
    assert &+[HurwitzClassNumber(4*n-t^2):t in [-b..b]] eq 2*SumOfDivisors(n) - &+[Min(d,n div d):d in Divisors(n)];
end for;
// REGRESSION (audit 2026-08-06): H(N) for N<0 always returned 0 because the code tested
// IsSquare(N) instead of IsSquare(-N); Zagier's extension H(-u^2) = -u/2 was dead code.
assert HurwitzClassNumber(-1) eq -1/2;
assert HurwitzClassNumber(-4) eq -1;
assert HurwitzClassNumber(-9) eq -3/2;
assert HurwitzClassNumber(-16) eq -2;
assert HurwitzClassNumber(-2) eq 0 and HurwitzClassNumber(-3) eq 0 and HurwitzClassNumber(-5) eq 0;

print "  KroneckerClassNumber";
for D in [-d:d in [3..200]|(-d) mod 4 in [0,1]] do   // definition: sum of h(E) over discriminants E dividing D
    D0 := FundamentalDiscriminant(D); _,fc := IsSquare(D div D0);
    assert KroneckerClassNumber(D) eq &+[ClassNumber(e^2*D0):e in Divisors(fc)];
end for;

// audit 2026-08-06 item 11: split(f::RngUPolElt,p::RngIntElt) (which piped to Sage via a
// hardcoded personal path) was removed; verify the polynomial overload no longer exists.
ok := false; try _ := split(x^2+1,3); catch e ok := true; end try; assert ok;

print "  Log";
R7 := Integers(7);
assert Log(R7!1,R7!1) eq 0 and Log(R7!1,R7!3) eq -1 and Log(R7!3,R7!6) eq 3;
R100 := Integers(100);
assert Log(R100!3,(R100!3)^7) eq 7 and Log(R100!3,R100!2) eq -1;
pL := 100003; Rp := Integers(pL); gp := Rp!PrimitiveRoot(pL);  // order 100002 > 5000 forces BSGS/CRT path
for xL in [0,1,12345,99999] do assert Log(gp,gp^xL) eq xL; end for;
nL := 2^5*3^4*100003; Rn := Integers(nL); an := Rn!7; on := Order(an);
for xL in [0,1,7777,123456] do yL := Log(an,an^xL); assert yL eq xL mod on and an^yL eq an^xL; end for;
R2L := Integers(2^20); a2 := R2L!3; o2 := Order(a2);           // 2-adic plog path
for xL in [0,12345,262143] do assert Log(a2,a2^xL) eq xL mod o2; end for;
assert Log(R2L!3,R2L!5) eq -1;  // 5 not in <3> mod 2^20 (log_5(9) is even: 5^6 = 9 mod 32)
gL := PrimitiveRoot(10007); R3x := Integers(3*10007);
a3 := R3x!CRT([gL,2],[10007,3]);                    // order lcm(10006,2) = 10006
b3 := R3x!CRT([Modexp(gL,3,10007),1],[10007,3]);    // local logs 3 mod 10006 and 0 mod 2 are inconsistent
assert Log(a3,b3) eq -1;

print "  Contractions";
// brute-force closure of single block-merges as independent oracle
function aud1AllContr(p)
    P := {p}; frontier := {p};
    while #frontier gt 0 do
        newf := {};
        for q in frontier do
            qs := [z : z in q];
            for i in [1..#qs], j in [i+1..#qs] do
                rq := Exclude(Exclude(q,qs[i]),qs[j]);
                Include(~rq,qs[i]+qs[j]);
                if not rq in P then Include(~P,rq); Include(~newf,rq); end if;
            end for;
        end for;
        frontier := newf;
    end while;
    return P;
end function;
for pp in [{*1,1,2,3*},{*2,2,2*},{*1,1,1,1*},{*5*},{*1,2*}] do
    assert Contractions(pp) eq aud1AllContr(pp);
end for;
pp := {*1,1,2,3*};
assert Contractions(pp,2) eq {q:q in aud1AllContr(pp)|#q eq 2};
assert Contractions(pp,4) eq {pp} and Contractions(pp,5) eq {};
assert MinimalContractions({*5*}) eq {} and MinimalContractions({*1,2,4*}) eq {{*3,4*},{*1,6*},{*2,5*}};
assert CommonContractions([{*1,1,2*},{*2,2*}]) eq (aud1AllContr({*1,1,2*}) meet aud1AllContr({*2,2*}));
assert CommonContractions([{*1,1*},{*2*}]) eq {{*2*}};
assert MinimalCommonContractions([{*1,1,2*},{*2,2*}]) eq {{*2,2*}};
assert MinimalCommonContractions([{*1,1,1,1*},{*2,2*},{*1,3*}]) eq {{*4*}};
assert MinimalCommonContractions([{*1,2*},{*1,2*}]) eq {{*1,2*}};
assert MinimalCommonContractions([{*1,1,1*},{*2,1*}]) eq {{*2,1*}};
assert MinimalCommonContractions([{*2,3*},{*1,4*}]) eq {{*5*}};
// REGRESSION (audit 2026-08-06): when the smallest input partition had a single block,
// the result was the bare partition (SetMulti) instead of a set of partitions.
rMCC := MinimalCommonContractions([{*3*},{*1,2*}]);
assert Type(rMCC) eq SetEnum and rMCC eq {{*3*}};

//
// ===== Auditor fragments (lines 661-1320) =====
//

print "  C4C6Invariants";
for lbl in ["11a1","37a1","389a1","5077a1"] do
    E := EllipticCurve(lbl);
    c4,c6 := C4C6Invariants(E); c := cInvariants(E);
    assert c4 eq c[1] and c6 eq c[2];
end for;
E := EllipticCurve([1,2,3,4,5]); c4,c6 := C4C6Invariants(E); c := cInvariants(E);
assert c4 eq c[1] and c6 eq c[2];

print "  Coefficients";
Ru<x> := PolynomialRing(Rationals());
Chyp := HyperellipticCurve(x^5+3*x+1,x+1);
assert Coefficients(Chyp) eq [[1,3,0,0,0,1],[1,1]];
assert CoefficientString(Chyp) eq "[[1,3,0,0,0,1],[1,1]]";
P2<X,Y,Z> := ProjectiveSpace(Rationals(),2);
Cpln := Curve(P2, X^4+2*X*Y^3-Z^4+5*Y^2*Z^2);
cp := Coefficients(Cpln); MM := MonomialsOfDegree(CoordinateRing(P2),4);
assert &+[cp[i]*MM[i]:i in [1..#MM]] eq DefiningPolynomial(Cpln);
P2f<X5,Y5,Z5> := ProjectiveSpace(GF(5),2);
Cpln5 := Curve(P2f, X5^3+2*X5*Y5*Z5-Z5^3+3*Y5^2*Z5);
cp5 := Coefficients(Cpln5); MM5 := MonomialsOfDegree(CoordinateRing(P2f),3);
assert &+[cp5[i]*MM5[i]:i in [1..#MM5]] eq DefiningPolynomial(Cpln5);

print "  facpat";
assert facpat(x^2+1) eq {* 2 *};
assert facpat((x+1)*(x+2)*(x^2+2)) eq {* 1, 1, 2 *};
assert facpat((x+1)^2*(x^2+x+7)) eq {* 1^^2, 2 *};   // generic branch counts multiplicity
assert facpat([2,3,1],7) eq {* 1, 1 *};              // (x+1)(x+2) mod 7
for p in [2,3,5,13], i in [1..5] do
    fp := PolynomialRing(GF(p))![Random(0,p-1):j in [1..6]];
    if fp eq 0 or Degree(fp) le 0 or not IsSquarefree(fp) then continue; end if;
    pat := {* Degree(a[1])^^a[2] : a in Factorization(fp) *};
    assert facpat(fp) eq pat;                        // finite-field branch, squarefree input
    assert facpat(fp:SquareFree:=true) eq pat;       // fast path agrees on squarefree input
end for;
// audit 2026-08-06 item 10: for non-squarefree f over a finite field, facpat now counts
// repeated factors with multiplicity, matching the generic {* Degree(a[1])^^a[2] *} semantics.
assert facpat((x+1)^2*(x^2+x+7),5) eq {* 1^^2, 2 *};              // audit repro (was {* 1, 2 *})
assert facpat((x+1)^2*(x^2+x+7),3) eq {* 1^^4 *};                 // f mod 3 = (x+1)^2*(x+2)^2
assert facpat(PolynomialRing(GF(2))![0,0,1,3,3,1]) eq {* 1^^5 *}; // x^2*(x+1)^3, wild char 2
for p in [2,3,5,13], i in [1..10] do
    fp := PolynomialRing(GF(p))![Random(0,p-1):j in [1..Random(3,9)]];
    if Degree(fp) le 0 then continue; end if;
    pat := {* Degree(a[1])^^a[2] : a in Factorization(fp) *};     // inline recomputation
    assert facpat(fp) eq pat;                                     // finite-field branch, any input
    assert &+[Multiplicity(pat,d)*d : d in Set(pat)] eq Degree(fp);  // multiset sums to degree
    cs := [Integers()!c : c in Coefficients(fp)];
    assert facpat(Rx!cs,p) eq pat and facpat(cs,p) eq pat;        // mod-p overloads agree
    assert facpat(cs) eq facpat(Rx!cs);                           // char-0 overloads agree
    if IsSquarefree(fp) then assert facpat(fp:SquareFree:=true) eq pat; end if;
end for;

print "  EasyFactorization";
for n in [-12,-1,1,30,97,2^10*3^5] do
    F,s := EasyFactorization(n);
    assert F eq Factorization(n) and s eq Sign(n);
end for;
F,s := EasyFactorization(2^41*3^30); assert F eq Factorization(2^41*3^30) and s eq 1;
bigp1 := NextPrime(10^24); bigp2 := NextPrime(3*10^24);  // 51-digit product is beyond ECMLimit:=1000
F,s := EasyFactorization(3^5*bigp1*bigp2);
assert s eq 0 and F eq [<3,5>];                      // provably correct partial factorization
F,s := EasyFactorization(bigp1*bigp2);
assert s eq 0 and F eq [];
// REGRESSION (audit 2026-08-06): EasyFactorization(0) used to hit Magma's generic
// Factorization(0) error; the (previously unreachable) nonzero require now fires.
okEF := false;
try _ := EasyFactorization(0); catch e okEF := "nonzero" in e`Object; end try;
assert okEF;

print "  PrimeDivisors";
P,b := PrimeDivisors([12,35,-49]);
assert P eq [2,3,5,7] and b;
P,b := PrimeDivisors([96,75]:AllowComposites:=true);
assert P eq [2,3,5] and b;
P,b := PrimeDivisors([3^5*bigp1*bigp2]:AllowComposites:=true);
assert not b and P eq Sort([3,bigp1*bigp2]);         // merged sorted list, flag false

print "  Valuation";
for num in [-9..9], den in [1..6], vp in [2,3,5] do
    if num eq 0 then continue; end if;
    r := num/den;
    assert Valuation(r,vp,true) eq Valuation(r,vp);
    assert Valuation(r,vp,false) eq Valuation(r,vp);
end for;
QQ := Rationals();
assert Valuation(QQ!8,4,false) eq 1;   // largest n with 8/4^n having denominator coprime to 4
assert Valuation(QQ!16,4,false) eq 2;
assert Valuation(QQ!2,4,false) eq 0;
assert Valuation(QQ!1/4,4,false) eq -1;

print "  NormalizedProjectiveInvariants";
z,r,b := NormalizedProjectiveInvariants([12/5,9/25],[1,2]);
assert z eq [4,1] and r eq 3/5 and b;                // z[i] = v[i]*r^-w[i], minimal integral
assert [12/5*r^-1, 9/25*r^-2] eq [QQ!zz : zz in z];
z,r := NormalizedProjectiveInvariants([-3/1,5/1],[1,2]);
assert z eq [3,5] and r eq -1;                       // first odd-weight entry made positive
z,r := NormalizedProjectiveInvariants([0/1,-7/1],[3,2]);
assert z eq [0,-7] and r eq 1;                       // even-weight signs immutable

print "  NormalizedIgusaClebschInvariants";
// LMFDB oracle: SELECT label,eqn,igusa_clebsch_inv,igusa_inv FROM g2c_curves
//   WHERE label IN ('169.a.169.1','249.a.249.1')
C1 := HyperellipticCurve(x^5+x^4, x^3+x+1);          // 169.a.169.1
assert NormalizedIgusaClebschInvariants(C1) eq [4,793,3757,-21632];
assert NormalizedIgusaInvariants(C1) eq [1,-33,-43,-283,-169];
C2 := HyperellipticCurve(x^2+x, x^3+1);              // 249.a.249.1
assert NormalizedIgusaClebschInvariants(C2) eq [108,57,2259,-31872];
assert NormalizedIgusaInvariants(C2) eq [27,28,32,20,-249];
Cg := HyperellipticCurve(x^5+3*x^3-2*x+1);
icn := NormalizedIgusaClebschInvariants(Cg);
ign := NormalizedIgusaInvariants(Cg);
mgn := NormalizedModularIgusaInvariants(Cg);
for d in [-3,2,5] do
    Cd := QuadraticTwist(Cg,d);                      // twists have the same weighted projective invariants
    assert NormalizedIgusaClebschInvariants(Cd) eq icn;
    assert NormalizedIgusaInvariants(Cd) eq ign;
    assert NormalizedModularIgusaInvariants(Cd) eq mgn;
end for;

print "  NormalizedIgusaClebschInvariantsFp";
// REGRESSION (audit 2026-08-06): the GF(p) branch was copy-pasted from the 5-invariant
// Igusa code and indexed inv[5] (out of range) -- every call for p>2 crashed; the
// I6-branch also returned unnormalized invariants when p mod 3 ne 1.  Now normalized
// with weights [1,2,3,5]: check orbit membership and twist canonicality exhaustively.
for p in [3,5,7] do   // p=7 exercises the p mod 3 eq 1 cube-root branch
    F := GF(p); RF := PolynomialRing(F); ns := Nonsquare(F);
    for a0,a1,a2,a3 in [0..p-1] do
        fq := RF![a0,a1,a2,a3,0,1];
        if not IsSeparable(fq) then continue; end if;
        Cq := HyperellipticCurve(fq);
        ic := IgusaClebschInvariants(Cq);
        nic := NormalizedIgusaClebschInvariants(Cq);
        wIC := [1,2,3,5];
        assert exists{cc : cc in F | cc ne 0 and [cc^wIC[i]*ic[i]:i in [1..4]] eq [F!zz:zz in nic]};
        assert NormalizedIgusaClebschInvariants(HyperellipticCurve(ns*fq)) eq nic;
    end for;
end for;

print "  NormalizedIgusaInvariantsFp";
for p in [3,5] do
    F := GF(p); RF := PolynomialRing(F); ns := Nonsquare(F);
    for a0,a1,a2,a3 in [0..p-1] do
        fq := RF![a0,a1,a2,a3,0,1];
        if not IsSeparable(fq) then continue; end if;
        Cq := HyperellipticCurve(fq);
        J := IgusaInvariants(Cq);
        NJ := NormalizedIgusaInvariants(Cq);
        // result lies in the weighted scaling orbit of J (weights [1,2,3,4,5])
        assert exists{c : c in F | c ne 0 and [c^w*J[w]:w in [1..5]] eq [F!zz:zz in NJ]};
        // canonical on orbits: quadratic twist gives identical output
        assert NormalizedIgusaInvariants(HyperellipticCurve(ns*fq)) eq NJ;
    end for;
end for;
// dead-code removal (audit 2026-08-06): the "elif inv[4] ne 0" branch of the Fp normalization
// was mathematically unreachable (4*J8 = J2*J6 - J4^2 forces J8=0 when J2=J4=J6=0 for odd p;
// p=2 returns earlier); pin the J2=J4=J6=J8=0 case (y^2 = x^5 + 1) still normalizing correctly.
for p in [7,11,13] do
    fq5 := PolynomialRing(GF(p))![1,0,0,0,0,1];
    J0 := IgusaInvariants(HyperellipticCurve(fq5));
    assert [J0[i] : i in [1..4]] eq [GF(p)|0,0,0,0] and J0[5] ne 0;
    N0 := NormalizedIgusaInvariants(HyperellipticCurve(fq5));
    assert [N0[i] : i in [1..4]] eq [0,0,0,0] and N0[5] eq PowerClassRepresentative(J0[5],5);
end for;

print "  NormalizedShiodaInvariants";
C3 := HyperellipticCurve(x^7+2*x^5-3*x+1);
sh := NormalizedShiodaInvariants(C3);
assert NormalizedShiodaInvariants(QuadraticTwist(C3,-3)) eq sh;
assert NormalizedShiodaInvariants(x^7+2*x^5-3*x+1, Ru!0) eq sh;

print "  NormalizedDixmierOhnoInvariants";
P3<u3,v3,w3> := PolynomialRing(Rationals(),3);
fq4 := u3^4+v3^4+w3^4+3*u3*v3*w3^2-2*u3^2*v3^2;
do1 := NormalizedDixmierOhnoInvariants(fq4);
assert #do1 eq 13;
assert NormalizedDixmierOhnoInvariants(5*fq4) eq do1;                           // scaling invariance
assert NormalizedDixmierOhnoInvariants(Evaluate(fq4,[2*v3,u3-w3,3*w3])) eq do1; // GL3(Q) invariance
assert SPQInvariants(fq4) eq do1;
assert SPQInvariants("x^4+y^4+z^4+3*x*y*z^2-2*x^2*y^2") eq do1;

print "  SPQIsIsomorphic";
P7<a7,b7,c7> := PolynomialRing(GF(7),3);
f2q := a7^4+b7^4+c7^4+a7^2*b7^2;
g1q := Evaluate(f2q,[b7+c7,a7-c7,2*c7]);
isiso,Mq := SPQIsIsomorphic(f2q,g1q);
assert isiso and LeadingCoefficient(f2q^Mq)*g1q eq LeadingCoefficient(g1q)*(f2q^Mq);
assert not SPQIsIsomorphic(a7^4+b7^4+c7^4, a7^4+b7^4+c7^4+a7*b7*c7^2);

print "  GeometricAutomorphismField";
Kaut := GeometricAutomorphismField(HyperellipticCurve(x^5+x));
assert Degree(Kaut) eq 4 and IsIsomorphic(Kaut,NumberField(x^4+1)); // Q(zeta_8) for y^2=x^5+x

print "  MonicQuadraticRoots";
for pe in [<2,1>,<2,2>,<2,3>,<2,4>,<3,1>,<3,2>,<5,1>,<5,2>,<7,1>] do
    p := pe[1]; e := pe[2]; q := p^e;
    for bb in [0..q-1], cc in [0..q-1] do
        assert Sort([x0 mod q: x0 in MonicQuadraticRoots(bb,cc,p,e)])
            eq [x0 : x0 in [0..q-1] | (x0^2+bb*x0+cc) mod q eq 0];
    end for;
end for;
for m in [2..30] do
    for bb in [-2..m-1], cc in [-2..m-1] do
        assert Sort([x0 mod m: x0 in MonicQuadraticRoots(bb,cc,m)])
            eq [x0 : x0 in [0..m-1] | (x0^2+bb*x0+cc) mod m eq 0];
    end for;
end for;

print "  PrimePowers";
for B in [1..300] do
    assert PrimePowers(B) eq [n : n in [2..B] | IsPrimePower(n)];
end for;
for B in [2^20, 3^10, 5^10, 997^2] do   // exact powers at the boundary
    S := PrimePowers(B);
    assert S[#S] eq B;
end for;

print "  ProperDivisors";
for N in [1..60] do
    assert ProperDivisors(N) eq [d : d in Divisors(N) | d ne 1 and d ne N];
end for;

print "  PrimesInIntervalNF";
Knf := NumberField(x^2+5);
assert PrimesInInterval(Knf,4,25) eq [p : p in PrimesUpTo(25,Knf) | Norm(p) ge 4];
assert #PrimesInInterval(Knf,26,28) eq 0;
// Q(sqrt(-5)): 3 and 7 split, 5 ramifies, norms coprime to 2 up to 10 are 3,3,5,7,7
assert Sort([Norm(p):p in PrimesInInterval(Knf,2,10:coprime_to:=2)]) eq [3,3,5,7,7];

print "  NumberOfRoots";
f5 := PolynomialRing(GF(5))!((x-1)^3*(x-2)*(x^2+2));
assert NumberOfRoots(f5) eq 4;   // roots counted with multiplicity
for q in [2,5,49], i in [1..8] do
    fr := PolynomialRing(GF(q))![Random(0,4):j in [1..Random(3,7)]];
    if fr eq 0 then continue; end if;
    assert NumberOfRoots(fr) eq &+[Integers()|r0[2]:r0 in Roots(fr)];
end for;

print "  LPolynomialRoundTrips";
for q in [3,5,9] do
    F := GF(q); RF<uu> := PolynomialRing(F);
    Cq := 0; n := 0;
    repeat
        fq := uu^5 + RF![Random(F): j in [1..5]];
        try Cq := HyperellipticCurve(fq); catch e Cq := 0; end try;
        n +:= 1;
    until Type(Cq) ne RngIntElt or n gt 100;
    L := LPolynomial(Cq);
    tr := [Integers()|q^j+1-#Points(BaseChange(Cq,GF(q^j))) : j in [1..2]];
    assert TracesToLPolynomial(tr,q) eq L;
    tt,qq := LPolynomialToTraces(L); assert tt eq tr and qq eq q;
    nn := [#Points(BaseChange(Cq,GF(q^j))) : j in [1..2]];
    assert PointCountsToLPolynomial(nn,q) eq L;
    assert LPolynomialToPointCounts(L) eq nn;
end for;
E7 := EllipticCurve([GF(7)|1,3]);
LE := LPolynomial(E7);
t2 := LPolynomialToTraces(LE:d:=2);
assert t2 eq [Integers()|7+1-#Points(E7), 49+1-#Points(BaseChange(E7,GF(49)))];
assert TracesToLPolynomial([Integers()|],5) eq 1;

print "  SmoothNumbers";
smtest := func<n,P|n eq 1 or Set(PrimeDivisors(n)) subset Set(P)>;
for P in [[2],[2,3],[2,5],[2,3,5],[3,7]] do
    for B in [1,2,3,5,6,7,8,10,12,15,20,23,50,99,120] do
        assert SmoothNumberCount(P,B) eq #[n:n in [1..B]|smtest(n,P)];
        assert SmoothNumbers(P,B) eq [n:n in [1..B]|smtest(n,P)];
    end for;
    assert SmoothNumbers(P,50:B0:=7) eq [n:n in [7..50]|smtest(n,P)];
end for;
// REGRESSION (audit 2026-08-06): B = p^(2^k) was omitted from the doubled-power list
// ('while q lt B' instead of 'le'), so counts/lists were short by one exactly there.
assert SmoothNumberCount([2],4) eq 3 and SmoothNumbers([2],4) eq [1,2,4];
assert SmoothNumberCount([2],16) eq 5 and SmoothNumbers([2],16) eq [1,2,4,8,16];
assert SmoothNumberCount([3],9) eq 3 and SmoothNumbers([3],9) eq [1,3,9];
assert SmoothNumberCount([7],49) eq 3;
for P in [[2],[3],[2,3],[2,5],[2,3,5],[7]] do
    for B in [1..130] do
        assert SmoothNumberCount(P,B) eq #[n:n in [1..B]|smtest(n,P)];
        assert SmoothNumbers(P,B) eq [n:n in [1..B]|smtest(n,P)];
    end for;
end for;

print "  PowerClassRepresentative";
for p in [5,7,11], nn in [2,3,5] do
    for a in [1..p-1] do
        bpc := PowerClassRepresentative(a,p,nn);
        assert bpc eq Min({(a*c^nn) mod p : c in [1..p-1]});   // least positive elt of coset a*(F_p^*)^n
        assert PowerClassRepresentative(GF(p)!a,nn) eq bpc;
    end for;
end for;
assert PowerClassRepresentative(0,7,2) eq 0;
// audit 2026-08-06 item 12: the unused optional parameter Root of PowerClassRepresentative
// was removed; passing it must now raise an error.
ok := false; try _ := PowerClassRepresentative(3,7,2:Root:=true); catch e ok := true; end try; assert ok;

print "  SquareFreePoly";
for i in [1..12] do
    K := i mod 3 eq 0 select Rationals() else (i mod 3 eq 1 select GF(101) else GF(97));
    RK<y> := PolynomialRing(K);
    fsq := &*[(y + Random(1,20))^Random(1,3) : j in [1..3]] * Random(1,5);
    g,h := SquareFree(fsq);
    assert fsq eq g*h^2 and IsMonic(h) and IsSquarefree(g);
end for;

print "  ChangeRingMap";
pim := hom<Integers()->GF(7)|>;
assert ChangeRing(x^3+10*x-3,pim) eq PolynomialRing(GF(7))![4,3,0,1];

print "  GetFilenames";
gfn := GetFilenames(PrimePowers);
assert #gfn ge 1 and exists{t : t in gfn | #t[1] ge 7 and t[1][#t[1]-6..#t[1]] eq "utils.m" and t[2] eq ["RngIntElt"]};

print "  ExtraFields";
CCx := ComplexFieldExtra(50);
assert Precision(CCx) eq 50 and CCx`epscomp eq RealField(CCx)!(10^-40) and CCx`prec_algdep eq 45;
assert ComplexFieldExtra(300)`prec_algdep eq 240;
assert Precision(ComplexFieldExtra()) eq 100;
Krx := RationalsExtra(60);
assert Precision(Krx`CC) eq 60 and Krx`base eq Rationals() and Krx`iota eq 1;
assert Precision(RationalsExtra()`CC) eq 100;
Lnf := NumberField(x^2-2);
Lnf`CC := ComplexFieldExtra(40);
ip := InfinitePlacesExtra(Lnf);
assert #ip eq 2 and forall{z0 : z0 in ip | Abs(z0^2-2) lt 10^-20};

print "  ParallelJobsInline";
ParallelJobs("assert atoi(jobid) ge 0 and atoi(jobid) le 2", 3, 1);

print "  WriteStderr";
WriteStderr("");

print "ALL TESTS PASSED test_utils.m";
quit;
