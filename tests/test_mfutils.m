AttachSpec("magma.spec");
SetSeed(1);
print "test_mfutils.m";

print "  AnalyticConductor";
// LMFDB oracle: SELECT level,weight,analytic_conductor FROM mf_newforms WHERE (level,weight) IN ((11,2),(1,12),(7,3),(23,1),(100,6))
assert Abs(AnalyticConductor(11,2) - 0.08783544222340842) lt 1e-14;
assert Abs(AnalyticConductor(1,12) - 0.7683431805595888) lt 1e-13;
assert Abs(AnalyticConductor(7,3) - 0.19073618505220782) lt 1e-13;
assert Abs(AnalyticConductor(23,1) - 0.011478495290559056) lt 1e-14;
assert Abs(AnalyticConductor(100,6) - 16.038381981298063) lt 1e-11;

print "  NewformLabel";
assert NewformLabel(11,2,1,1) eq "11.2.a.a";       // LMFDB 11.2.a.a
assert NewformLabel(23,1,2,1) eq "23.1.b.a";       // LMFDB 23.1.b.a
assert NewformLabel(100,6,1,4) eq "100.6.a.d";     // LMFDB 100.6.a.d
assert NewformLabel(10000,2,27,28) eq "10000.2.ba.bb"; // base-26: 26->"ba", 27->"bb"
assert NewformLabel("11.1",2,1) eq "11.2.a.a";     // Conrey character label form

print "  SplitNewformLabel";
assert SplitNewformLabel("11.2.a.a") eq [11,2,1,1];
assert SplitNewformLabel("10000.2.ba.bb") eq [10000,2,27,28];
for N in [1,26,703], k in [1,7], o in [1,27], n in [2,26] do
    assert SplitNewformLabel(NewformLabel(N,k,o,n)) eq [N,k,o,n];
end for;

print "  SplitEmbeddedNewformLabel";
assert SplitEmbeddedNewformLabel("11.2.a.a.1.1") eq [11,2,1,1,1,1];
assert SplitEmbeddedNewformLabel("983.2.c.a.982.3") eq [983,2,3,1,982,3];

print "  CompareNewformLabels";
assert CompareNewformLabels("11.2.a.a","11.2.a.a") eq 0;
assert CompareNewformLabels("2.8.a.a","10.2.a.a") eq -1;  // numeric, not string, level order
assert CompareNewformLabels("11.2.a.a","11.2.a.b") eq -1;
assert CompareNewformLabels("11.10.a.a","11.2.a.a") eq 1;  // numeric weight order
assert CompareNewformLabels("11.2.b.a","11.2.a.a") eq 1;

print "  CompareEmbeddedNewformLabels";
assert CompareEmbeddedNewformLabels("11.2.a.a.1.1","11.2.a.a.1.1") eq 0;
assert CompareEmbeddedNewformLabels("11.2.a.a.1.1","11.2.a.a.1.2") eq -1;
assert CompareEmbeddedNewformLabels("2.8.a.a.1.1","10.2.a.a.1.1") eq -1;
assert CompareEmbeddedNewformLabels("11.2.a.a.10.1","11.2.a.a.2.1") eq 1;

print "  NewspaceLabel";
assert NewspaceLabel(11,2,1) eq "11.2.a";
assert NewspaceLabel(23,1,2) eq "23.1.b";
assert NewspaceLabel(DirichletGroup(11)!1,2) eq "11.2.a";
assert NewspaceLabel("11.1",2) eq "11.2.a";

print "  SplitNewspaceLabel";
N,k,o := SplitNewspaceLabel("983.2.c"); assert N eq 983 and k eq 2 and o eq 3;
for N in [1,26,100], k in [1,12], o in [1,27] do
    a,b,c := SplitNewspaceLabel(NewspaceLabel(N,k,o));
    assert a eq N and b eq k and c eq o;
end for;

print "  CompareNewspaceLabels";
assert CompareNewspaceLabels("11.2.a","11.2.a") eq 0;
assert CompareNewspaceLabels("2.2.a","10.2.a") eq -1;
assert CompareNewspaceLabels("13.2.a","11.2.a") eq 1;

print "  Gamma1Label";
assert Gamma1Label(23,2) eq "23.2";
N,k := SplitGamma1Label("23.2"); assert N eq 23 and k eq 2;
N,k := SplitGamma1Label(Gamma1Label(9999,100)); assert N eq 9999 and k eq 100;

print "  HeckeOrbitCode";
// LMFDB oracle: SELECT label,hecke_orbit_code FROM mf_newforms WHERE label IN ('11.2.a.a','23.1.b.a','7.3.b.a','100.6.a.d','983.2.c.a')
assert HeckeOrbitCode(11,2,1,1) eq 33554443;
assert HeckeOrbitCode(23,1,2,1) eq 68736253975;
assert HeckeOrbitCode(7,3,2,1) eq 68769808391;
assert HeckeOrbitCode(100,6,1,4) eq 13510798982774884;
assert HeckeOrbitCode(983,2,3,1) eq 137472508887;
for T in [<11,2,1,1>,<2^24-1,2^12-1,2^16-1,2047>,<997,3,14,29>] do
    N,k,o,n := SplitHeckeOrbitCode(HeckeOrbitCode(T[1],T[2],T[3],T[4]));
    assert <N,k,o,n> eq T;
end for;
assert HeckeOrbitCode(2^24-1,2^12-1,2^16-1,2047) lt 2^63; // fits in signed 64-bit

print "  anlist_from_aplist";
m := 120; P := PrimesInInterval(1,m);
E := EllipticCurve("11a1");
ap := [Integers()|TraceOfFrobenius(E,p):p in P];
chi := map<Integers()->Integers()|x:->GCD(x,11) eq 1 select 1 else 0>;
an := anlist_from_aplist(11,2,chi,ap,m);
f := qExpansion(ModularForm(E),m+1);
assert an eq [Coefficient(f,n):n in [1..m]];
E := EllipticCurve("20a1");  // 2^2*5 | N exercises the p|N branch (a_2=0, a_5=1)
ap := [Integers()|TraceOfFrobenius(E,p):p in P];
chi20 := map<Integers()->Integers()|x:->GCD(x,20) eq 1 select 1 else 0>;
an := anlist_from_aplist(20,2,chi20,ap,m);
f := qExpansion(ModularForm(E),m+1);
assert an eq [Coefficient(f,n):n in [1..m]];
// nontrivial (quadratic, odd) character: newform 7.3.b.a
mm := 60;
chi7 := [c:c in Elements(FullDirichletGroup(7))|Order(c) eq 2][1];
f := Newforms(CuspForms(chi7,3))[1][1];
apseq := [Integers()!Coefficient(f,p):p in PrimesInInterval(1,mm)];
chimap := map<Integers()->Integers()|x:->GCD(x,7) ne 1 select 0 else JacobiSymbol(x,7)>;
assert anlist_from_aplist(7,3,chimap,apseq,mm) eq [Integers()!Coefficient(f,n):n in [1..mm]];
// weight 12 level 1: Ramanujan tau
D := Newforms(CuspForms(1,12))[1][1];
apD := [Integers()!Coefficient(D,p):p in PrimesInInterval(1,60)];
anD := anlist_from_aplist(1,12,map<Integers()->Integers()|x:->1>,apD,60);
assert anD eq [Integers()!Coefficient(D,n):n in [1..60]];
assert anD[2] eq -24 and anD[6] eq -6048; // tau(2), tau(6), Ramanujan 1916
// edge case m=1 (no primes, empty ap)
assert anlist_from_aplist(11,2,chi,[Integers()|],1) eq [1];

print "  Regressions (audit 2026-08-06)";
// BUG FIX: CompareNewspaceLabels formerly compared only the level (SplitNewspaceLabel
// returns three values, of which only the first was used in an expression context),
// so any two distinct labels with the same level compared as 1 in both orders.
assert CompareNewspaceLabels("11.2.a","11.4.a") eq -1;
assert CompareNewspaceLabels("11.4.a","11.2.a") eq 1;
assert CompareNewspaceLabels("11.2.a","11.2.b") eq -1;
assert CompareNewspaceLabels("11.2.b","11.2.a") eq 1;
assert CompareNewspaceLabels("11.2.b","11.2.b") eq 0;
assert CompareNewspaceLabels("11.12.a","11.2.a") eq 1;  // numeric weight order
// DOC FIX: SplitNewformLabel/SplitEmbeddedNewformLabel return a single SeqEnum,
// not four scalar values as their signatures formerly claimed.
assert Type(SplitNewformLabel("11.2.a.a")) eq SeqEnum;
assert Type(SplitEmbeddedNewformLabel("11.2.a.a.1.1")) eq SeqEnum;
// BUG FIX: HeckeOrbitCode formerly required n lt 2^12 (message said 2^11); codes with
// n gt 2^11 exceed 2^63-1 and do not fit the signed 64-bit LMFDB bigint. Exact bound n le 2^11.
assert HeckeOrbitCode(11,2,1,2^11) lt 2^63;             // n=2^11 accepted, fits
assert HeckeOrbitCode(2^24-1,2^12-1,2^16-1,2^11) lt 2^63; // max fields, still fits
ok := false;
try x := HeckeOrbitCode(11,2,1,2^11+1); catch e ok := true; end try;
assert ok; // n=2^11+1 now rejected (formerly accepted, produced code ge 2^63)
// DOC FIX: HeckeOrbitCode positivity require message named NewformLabel.
ok := false;
try x := HeckeOrbitCode(0,2,1,1); catch e ok := "HeckeOrbitCode" in e`Object; end try;
assert ok;

print "ALL TESTS PASSED test_mfutils.m";
quit;
