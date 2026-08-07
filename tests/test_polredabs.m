AttachSpec("magma.spec");
SetSeed(1);
print "test_polredabs.m";

print "  polredabs";
R<x> := PolynomialRing(Rationals());
// LMFDB nf_fields oracle values (SELECT label,coeffs FROM nf_fields WHERE label IN
// ('2.0.7.1','3.1.23.1','4.0.229.1','5.5.14641.1')): coeffs are the polredabs polynomial
assert polredabs([8,-2,1]) eq [2,-1,1];              // x^2-2x+8 defines 2.0.7.1 = Q(sqrt(-7))
assert polredabs(x^2-2*x+8) eq x^2-x+2;
K := NumberField(x^3-x^2+1);                          // 3.1.23.1
assert polredabs(MinimalPolynomial(K.1+2)) eq x^3-x^2+1;
K := NumberField(x^4-x+1);                            // 4.0.229.1
assert polredabs(MinimalPolynomial(K.1+3)) eq x^4-x+1;
// minimal polynomial of 2*cos(2*pi/11) (classical) reduces to LMFDB 5.5.14641.1
assert polredabs(x^5+x^4-4*x^3-3*x^2+3*x+1) eq x^5-x^4-4*x^3+3*x^2+3*x-1;
// cyclotomic fixed points and idempotence
for n in [5,7,8,12,16] do
    c := polredabs(CyclotomicPolynomial(n));
    assert c eq polredabs(c);                         // idempotent
    assert IsIsomorphic(NumberField(c),CyclotomicField(n));
end for;
// isomorphic-field invariance: any defining polynomial of the field gives the same result
K := NumberField(x^3-x-2);
assert #{polredabs(MinimalPolynomial(K.1+j)) : j in [0..2]} eq 1;
// DiscFactors branch of the gp command
assert polredabs(x^2-5:DiscFactors:=[2,5]) eq x^2-x-1;
// reducible (etale, squarefree) input is supported by modern pari
assert polredabs([-1,0,1]) eq [0,-1,1];               // x^2-1 -> x^2-x
// rational coefficients
assert polredabs([1/2,1/2,1]) eq [2,-1,1];            // x^2+x/2+1/2 defines Q(sqrt(-7))
// non-monic input
assert polredabs(9*x^2-6*x-4) eq x^2-x-1;             // defines Q(sqrt(5))
// FldNum and FldRat signatures
L := polredabs(NumberField(x^2-2*x+8));
assert DefiningPolynomial(L) eq x^2-x+2;
assert polredabs(Rationals()) cmpeq Rationals();
// FLAGGED (audit 2026-08-06): gp errors are silently swallowed -- polredabs of a
// non-squarefree polynomial (outside the documented etale domain) returns [] (SeqEnum
// version) or the zero polynomial (RngUPolElt version) instead of raising an error.

print "  polredbest";
g := polredbest(x^2-2*x+8);
assert Degree(g) eq 2 and IsIsomorphic(NumberField(g),NumberField(x^2-2*x+8));
assert polredbest([8,-2,1]) eq Eltseq(polredbest(x^2-2*x+8));
assert Degree(polredbest(x^2-5:DiscFactors:=[2,5])) eq 2;
M := polredbest(NumberField(x^3-x-2));
assert IsIsomorphic(M,NumberField(x^3-x-2));

print "  PerfectPowerBase";
assert PerfectPowerBase(0) eq 0 and PerfectPowerBase(1) eq 1;
assert PerfectPowerBase(64) eq 2;                     // least base: 2^6 (not 8^2)
assert PerfectPowerBase(729) eq 3;
assert PerfectPowerBase(46656) eq 6;                  // 6^6 = 216^2 = 36^3, least base is 6
assert PerfectPowerBase(2^6*3^4) eq 72;               // gcd of exponents is 2: 72^2
assert PerfectPowerBase(12) eq 12;                    // not a perfect power
assert forall{n : n in [2..100] | PerfectPowerBase(n)^Round(Log(PerfectPowerBase(n),n)) eq n};

print "  IsPolredabsCandidate";
Z<t> := PolynomialRing(Integers());
assert IsPolredabsCandidate(t^2-5);
assert IsPolredabsCandidate([-5,0,1]);
assert not IsPolredabsCandidate(t^65-2);              // degree > 64
// discriminant 4pq with p,q 60-digit primes: not factorable, not prime => false
p := 100000000000000000000000000000000000000000000000000000000019; // NextPrime(10^59)
q := 300000000000000000000000000000000000000000000000000000000017; // NextPrime(3*10^59+11)
assert IsPrime(p) and IsPrime(q);
assert not IsPolredabsCandidate(t^2-p*q);
// large prime discriminant is fine (IsProbablePrime branch)
assert IsPolredabsCandidate(t^2-NextPrime(10^100));

print "  polredbestify";
h, b := polredbestify(x^2-2*x+8);
assert b and h eq x^2-x+2;                            // candidate => polredabs result
hs, bs := polredbestify([8,-2,1]);
assert bs and hs eq [2,-1,1];                         // SeqEnum version returns Eltseq
h, b := polredbestify(x^5+x^4-4*x^3-3*x^2+3*x+1);
assert b and h eq x^5-x^4-4*x^3+3*x^2+3*x-1;

print "  polredbestwithroot";
f := x^4+24*x^2+144*x+300;
g, r := polredbestwithroot(f);
assert Degree(g) eq 4 and Evaluate(f,NumberField(g)!r) eq 0;
g, r := polredbestwithroot(9*x^2-6*x-4);              // non-monic, rational root coords
assert Evaluate(9*x^2-6*x-4,NumberField(g)!r) eq 0;

print "  polredabswithroot";
g, r := polredabswithroot(f);
assert g eq polredabs(f) and Evaluate(f,NumberField(g)!r) eq 0;
g, r := polredabswithroot(9*x^2-6*x-4);
assert g eq x^2-x-1 and Evaluate(9*x^2-6*x-4,NumberField(g)!r) eq 0;

print "  polredbestifywithroot";
g, r, b := polredbestifywithroot(f);
assert b and g eq polredabs(f) and Evaluate(f,NumberField(g)!r) eq 0;
// non-candidate path exercises the polredbest loop and hom composition
f2 := (x-1)^2 - p*q;
g, r, b := polredbestifywithroot(f2);
assert not b and Degree(g) eq 2 and Evaluate(f2,NumberField(g)!r) eq 0;

print "  nfisincl";
e := nfisincl(x^2+1,x^4+1);                           // Q(i) in Q(zeta_8): 2 embeddings
L := NumberField(x^4+1);
assert #e eq 2 and forall{h0 : h0 in e | Evaluate(x^2+1,Evaluate(h0,L.1)) eq 0};
e := nfisincl(x^2+2,x^4+1);                           // Q(sqrt(-2)) in Q(zeta_8)
assert #e eq 2 and forall{h0 : h0 in e | Evaluate(x^2+2,Evaluate(h0,L.1)) eq 0};
assert #nfisincl(x^2+1,x^4+2) eq 0;                   // gp returns 0: no embedding
assert #nfisincl(x^3-2,x^4+1) eq 0;                   // degree non-divisibility early exit
e := nfisincl(x^2-x-1,x^2-5);                         // embeddings with rational coefficients
L := NumberField(x^2-5);
assert #e eq 2 and forall{h0 : h0 in e | Evaluate(x^2-x-1,Evaluate(h0,L.1)) eq 0};
e := nfisincl(x-3,x^2-2);                             // degree-1 shortcut, matches gp: [3]
assert #e eq 1 and e[1] eq 3;
es := nfisincl([-1,-1,1],[-5,0,1]);                   // SeqEnum version: coefficient vectors
assert #es eq 2 and forall{c : c in es | Evaluate(x^2-x-1,Evaluate(Polynomial(c),L.1)) eq 0};
assert #nfisincl([1,0,1],[2,0,0,0,1]) eq 0;           // empty path
assert #nfisincl([-2,0,0,1],[1,0,0,0,1]) eq 0;        // non-divisibility early exit
e := nfisincl(x^2+1,x^2+1);                           // automorphisms of Q(i)
assert #e eq 2 and Set(e) eq {x,-x};

print "  regressions (audit 2026-08-06)";
// BUG FIX (polredbestify line 95): DiscFactors was dropped in the final polredabs call,
// so polredbestify hung forever on exactly the unfactorable-discriminant inputs the
// option exists for.  Now it passes DiscFactors through and returns immediately.
fpq := x^2 - p*q;
h, b := polredbestify(fpq : DiscFactors := [2,p,q]);
assert b and h eq polredabs(fpq : DiscFactors := [2,p,q]);
hs, bs := polredbestify([-p*q,0,1] : DiscFactors := [2,p,q]);
assert bs and hs eq Eltseq(h);

// BUG FIX (nfisincl RngUPolElt line 165): the gp command used Sprintf("%o",f), which
// only parsed when the parent ring's print variable happened to be "x".  Now the
// polynomials are sent as coefficient vectors via Pol(Vecrev(...)), so any parent ring
// works: unnamed rings (variable prints as $.1) and rings named y both used to fail.
Ru := PolynomialRing(Rationals() : Global := false);  // unnamed: Sprint(Ru.1) is "$.1"
eu := nfisincl(Ru.1^2+1, Ru.1^4+1);
Lu := NumberField(Ru.1^4+1);
assert #eu eq 2 and forall{h0 : h0 in eu | Evaluate(Ru.1^2+1,Evaluate(h0,Lu.1)) eq 0};
Ry<y> := PolynomialRing(Rationals() : Global := false);
ey := nfisincl(y^2-y-1, y^2-5);
Ly := NumberField(y^2-5);
assert #ey eq 2 and forall{h0 : h0 in ey | Evaluate(y^2-y-1,Evaluate(h0,Ly.1)) eq 0};

// BUG FIX (nfisincl RngUPolElt line 169): dead code 'R<T>:=PolynomialRing(Integers());'
// renamed the print variable of the session-global Z[x] to "T" as a side effect;
// similarly line 177 renamed the global Q[x] to "x" (now uses a non-global ring).
assert Sprint(PolynomialRing(Integers()).1) ne "T";

// BUG FIX (nfisincl SeqEnum line 178): the degree-1 shortcut returned a sequence
// containing a polynomial while the general branch returns coefficient sequences;
// now both branches return coefficient sequences.
s1 := nfisincl([-3,1],[-2,0,1]);
assert Type(s1[1]) eq SeqEnum and s1 eq [[3]];
s2 := nfisincl([1,0,1],[1,0,0,0,1]);
assert Type(s2[1]) eq SeqEnum and s2 eq [[0,0,-1],[0,0,1]];

// DOC FIX (line 83): IsPolredabsCandidate(SeqEnum) is declared -> BoolElt (was SeqEnum)
assert Type(IsPolredabsCandidate([-5,0,1])) eq BoolElt;
// DOC FIX (line 99): polredbestify(SeqEnum) is declared -> SeqEnum (was RngUPolElt)
assert Type(hs) eq SeqEnum;
// DOC FIX (line 32): polredabs(FldRat) is declared -> FldRat (was FldNum) and returns K
assert Type(polredabs(Rationals())) eq FldRat;
// DOC FIX (line 50): polredbest(FldNum) docstring now says small (non-canonical);
// behaviorally it still returns an isomorphic field
assert IsIsomorphic(polredbest(NumberField(x^2-2*x+8)), NumberField(x^2-2*x+8));

print "ALL TESTS PASSED test_polredabs.m";
quit;
