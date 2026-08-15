AttachSpec("magma.spec");
SetSeed(1);
print "test_tracehash.m";

print "  TraceHashWindow";
P := PrimesInInterval(2^12,2^13);
// window facts underlying the docstrings: p_565=4099,...,p_1028=8191, 464 primes
assert #P eq 464 and P[1] eq 4099 and P[464] eq 8191;
assert #PrimesUpTo(2^12) eq 564 and #PrimesUpTo(2^13) eq 1028;

print "  TraceHashEC";
// LMFDB oracle: SELECT lmfdb_iso, trace_hash FROM ec_classdata WHERE lmfdb_iso IN ('11.a','14.a','37.a','389.a','5077.a')
assert TraceHash(EllipticCurve("11a1")) eq 1428752966040989219;
assert TraceHash(EllipticCurve("14a1")) eq 1459918945821948014;
assert TraceHash(EllipticCurve("37a1")) eq 1127515239490717889;
assert TraceHash(EllipticCurve("389a1")) eq 680508473259657034;
// conductor 5077 lies inside the hash window (4096,8192), so this checks bad-prime a_p handling
assert TraceHash(EllipticCurve("5077a1")) eq 129556073554127214;

print "  TraceHashIsogenyInvariance";
assert #{TraceHash(F): F in IsogenousCurves(EllipticCurve("14a1"))} eq 1;
assert #{TraceHash(F): F in IsogenousCurves(EllipticCurve("11a1"))} eq 1;
assert #{TraceHash(EllipticCurve(l)): l in ["11a1","14a1","37a1","389a1","5077a1"]} eq 5;

print "  TraceHashListFunctionConsistency";
p61 := 2^61-1;
E := EllipticCurve("11a1"); E2 := EllipticCurve("37a1");
apl := [TraceOfFrobenius(E,p): p in P];
assert TraceHash(apl) eq TraceHash(E);
assert TraceHash(func<p|TraceOfFrobenius(E,p)>) eq TraceHash(E);
assert TraceHash(E) eq TraceHash(E); // determinism

print "  TraceHashTwoCurves";
assert TraceHash(E,E2) eq (TraceHash(E)+TraceHash(E2)) mod p61;
assert TraceHash(E,E2) eq TraceHash(func<p|TraceOfFrobenius(E,p)+TraceOfFrobenius(E2,p)>);

print "  TwistHash";
assert TwistHash(apl) eq TwistHash(func<p|TraceOfFrobenius(E,p)>);
// |a_p| is invariant under quadratic twist away from bad primes, so twist hash must agree
assert TwistHash(E) eq TwistHash(QuadraticTwist(E,-3));
assert TwistHash(E) eq TwistHash(QuadraticTwist(E,17));
assert TwistHash(E) eq TwistHash(QuadraticTwist(E,4099)); // twisting prime inside the hash window
assert TwistHash(E,E2) eq TwistHash(func<p|TraceOfFrobenius(E,p)+TraceOfFrobenius(E2,p)>);
// simultaneous quadratic twist leaves |a_p(E1)+a_p(E2)| unchanged at good primes
assert TwistHash(E,E2) eq TwistHash(QuadraticTwist(E,-3),QuadraticTwist(E2,-3));
// Abs is applied entrywise in the list version
assert TwistHash([-1,2,-3] cat [0:i in [4..464]]) eq TwistHash([1,2,3] cat [0:i in [4..464]]);
// regression (doc fix 2026-08-06): TwistHash(E::CrvEll) hashes the minimal quadratic twist of j(E),
// so for j=0 curves that are sextic (not quadratic) twists of each other the hashes coincide
E60 := EllipticCurve([0,0,0,0,2]); E61 := EllipticCurve([0,0,0,0,3]);
assert not IsQuadraticTwist(E60,E61);
assert TwistHash(E60) eq TwistHash(E61);

print "  TraceHashGenus2Convention";
// LMFDB oracle: SELECT label, "Lhash", eqn FROM g2c_curves WHERE label IN ('249.a.249.1','277.a.277.1')
// (for genus 2 curves Lhash is the trace hash); a_p = p+1-#C(F_p) at good p, and both discs (249, 277) have no window prime
R<x> := PolynomialRing(Rationals());
C := HyperellipticCurve(x^2+x,x^3+1);          // 249.a.249.1
assert TraceHash(func<p|p+1-#ChangeRing(C,GF(p))>) eq 1229180703233001291;
C := HyperellipticCurve(-x-x^2,1+x+x^2+x^3);   // 277.a.277.1
assert TraceHash(func<p|p+1-#ChangeRing(C,GF(p))>) eq 639653774064676620;
// FLAGGED (audit 2026-08-06): SlowTraceHash(C::CrvHyp), TraceHash(C::CrvPln), TraceHash(C::CrvHyp) for
// genus != 2, TraceHash(C::CrvPln,E) and TraceHash(C::CrvHyp,E) all fail unconditionally: they call
// TracesOfFrobenius(C,2^13:B0:=2^12), a signature that exists neither in stock Magma nor in this package.
// regression (item 3 fix 2026-08-09): the genus 2 fast paths of TraceHash/TwistHash(C::CrvHyp) now check
// that the external "hashcurves" binary (smalljac) is on the PATH before calling Pipe, raising a clean
// require error when it is absent (previously an opaque "Pipe: Subprocess failed with exit status 127")
if System("which hashcurves > /dev/null 2>&1") ne 0 then
    // hashcurves absent: both genus 2 fast paths must raise the clean availability error
    ok := false; try _ := TraceHash(C); catch e ok := "hashcurves binary (smalljac)" in e`Object; end try; assert ok;
    ok := false; try _ := TwistHash(C); catch e ok := "hashcurves binary (smalljac)" in e`Object; end try; assert ok;
else
    // hashcurves present: the fast path must still run and match the LMFDB trace hash for 277.a.277.1
    assert TraceHash(C) eq 639653774064676620;
end if;

print "  TraceHashNumberField";
// Res_{K/Q}(E_K) ~ E x E^(5), so the trace hash over K is the sum of the two rational hashes
K := QuadraticField(5);
EK := ChangeRing(EllipticCurve("11a1"),K);
assert TraceHash(EK) eq (TraceHash(EllipticCurve("11a1"))+TraceHash(QuadraticTwist(EllipticCurve("11a1"),5))) mod p61;

print "  TraceHashPowerSeries";
Rq<q> := PowerSeriesRing(Integers());
f := &+[TraceOfFrobenius(E2,p)*q^p : p in P] + O(q^8192);
assert TraceHash(f) eq TraceHash(E2);

print "  TraceHashModSym";
// LMFDB oracle: SELECT label, trace_hash FROM mf_newforms WHERE label = '23.2.a.a' (dim 2, coefficient field Q(sqrt5))
M := NewformDecomposition(NewSubspace(CuspidalSubspace(ModularSymbols(23,2))))[1];
assert TraceHash(M) eq 1804802565588895238;

print "  TraceStats";
// regression (doc fix 2026-08-06): TraceStats returns zratio, moments, trace hash in that order;
// the docstring/return types formerly claimed the order was trace hash, zratio, moments
aps := [TraceOfFrobenius(E,p): p in PrimesUpTo(2^13)];
z,m,h := TraceStats(aps,0);
assert Type(z) eq FldReElt and Type(m) eq SeqEnum and Type(h) eq RngIntElt;
assert h eq 1428752966040989219;       // hash of the window slice = TraceHash(11a1), LMFDB 11.a
assert #m eq 6;
zc := #[a: a in aps | a eq 0];
assert Abs(z - 1.0*zc/#aps) lt 1e-25;  // zratio = fraction of zero traces
assert Abs(m[1] - 1.0*&+aps/#aps) lt 1e-25;                 // first raw moment
assert Abs(m[2] - 1.0*&+[t^2: t in aps]/#aps) lt 1e-20;     // second raw moment
z1,m1,h1 := TraceStats(aps,1:Moments:=4);
assert h1 eq h and Abs(z1-z) lt 1e-25 and #m1 eq 4;
// weight-1 normalization a_p/sqrt(p): second Sato-Tate moment is 1
assert Abs(m1[2] - 1) lt 0.05;
assert Abs(m1[2] - 1.0*&+[aps[i]^2/NthPrime(i): i in [1..#aps]]/#aps) lt 1e-20;

print "ALL TESTS PASSED test_tracehash.m";
quit;
