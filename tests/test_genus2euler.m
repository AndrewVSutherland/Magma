AttachSpec("magma.spec");
SetSeed(1);
print "test_genus2euler.m";

print "  Genus2AlmostGoodEulerFactor type 1";
// Oracle for all tests below: explicit cluster constructions whose stable reduction
// components are elliptic curves computed independently via Magma's LPolynomial.
// If f = g(x)*CL(x) with g a cubic that is squarefree mod p, g(r) != 0 mod p, and
// CL = (x-r0)^3 + p^d*a*(x-r0)^2 + p^(2d)*b*(x-r0) + p^(3d)*c (r0 = r + p*drift, d even,
// h = t^3+at^2+bt+c squarefree mod p), then p is a prime of almost good reduction for
// y^2 = f and the Euler factor is L(E_out)*L(E_in) with E_out: w^2 = (x-r)*g(x) mod p
// (substitute x = 1/u, w = y/u^2 in y^2 = (x-r)^3 g(x) after normalizing w = y/(x-r))
// and E_in: w^2 = g(r)*h(t) mod p (substitute x = r0 + p^d t, y = p^(3d/2) w).
g2eR<x> := PolynomialRing(Integers());
g2elp := function(cub) c := LeadingCoefficient(cub); return LPolynomial(EllipticCurve(Evaluate(cub,Parent(cub).1/c)*c^2)); end function;
for p in [3,5,7,11,13] do  // p=3,5 exercise the irreducible-enumeration gcd branch, p>5 the derivative branch
    Fp := GF(p); Rp<t> := PolynomialRing(Fp);
    for tc in [<2,0,[5,1,4],5,2>, <1,3,[3,2,6],2,2>, <0,1,[0,1,2],1,4>] do // <r,drift,abc,g0,d>
        r := tc[1]; abc := tc[3]; g0 := tc[4]; d := tc[5];
        while Discriminant(Rp![abc[3],abc[2],abc[1],1]) eq 0 do abc[3] +:= 1; end while;
        g := x^3 + 2*x^2 + 3*x + g0;
        while Discriminant(Rp!g) eq 0 or Evaluate(Rp!g,Fp!r) eq 0 do g +:= 1; end while;
        h := t^3 + abc[1]*t^2 + abc[2]*t + abc[3];
        r0 := r + p*tc[2];
        CL := (x-r0)^3 + p^d*abc[1]*(x-r0)^2 + p^(2*d)*abc[2]*(x-r0) + p^(3*d)*abc[3];
        f := g*CL;
        q4 := Evaluate((t-r)*(Rp!g), t+r); cub_out := Rp![Coefficient(q4,4-i):i in [0..3]];
        oracle := g2elp(cub_out)*g2elp(Fp!Evaluate(g,r)*h);
        assert Genus2AlmostGoodEulerFactor(f,p) eq oracle;
        assert Genus2AlmostGoodEulerFactor(f,p:WhichTypeOnly:=true) eq 1;
    end for;
end for;

print "  Genus2AlmostGoodEulerFactor type 2a";
// f = lc*CL_r*CL_s (two rational size-3 clusters at r,s; depths even for vc=0, odd with an
// extra factor p for vc=1). Components: E_r: w^2 = lc*(r-s)^3*h_r(t), E_s likewise.
for p in [3,5,7,11,13] do
    Fp := GF(p); Rp<t> := PolynomialRing(Fp);
    for tc in [<0,1,0,0,[1,0,3],[2,1,5],2,2,1,false>, <2,1,1,2,[3,2,6],[1,5,3],2,4,3,false>,
               <1,2,0,0,[4,4,1],[2,3,3],1,1,2,true>, <0,2,1,1,[5,0,2],[1,1,4],1,3,1,true>] do
        r := tc[1]; s := tc[2]; if (r-s) mod p eq 0 then s +:= 1; end if;
        abc_r := tc[5]; abc_s := tc[6]; dr := tc[7]; ds := tc[8]; lc := tc[9];
        if lc mod p eq 0 then lc +:= 1; end if;
        while Discriminant(Rp![abc_r[3],abc_r[2],abc_r[1],1]) eq 0 do abc_r[3] +:= 1; end while;
        while Discriminant(Rp![abc_s[3],abc_s[2],abc_s[1],1]) eq 0 do abc_s[3] +:= 1; end while;
        hr := t^3+abc_r[1]*t^2+abc_r[2]*t+abc_r[3]; hs := t^3+abc_s[1]*t^2+abc_s[2]*t+abc_s[3];
        r0 := r + p*tc[3]; s0 := s + p*tc[4];
        CLr := (x-r0)^3 + p^dr*abc_r[1]*(x-r0)^2 + p^(2*dr)*abc_r[2]*(x-r0) + p^(3*dr)*abc_r[3];
        CLs := (x-s0)^3 + p^ds*abc_s[1]*(x-s0)^2 + p^(2*ds)*abc_s[2]*(x-s0) + p^(3*ds)*abc_s[3];
        f := (tc[10] select p else 1)*lc*CLr*CLs;  // vc=1 examples need odd depths
        oracle := g2elp(Fp!(lc*(r-s)^3)*hr)*g2elp(Fp!(lc*(s-r)^3)*hs);
        assert Genus2AlmostGoodEulerFactor(f,p) eq oracle;
        assert Genus2AlmostGoodEulerFactor(f,p:WhichTypeOnly:=true) eq 2;
    end for;
end for;

print "  Genus2AlmostGoodEulerFactor type 2b";
// Conjugate clusters at the roots of an irreducible quadratic mod p; Euler factor is
// L_E(T^2) for the inner elliptic curve E over F_p^2 (Weil restriction of scalars).
for pD in [<3,2,0>, <5,2,1>, <7,3,2>, <11,2,0>, <13,2,3>] do  // <p, D nonresidue, drift>
    p := pD[1]; D := pD[2]; assert not IsSquare(GF(p)!D);
    K<om> := NumberField(x^2-D); RK<X> := PolynomialRing(K);
    conj := func<a|Eltseq(K!a)[1] - Eltseq(K!a)[2]*om>;
    Fp2 := GF(p^2); Rp2<tt> := PolynomialRing(Fp2);
    om1 := Roots(Rp2![-D,0,1])[1][1];
    red := func<a|Fp2!(Eltseq(K!a)[1]) + Fp2!(Eltseq(K!a)[2])*om1>;
    for tc in [<2+3*om,1+om,4+2*om,2,false>, <1,5+om,3,4,false>, <om,2,1+4*om,1,true>] do
        al := tc[1]; be := tc[2]; ga := tc[3]; d := tc[4];
        while Discriminant(tt^3 + red(al)*tt^2 + red(be)*tt + red(ga)) eq 0 do ga +:= 1; end while;
        drK := tc[5] select p*(1+om) else K!0;  // cluster-center drift for one case
        CL  := (X-om-drK)^3 + p^d*al*(X-om-drK)^2 + p^(2*d)*be*(X-om-drK) + p^(3*d)*ga;
        CLb := (X-conj(om)-conj(drK))^3 + p^d*conj(al)*(X-conj(om)-conj(drK))^2 + p^(2*d)*conj(be)*(X-conj(om)-conj(drK)) + p^(3*d)*conj(ga);
        fK := CL*CLb;
        assert forall{c : c in Coefficients(fK) | Eltseq(c)[2] eq 0};
        f := (IsOdd(d) select p else 1)*g2eR![Integers()!Eltseq(c)[1] : c in Coefficients(fK)];
        h := tt^3 + red(al)*tt^2 + red(be)*tt + red(ga);
        E := g2elp((2*om1)^3*h); S<T> := Parent(E);
        oracle := g2eR!Evaluate(E,T^2);
        assert Genus2AlmostGoodEulerFactor(f,p) eq oracle;
        assert Genus2AlmostGoodEulerFactor(f,p:WhichTypeOnly:=true) eq 3;
    end for;
end for;

print "  Genus2AlmostGoodEulerFactor type 4";
// f = lc*(x-s)*CL5: size-5 cluster at r (depth d1) with size-3 subcluster at a (depth d2).
// E1: w^2 = lc*(r-s)*(t-a)*(t^2+ut+v), E2: w^2 = lc*(r-s)*(a^2+ua+v)*(t^3+At^2+Bt+C).
for p in [3,5,7,11,13] do
    Fp := GF(p); Rp<t> := PolynomialRing(Fp);
    for tc in [<0,1,0,2,0,3,6,[1,2,3],2,2,1,false>, <3,1,4,2,5,3,6,[1,2,3],2,2,2,false>,
               <1,0,0,1,0,2,5,[4,1,2],1,2,1,true>] do
        r := tc[1]; s := tc[2]; if (r-s) mod p eq 0 then s +:= 1; end if;
        c1 := tc[3]; a := tc[4]; c2 := tc[5]; u := tc[6]; v := tc[7];
        ABC := tc[8]; d1 := tc[9]; d2 := tc[10]; lc := tc[11];
        while Evaluate(Rp![v,u,1],Fp!a) eq 0 or Discriminant(Rp![v,u,1]) eq 0 do v +:= 1; end while;
        while Discriminant(Rp![ABC[3],ABC[2],ABC[1],1]) eq 0 do ABC[3] +:= 1; end while;
        CL3q := (x-a-p*c2)^3 + p^d2*ABC[1]*(x-a-p*c2)^2 + p^(2*d2)*ABC[2]*(x-a-p*c2) + p^(3*d2)*ABC[3];
        q := CL3q*(x^2+u*x+v);
        CL5 := &+[Coefficient(q,i)*p^((5-i)*d1)*(x-r-p*c1)^i : i in [0..5]];
        f := (tc[12] select p else 1)*lc*(x-s)*CL5;  // vc=1 needs d1 odd
        E1 := g2elp(Fp!(lc*(r-s))*(t-a)*Rp![v,u,1]);
        E2 := g2elp(Fp!(lc*(r-s))*Evaluate(Rp![v,u,1],Fp!a)*(t^3+ABC[1]*t^2+ABC[2]*t+ABC[3]));
        oracle := E1*E2;
        assert Genus2AlmostGoodEulerFactor(f,p) eq oracle;
        assert Genus2AlmostGoodEulerFactor(f,p:WhichTypeOnly:=true) eq 4;
    end for;
end for;

print "  Genus2AlmostGoodEulerFactor degree 5 and normalization";
// degree-5 input: 6th root at infinity; also exercises the shift loop when f(0)=0 (s1=0)
for p in [3,5,7,11,13] do
    Fp := GF(p); Rp<t> := PolynomialRing(Fp);
    for tc in [<2,0,1,[5,1,4],2>, <0,1,2,[2,2,2],2>] do  // <r,s1,s2,abc,d>; s1=0 makes f(0)=0
        r := tc[1]; s1 := tc[2]; s2 := tc[3]; abc := tc[4]; d := tc[5];
        if #{r mod p, s1 mod p, s2 mod p} lt 3 then continue; end if;
        while Discriminant(Rp![abc[3],abc[2],abc[1],1]) eq 0 do abc[3] +:= 1; end while;
        h := t^3 + abc[1]*t^2 + abc[2]*t + abc[3];
        CL := (x-r)^3 + p^d*abc[1]*(x-r)^2 + p^(2*d)*abc[2]*(x-r) + p^(3*d)*abc[3];
        f := (x-s1)*(x-s2)*CL;  // quintic
        oracle := g2elp((t-r)*(t-s1)*(t-s2))*g2elp(Fp!((r-s1)*(r-s2))*h);
        assert Genus2AlmostGoodEulerFactor(f,p) eq oracle;
    end for;
end for;
// model invariances (all give Q-isomorphic curves, so the Euler factor must not change);
// p^2*f and f(p*x) exercise the rescaling branch of Normalize (Algorithm 1)
p := 7;
f0 := ((x-1)^3 + p^2*2*(x-1)^2 + p^4*3*(x-1) + p^6*5)*((x-3)^3 + p^2*(x-3)^2 + p^4*4*(x-3) + p^6*6);
L0 := Genus2AlmostGoodEulerFactor(f0,p);
assert L0 eq Genus2AlmostGoodEulerFactor(Evaluate(f0,x+5),p);
assert L0 eq Genus2AlmostGoodEulerFactor(g2eR![Coefficient(f0,6-i):i in [0..6]],p); // x -> 1/x
assert L0 eq Genus2AlmostGoodEulerFactor(4*f0,p);
assert L0 eq Genus2AlmostGoodEulerFactor(9*f0,p);
assert L0 eq Genus2AlmostGoodEulerFactor(p^2*f0,p);
assert L0 eq Genus2AlmostGoodEulerFactor(p^4*f0,p);
assert L0 eq Genus2AlmostGoodEulerFactor(Evaluate(f0,p*x),p);
Rq<xq> := PolynomialRing(Rationals());
assert L0 eq Genus2AlmostGoodEulerFactor(g2eR!(p^6*Evaluate(Rq!f0,xq/p)),p);
// sparse coefficients (zero coefficients hit the Valuation(0,p)=Infinity path in Normalize)
f1 := (x^3 + p^6*5)*((x-1)^3 + p^6*3);
L1 := Genus2AlmostGoodEulerFactor(f1,p);
assert L1 eq Genus2AlmostGoodEulerFactor(Evaluate(f1,p*x),p);
assert L1 eq Genus2AlmostGoodEulerFactor(p^2*Evaluate(f1,p*x),p);
// genuinely zero coefficients (x^5 and x^2) combined with the rescaling branch:
// f2 = (x^3+3)(x^3 + p^4*2*x + p^6*4) is a valid type-1 input at p=7 (cluster of 3 at 0, depth 2)
Fp := GF(p); Rp<t> := PolynomialRing(Fp);
f2 := (x^3 + 3)*(x^3 + p^4*2*x + p^6*4);
assert Coefficient(f2,5) eq 0 and Coefficient(f2,2) eq 0;
oracle2 := g2elp(Rp![Coefficient(t*(t^3+3),4-i):i in [0..3]])*g2elp(Fp!3*(t^3+2*t+4)); // E_out: reverse of t*(t^3+3)
assert Genus2AlmostGoodEulerFactor(f2,p) eq oracle2;
assert Genus2AlmostGoodEulerFactor(Evaluate(f2,p*x),p) eq oracle2;      // Valuation(0,p)=Infinity in Normalize rescale
assert Genus2AlmostGoodEulerFactor(p^2*Evaluate(f2,p*x),p) eq oracle2;

print "  Genus2AlmostGoodEulerFactor wrappers";
assert L0 eq Genus2AlmostGoodEulerFactor(Rq!f0,p);                                  // FldRat
assert L0 eq Genus2AlmostGoodEulerFactor(Coefficients(f0),p);                       // SeqEnum[RngIntElt]
assert L0 eq Genus2AlmostGoodEulerFactor([Coefficients(f0),[Integers()|]],p);       // [coeffs(f),coeffs(h)], h=0
assert L0 eq Genus2AlmostGoodEulerFactor([Coefficients(f0-x^2),[0,2]],p);           // h=2x: 4(f0-x^2)+(2x)^2=4f0
assert L0 eq Genus2AlmostGoodEulerFactor([f0-x^2,2*x],p);                           // SeqEnum[RngUPolElt]
assert L0 eq Genus2AlmostGoodEulerFactor(HyperellipticCurve(Rq!f0),p);              // CrvHyp
assert L0 eq Genus2AlmostGoodEulerFactor(HyperellipticCurve(Rq!(f0-x^2),Rq!(2*x)),p); // CrvHyp with h
assert 2 eq Genus2AlmostGoodEulerFactor(Coefficients(f0),p:WhichTypeOnly:=true);

print "  Genus2AlmostGoodEulerFactor p=2 fallback";
// LMFDB curves with odd conductor (good reduction at 2): the y^2=4f+h^2 model is bad at 2,
// so this exercises the p=2 fallback; truth is the L-polynomial of the reduction mod 2.
// LMFDB g2c_curves: SELECT label,eqn,cond FROM g2c_curves WHERE cond%2<>0 ORDER BY cond:
// 169.a.169.1 [[0,0,0,0,1,1],[1,1,0,1]], 249.a.249.1 [[0,1,1],[1,0,0,1]], 277.a.277.1 [[0,-1,-1],[1,1,1,1]]
for tc in [<[0,0,0,0,1,1],[1,1,0,1]>, <[0,1,1],[1,0,0,1]>, <[0,-1,-1],[1,1,1,1]>] do
    C := HyperellipticCurve(Rq!tc[1],Rq!tc[2]);
    R2 := PolynomialRing(GF(2));
    truth := LPolynomial(BaseChange(HyperellipticCurve(R2!tc[1],R2!tc[2]),GF(2)));
    assert Genus2AlmostGoodEulerFactor(C,2) eq truth;
end for;

print "  regressions (audit 2026-08-06)";
// BUG FIX: the six intrinsic declarations claimed two return values
// '-> RngUPolElt[RngInt], RngIntElt' but every return path returns exactly one value
// ('L, n := ...' raised a runtime error); declarations now match behavior.
assert Type(Genus2AlmostGoodEulerFactor(f0,7)) eq RngUPolElt;
assert Type(Genus2AlmostGoodEulerFactor(f0,7:WhichTypeOnly:=true)) eq RngIntElt;
// BUG FIX: WhichTypeOnly was silently ignored for p=2, returning a polynomial (which can
// print as "1", masquerading as reduction type 1) instead of a type in {1,2,3,4}.
// Now requires an odd prime when WhichTypeOnly is set.
caught := false;
try
    _ := Genus2AlmostGoodEulerFactor(f0,2:WhichTypeOnly:=true);
catch e
    caught := true;
end try;
assert caught;
assert Type(Genus2AlmostGoodEulerFactor(f0,2)) eq RngUPolElt; // p=2 fallback still works without WhichTypeOnly

print "ALL TESTS PASSED test_genus2euler.m";
quit;
