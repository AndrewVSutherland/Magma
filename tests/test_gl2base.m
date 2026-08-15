AttachSpec("magma.spec");
SetSeed(1);
print "test_gl2base.m";
// Assembled from the 2026-08-06/07 audit of gl2base.m: six auditor fragments (ranges 1-661, 662-1342,
// 1343-2011, 2012-2678 twice, 2679-3364) plus a regression section pinning every fix applied.

// =============================== lines 1-661 ===============================
// gl2base.m lines 1-661: ClassNumberTable, GL1/SL1/GL2/SL2 ambients, GL1 level/lift/project/labels/characters,
// GL2/SL2 lift/project, sizes, GL2Order, GL2TriangularSubgroup, PGL2Order, SL2Level

print "  ClassNumberTable";
// h(-3)=h(-4)=h(-7)=h(-8)=h(-11)=1, h(-15)=2, h(-20)=2, h(-23)=3, h(-56)=4, h(-163)=1 (standard tables)
gb1_htab := ClassNumberTable(300);
assert #gb1_htab eq 4096; // table is always extended to |D| <= 4096
assert gb1_htab[3] eq 1 and gb1_htab[4] eq 1 and gb1_htab[7] eq 1 and gb1_htab[8] eq 1 and gb1_htab[11] eq 1;
assert gb1_htab[15] eq 2 and gb1_htab[20] eq 2 and gb1_htab[23] eq 3 and gb1_htab[56] eq 4 and gb1_htab[163] eq 1;
assert forall{d : d in [1..4096] | d mod 4 in [0,3] or gb1_htab[d] eq 0}; // -d must be 0,1 mod 4 to be a discriminant
assert ClassNumberTable(-163)[163] eq 1; // sign-insensitive

print "  GL2Size/SL2Size/PSL2Size/PGL2Size/BorelSizes";
assert GL2Size(1) eq 1 and SL2Size(1) eq 1 and PSL2Size(1) eq 1 and PGL2Size(1) eq 1;
for N in [2..24] do
    assert GL2Size(N) eq #GL(2,Integers(N));
    assert SL2Size(N) eq #SL(2,Integers(N));
    nsc := #[x : x in [1..N] | x*x mod N eq 1];              // scalars in SL(2,Z/N)
    assert PSL2Size(N) eq SL2Size(N) div nsc;
    assert PGL2Size(N) eq GL2Size(N) div EulerPhi(N);        // scalars in GL(2,Z/N)
end for;
for N in [2..12] do
    R := Integers(N); G := GL(2,R);
    U := [Integers()!u : u in [1..N] | GCD(u,N) eq 1];
    B := sub<G | [G![u,0,0,1] : u in U] cat [G![1,0,0,u] : u in U] cat [G![1,1,0,1]]>;
    B1 := sub<G | [G![u,0,0,1] : u in U] cat [G![1,1,0,1]]>; // upper triangular, 1 in bottom right
    assert GL2BorelSize(N) eq #B;
    assert GL2Borel1Size(N) eq #B1;
    assert SL2BorelSize(N) eq #(B meet SL(2,R));
end for;

print "  Ambients";
for N in [2..16] do
    G := GL2Ambient(N);
    assert G`Order eq GL2Size(N) and G eq GL(2,Integers(N));
    S := SL2Ambient(N);
    assert S`Order eq SL2Size(N) and S eq SL(2,Integers(N)) and assigned S`SL;
    assert GL1Order(GL1Ambient(N)) eq EulerPhi(N);
    assert Degree(SL1Ambient(Integers(N))) eq 1 and #SL1Ambient(Integers(N)) eq 1;
    assert Degree(SL1Ambient(N)) eq 1 and assigned SL1Ambient(N)`SL; // N>1 branch
end for;
assert Degree(GL1Ambient(1)) eq 1 and GL1Index(GL1Ambient(1)) eq 1;
for N in [5,8,12] do // GL2Ambient(D) = largest subgroup with determinant image D
    for r in Subgroups(GL1Ambient(N)) do
        D := sub<GL(1,Integers(N))|[g:g in Generators(r`subgroup)]>;
        G := GL2Ambient(D);
        Gf := sub<GL(2,Integers(N))|[g:g in Generators(G)]>;
        assert #Gf eq GL2Size(N) div (EulerPhi(N) div #r`subgroup);
        assert sub<GL(1,Integers(N))|[[Determinant(g)] : g in Generators(Gf)]> eq D;
    end for;
end for;

print "  GL1Order/GL1Index";
for N in [3..30] do
    assert GL1Order(GL1Ambient(N)) eq EulerPhi(N);
    assert GL1Order(sub<GL(1,Integers(N))|>) eq 1;
    assert GL1Index(sub<GL(1,Integers(N))|>) eq EulerPhi(N);
end for;

print "  GL1Level/GL1Lift/GL1Project";
gb1_bflevel := function(H) // least M | N with H = full preimage of H mod M
    N := #BaseRing(H);
    hs := {Integers()!(h[1][1]) : h in H};
    for M in Divisors(N) do
        hm := {x mod M : x in hs};
        if {x : x in [1..N] | GCD(x,N) eq 1 and (x mod M) in hm} eq hs then return M; end if;
    end for;
end function;
for N in [2..36] do
    for r in Subgroups(GL1Ambient(N)) do
        Hf := sub<GL(1,Integers(N))|[g:g in Generators(r`subgroup)]>;
        lev,K := GL1Level(Hf);
        assert lev eq gb1_bflevel(Hf);
        if lev gt 1 then
            assert #BaseRing(K) eq lev;
            assert GL1Lift(K,N) eq Hf;                       // level model lifts back to H
        else
            assert not IsFinite(BaseRing(K)) and #K eq 1;
        end if;
    end for;
end for;
for pr in [[2,8],[3,9],[4,8],[6,12],[8,16],[12,24]] do       // GL1Lift = full preimage (brute-force sets)
    for r in Subgroups(GL1Ambient(pr[1])) do
        N := pr[1]; M := pr[2];
        Hf := sub<GL(1,Integers(N))|[g:g in Generators(r`subgroup)]>;
        Lf := sub<GL(1,Integers(M))|[g:g in Generators(GL1Lift(Hf,M))]>;
        hs := {Integers()!(h[1][1]) : h in Hf};
        assert {Integers()!(h[1][1]) : h in Lf} eq {x : x in [1..M] | GCD(x,M) eq 1 and (x mod N) in hs};
    end for;
end for;
for pr in [[12,4],[12,8],[8,12],[15,9],[16,6],[9,3]] do      // GL1Project = reduce full preimage mod lcm
    for r in Subgroups(GL1Ambient(pr[1])) do
        N := pr[1]; M := pr[2];
        Hf := sub<GL(1,Integers(N))|[g:g in Generators(r`subgroup)]>;
        P := GL1Project(Hf,M);
        L := LCM(N,M);
        hs := {Integers()!(h[1][1]) : h in Hf};
        pre := {x : x in [1..L] | GCD(x,L) eq 1 and (x mod N) in hs};
        assert {Integers()!(h[1][1]) : h in P} eq {x mod M : x in pre};
    end for;
end for;

print "  GL1CanonicalGenerators";
gb1_cangens := function(N)  // independent re-implementation of the documented algorithm
    if N le 2 then return [Integers()|]; end if;
    pp := Factorization(N); q := [a[1]^a[2] : a in pp];
    gens := [Integers()|];
    if pp[1][1] eq 2 then
        if pp[1][2] gt 1 then Append(~gens,CRT([q[1]-1,1],[q[1],N div q[1]])); end if;
        if pp[1][2] gt 2 then Append(~gens,CRT([5,1],[q[1],N div q[1]])); end if;
        pp := pp[2..#pp]; q := q[2..#q];
    end if;
    for i:=1 to #q do Append(~gens,CRT([PrimitiveRoot(q[i]),1],[q[i],N div q[i]])); end for;
    return gens;
end function;
for N in [1..1000] do assert GL1CanonicalGenerators(N) eq gb1_cangens(N); end for; // hardcoded table matches algorithm
for N in [2..150] cat [999,1000,1001,1024] do // and the generators do generate (Z/NZ)*
    A,pi := MultiplicativeGroup(Integers(N));
    assert #sub<A|[Inverse(pi)(Integers(N)!x):x in GL1CanonicalGenerators(N)]> eq EulerPhi(N);
end for;

print "  GL1SquareClassReps";
gb1_bfscr := function(N)
    units := [x : x in [1..N] | GCD(x,N) eq 1];
    sq := {x*x mod N : x in units};
    reps := []; done := {};
    for x in units do
        if x in done then continue; end if;
        cl := {(x*s) mod N : s in sq};
        Append(~reps, Min(cl)); done join:= cl;
    end for;
    return Sort(reps);
end function;
assert GL1SquareClassReps(1) eq [1] and GL1SquareClassReps(2) eq [1];
for N in [3..120] cat [999,1000,1001,1008] do assert GL1SquareClassReps(N) eq gb1_bfscr(N); end for;

print "  GL1Characters";
for N in [3..24] do
    for r in Subgroups(GL1Ambient(N)) do
        Hf := sub<GL(1,Integers(N))|[g:g in Generators(r`subgroup)]>;
        C := GL1Characters(Hf);
        assert #C eq EulerPhi(N) div #Hf;                    // # characters trivial on H = index of H
        assert C[1] eq 1;                                    // principal character always present
        S := Set(C); assert {(a*b) mod N : a,b in S} eq S;   // Conrey indexes trivial on H form a group
    end for;
end for;
// PARI/GP oracle (G=znstar(8,1); chareval(G,znconreylog(G,n),7)): mod 8 the characters trivial
// on 7 = -1 (i.e. the even ones) are 8.1 and 8.5; mod 5 those trivial on {1,4} are 5.1 and 5.4
assert GL1Characters(sub<GL(1,Integers(8))|[GL(1,Integers(8))![7]]>) eq [1,5];
assert GL1Characters(sub<GL(1,Integers(5))|[GL(1,Integers(5))![4]]>) eq [1,4];

print "  GL1Label/GL1Labels/GL1Subgroups/GL1SubgroupFromLabel";
for N in [1..30] do
    S,L := GL1Subgroups(N);
    assert #S eq #L and [GL1Label(K):K in S] eq L;
    assert Sort(GL1Labels(N)) eq Sort(L);
    if N le 16 then
        for lab in L do assert GL1Label(GL1SubgroupFromLabel(lab)) eq lab; end for;
    end if;
end for;
for lab in GL1Labels(8) do
    assert GL1Label(GL1Lift(8,lab)) eq lab; // includes "1.1.1" (GL1Level level-1 cache bug fixed in 2026-08 audit)
end for;
gb1_H := GL1Lift(8,"sl1"); assert assigned gb1_H`SL and #gb1_H eq 1 and #BaseRing(gb1_H) eq 8;

print "  GL1CompareLabels/GL1SortLabels";
assert GL1CompareLabels("2.1.1","10.2.1") eq -1;
assert GL1CompareLabels("10.2.1","2.1.1") eq 1;
assert GL1CompareLabels("8.2.1","8.2.1") eq 0;
assert GL1CompareLabels("?","8.2.1") eq 1 and GL1CompareLabels("8.2.1","?") eq -1;
assert GL1SortLabels(["24.2.1","4.2.1","1.1.1"]) eq ["1.1.1","4.2.1","24.2.1"];

print "  GL2Lift/GL2Lifter/SL2Lift/SL2Lifter";
for pr in [[2,4],[3,9],[4,8],[6,12],[5,15],[8,16],[12,24]] do
    N := pr[1]; M := pr[2];
    G := GL(2,Integers(N));
    for gens in [[G|],[Random(G)],[Random(G),Random(G)],[g:g in Generators(G)]] do
        Hf := sub<G|gens>;
        K := GL2Lift(sub<G|gens>,M);
        Kf := sub<GL(2,Integers(M))|[g:g in Generators(K)]>;
        assert #Kf * GL2Size(N) eq #Hf * GL2Size(M);         // full preimage has the right order
        assert ChangeRing(Kf,Integers(N)) eq Hf;             // and reduces onto H
        if assigned K`Order then assert K`Order eq #Kf; end if;
        assert GL2Lifter(N,M)(sub<G|gens>) eq Kf;
        assert GL2Lifter(M)(sub<G|gens>) eq Kf;
    end for;
    S := SL(2,Integers(N));
    for gens in [[S|],[Random(S),Random(S)],[g:g in Generators(S)]] do
        Hf := sub<S|gens>; Hf`SL := true;
        H2 := sub<S|gens>; H2`SL := true;
        K := SL2Lift(H2,M);
        Kf := sub<SL(2,Integers(M))|[g:g in Generators(K)]>;
        assert #Kf * SL2Size(N) eq #Hf * SL2Size(M);
        assert ChangeRing(Kf,Integers(N)) eq Hf;
        H3 := sub<S|gens>; H3`SL := true;
        assert SL2Lifter(N,M)(H3) eq Kf;
    end for;
end for;
assert #BaseRing(GL2Lifter(12)(GL2Ambient(1))) eq 12;        // level-1 input dispatch

print "  GL2ElementLifter/SL2ElementLifter";
for pr in [[6,36],[4,8],[2,16],[10,40]] do
    N := pr[1]; M := pr[2];
    glift := GL2ElementLifter(N,M); slift := SL2ElementLifter(N,M);
    G := GL(2,Integers(N)); S := SL(2,Integers(N));
    for i in [1..10] do
        h := Random(G); l := glift(h);
        assert [Integers()!x mod N : x in Eltseq(l)] eq [Integers()!x : x in Eltseq(h)];
        h := Random(S); l := slift(h);
        assert Determinant(l) eq 1;
        assert [Integers()!x mod N : x in Eltseq(l)] eq [Integers()!x : x in Eltseq(h)];
    end for;
end for;

print "  GL2Project/GL2ProjectKernel/SL2Project";
gb1_G12 := GL(2,Integers(12));
gb1_I3 := Identity(GL(2,Integers(3)));
for i in [1..4] do
    gens := [Random(gb1_G12),Random(gb1_G12)];
    Hf := sub<gb1_G12|gens>;
    for M in [2,3,4,6] do assert GL2Project(sub<gb1_G12|gens>,M) eq ChangeRing(Hf,Integers(M)); end for;
    K24 := sub<GL(2,Integers(24))|[g:g in Generators(GL2Lift(sub<gb1_G12|gens>,24))]>;
    assert GL2Project(sub<gb1_G12|gens>,8) eq ChangeRing(K24,Integers(8));  // lift+project path
    P1 := GL2Project(sub<gb1_G12|gens>,1);
    assert not IsFinite(BaseRing(P1)) and #P1 eq 1;
    ker := sub<gb1_G12|[h : h in Hf | ChangeRing(h,Integers(3)) eq gb1_I3]>;
    assert GL2ProjectKernel(sub<gb1_G12|gens>,4) eq ChangeRing(ker,Integers(4));
end for;
gb1_G3 := GL(2,Integers(3));
assert GL2ProjectKernel(sub<gb1_G3|[Random(gb1_G3),Random(gb1_G3)]>,4) eq GL(2,Integers(4)); // coprime: mod-3 kernel surjects mod 4
gb1_S12 := SL(2,Integers(12));
for i in [1..3] do
    gens := [Random(gb1_S12),Random(gb1_S12)];
    Hf := sub<gb1_S12|gens>; Hf`SL := true;
    H2 := sub<gb1_S12|gens>; H2`SL := true;
    P := SL2Project(H2,4);
    assert P eq ChangeRing(Hf,Integers(4)) and assigned P`SL;
    H3 := sub<gb1_S12|gens>; H3`SL := true;
    K24 := SL2Lift(H3,24);
    H4 := sub<gb1_S12|gens>; H4`SL := true;
    assert SL2Project(H4,8) eq ChangeRing(K24,Integers(8));
    H5 := sub<gb1_S12|gens>; H5`SL := true;
    P1 := SL2Project(H5,1);
    assert not IsFinite(BaseRing(P1)) and #P1 eq 1 and assigned P1`SL;
end for;

print "  GL2Order";
for N in [25,27,32,36] do
    G := GL(2,Integers(N));
    for i in [1..3] do
        gens := [Random(G),Random(G)];
        assert GL2Order(sub<G|gens>) eq #sub<G|gens>;
    end for;
    assert GL2Order(sub<G|[g:g in Generators(G)]>) eq GL2Size(N);
    assert GL2Order(sub<G|[G!g:g in Generators(SL(2,Integers(N)))]>) eq SL2Size(N); // non-surjective det path
    assert GL2Order(sub<G|>) eq 1;
end for;

print "  GL2TriangularSubgroup";
for N in [8,9,12,15] do
    R := Integers(N); G := GL(2,R);
    U := [Integers()!u : u in [1..N] | GCD(u,N) eq 1];
    B := sub<G | [G![u,0,0,1] : u in U] cat [G![1,0,0,u] : u in U] cat [G![1,1,0,1]]>;
    Blow := sub<G | [G![u,0,0,1] : u in U] cat [G![1,0,0,u] : u in U] cat [G![1,0,1,1]]>;
    for i in [1..3] do
        gens := [Random(G),Random(G)];
        Hf := sub<G|gens>;
        K := GL2TriangularSubgroup(sub<G|gens>);
        assert K eq (Hf meet B) and K`Order eq #(Hf meet B);
        K2 := GL2TriangularSubgroup(sub<G|gens>:Upper:=false);
        assert K2 eq (Hf meet Blow);
    end for;
    assert GL2TriangularSubgroup(sub<G|[g:g in Generators(G)]>) eq B;
end for;

print "  PGL2Order";
for N in [5,7,8,9,12] do
    R := Integers(N); G := GL(2,R);
    U := [Integers()!u : u in [1..N] | GCD(u,N) eq 1];
    Sc := sub<G|[G![u,0,0,u] : u in U]>;
    for i in [1..3] do
        Hf := sub<G|[Random(G),Random(G)]>;
        assert PGL2Order(Hf) eq #Hf div #(Hf meet Sc);       // image in PGL = H/(H cap scalars)
    end for;
    assert PGL2Order(sub<G|[g:g in Generators(G)]>) eq PGL2Size(N);
end for;

print "  SL2Level";
for N in [4,6,8,9,12,16] do
    S := SL(2,Integers(N));
    for i in [1..3] do
        gens := [Random(S),Random(S)];
        H := sub<S|gens>; H`SL := true;
        lev,K := SL2Level(H);
        H2 := sub<S|gens>; H2`SL := true;
        blev := 0; // brute-force level: least M | N with #(full preimage of H mod M) = #H
        for M in Divisors(N) do
            if M eq 1 then if #H2 eq SL2Size(N) then blev := 1; break; end if; continue; end if;
            KM := {ChangeRing(k,Integers(M)) : k in H2};
            if #KM * (SL2Size(N) div SL2Size(M)) eq #H2 then blev := M; break; end if;
        end for;
        assert lev eq blev;
        if lev gt 1 then
            assert #BaseRing(K) eq lev;
            H3 := sub<S|gens>; H3`SL := true;
            assert SL2Lift(K,N) eq H3;
        end if;
    end for;
    H := sub<S|[g:g in Generators(S)]>; H`SL := true;
    lev,K := SL2Level(H);
    assert lev eq 1 and assigned K`SL and #K eq 1;           // full SL2 has level 1, K = sl2N1
end for;

// =============================== lines 662-1342 ===============================
// Audit tests for gl2base.m lines 662-1342 (GL2/SL2 index/level/generators/permrep/invariant intrinsics)

print "  GL2Index/GL2DeterminantIndex/GL2RelativeIndex";
for N in [2,3,4,5,6,8,9,12] do
    G := GL(2,Integers(N));
    for i in [1..2] do
        H := sub<G|[Random(G),Random(G)]>;
        Hc := sub<G|[g:g in Generators(H)]>;             // clean copy (no cached attributes)
        idx := Index(G,Hc);                              // Magma built-in as oracle
        assert GL2Index(H) eq idx;
        dind := EulerPhi(N) div #{Determinant(h):h in Hc};
        assert GL2DeterminantIndex(H) eq dind;
        assert GL2RelativeIndex(H) eq idx div dind;
    end for;
end for;

print "  SL2Order/SL2Intersection/SL2Index/PSL2Index";
// N<=24: direct path; 25<N<=46: SL2Order Borel path; N>46: SL2Intersection det-rep path
for N in [6,12,27,48] do
    G := GL(2,Integers(N)); S := SL(2,Integers(N));
    for i in [1..2] do
        H := sub<G|[Random(G),Random(G)]>;
        Hc := sub<G|[g:g in Generators(H)]>;
        HS := Hc meet S;                                 // brute-force oracle
        assert SL2Order(H) eq #HS;
        K := SL2Intersection(sub<G|[g:g in Generators(H)]>);
        assert #K eq #HS and SL2Order(K) eq #HS;
        assert SL2Index(sub<G|[g:g in Generators(H)]>) eq SL2Size(N) div #HS;
        HSm := sub<S|HS,-Identity(S)>;
        assert PSL2Index(sub<G|[g:g in Generators(H)]>) eq SL2Size(N) div #HSm;
    end for;
    K := sub<S|[Random(S),Random(S)]>; K`SL := true;
    assert SL2Order(K) eq #sub<S|[g:g in Generators(K)]>;
end for;

print "  GL2Level/GL2Levels";
// brute-force level: least M | N with [GL2(M):H mod M] = [GL2(N):H]
bflevel := function(H,N)
    idx := Index(GL(2,Integers(N)),H);
    for M in Divisors(N) do
        if M eq 1 then if idx eq 1 then return 1; end if; continue; end if;
        if Index(GL(2,Integers(M)),ChangeRing(H,Integers(M))) eq idx then return M; end if;
    end for;
end function;
for N in [8,12,16,24] do
    G := GL(2,Integers(N));
    for i in [1..2] do
        H := sub<G|[Random(G),Random(G)]>;
        Hc := sub<G|[g:g in Generators(H)]>;
        lev, HH := GL2Level(H);
        assert lev eq bflevel(Hc,N);
        if lev gt 1 then
            assert #BaseRing(HH) eq lev;
            assert Index(GL(2,Integers(lev)),ChangeRing(Hc,Integers(lev))) eq GL2Index(HH);
        end if;
        L := GL2Levels(sub<G|[g:g in Generators(H)]>);
        X := AssociativeArray();
        for M in Divisors(N) do X[M] := M eq 1 select 1 else Index(GL(2,Integers(M)),ChangeRing(H,Integers(M))); end for;
        assert L eq Sort([[M,X[M]] : M in Divisors(N) | &and[X[M div p] lt X[M] : p in PrimeDivisors(M)]]);
        assert L[#L][1] eq lev;
    end for;
end for;
// deterministic: lift of Borel(5) to level 40 has level 5 and index 6 (X_0(5))
H := sub<GL(2,Integers(40))|[g:g in Generators(GL2Lift(GL2Borel(5),40))]>;
lev, HH := GL2Level(H); assert lev eq 5 and GL2Index(HH) eq 6;
// prime-index cached branch: lift of Borel(2) (index 3) to level 8
H := GL2Lift(GL2Borel(2),8);
assert GL2Levels(H) eq [[1,1],[2,3]];

print "  GL2RelativeLevel";
for N in [8,9,12] do
    S := SL(2,Integers(N)); G := GL(2,Integers(N));
    for u in [i : i in [3..N] | GCD(i,N) eq 1] do
        // full preimage of a determinant subgroup has relative level 1
        assert GL2RelativeLevel(sub<G|[G!g : g in Generators(S)] cat [G![u,0,0,1]]>) eq 1;
    end for;
end for;
assert GL2RelativeLevel(sub<GL(2,Integers(8))|[g:g in Generators(GL2Borel(8))]>) eq 8;

print "  GL2FromGenerators/SL2FromGenerators/GL2Generators/SL2Generators";
for N in [8,9,15] do
    G := GL(2,Integers(N)); S := SL(2,Integers(N));
    H := sub<G|[Random(G),Random(G)]>;
    gens := GL2Generators(H);
    assert gens eq Sort(gens);
    idx := Index(G,H);
    H3 := GL2FromGenerators(IntegerToString(N),IntegerToString(idx),sprint(gens));
    assert GL2Index(H3) eq idx and sub<G|[G!x:x in GL2Generators(H3)]> eq sub<G|gens>;
    assert GL2FromGenerators(N,idx,true,gens)`NegOne;
    K := sub<S|[Random(S),Random(S)]>; K`SL := true;
    sgens := SL2Generators(K);
    sidx := Index(S,sub<S|[S!x:x in sgens]>);
    K2 := SL2FromGenerators(N,sidx,sgens);
    assert K2`SL and SL2Index(K2) eq sidx;
end for;
// X_0(11): level 11, index 12, genus 1, contains -I (classical; genus X_0(11)=1)
H := GL2FromGenerators(11,12,1,true,GL2Generators(GL2Borel(11)));
assert H`Genus eq 1 and H`NegOne and H`Level eq 11 and GL2Order(H) eq GL2Size(11) div 12;
assert GL2Index(GL2FromGenerators(["11","12",sprint(GL2Generators(GL2Borel(11)))])) eq 12;
K := SL2FromGenerators("11","12","1","1",sprint(SL2Generators(SL2Borel(11))));
assert K`SL and K`Genus eq 1 and SL2Index(K) eq 12;
assert GL2FromGenerators(1,1,[Parent([1])|]) eq GL2Ambient(1);
assert SL2FromGenerators(1,1,[Parent([1])|])`SL;

print "  GL2RandomizeGenerators/SL2RandomizeGenerators";
for N in [5,8,12] do
    G := GL(2,Integers(N));
    H := sub<G|[Random(G),Random(G)]>;
    Hc := sub<G|[g:g in Generators(H)]>;
    K := GL2RandomizeGenerators(H);
    assert GL2Order(K) eq #Hc and IsConjugate(G,Hc,sub<G|[g:g in Generators(K)]>);
    S := SL(2,Integers(N));
    K0 := sub<S|[Random(S),Random(S)]>; K0`SL := true;
    Kc := sub<S|[g:g in Generators(K0)]>;
    K := SL2RandomizeGenerators(K0);
    assert SL2Order(K) eq #Kc;
    assert IsConjugate(G,sub<G|[G!g:g in Generators(Kc)]>,sub<G|[G!g:g in Generators(K)]>);
end for;

print "  GL2Transpose/SL2Transpose";
for N in [4,7,9] do
    G := GL(2,Integers(N));
    H := sub<G|[Random(G),Random(G)]>;
    Hc := sub<G|[g:g in Generators(H)]>;
    K := GL2Transpose(H);
    assert sub<G|[g:g in Generators(K)]> eq sub<G|[Transpose(g):g in Generators(Hc)]>;
    assert GL2Transpose(K) eq Hc;
    S := SL(2,Integers(N));
    K0 := sub<S|[Random(S)]>; K0`SL := true;
    K1 := SL2Transpose(K0);
    assert K1`SL and sub<S|[S!g:g in Generators(K1)]> eq sub<S|[Transpose(g):g in Generators(K0)]>;
end for;

print "  CosetActionViaIntermediate";
for N in [8,9] do
    G := GL(2,Integers(N));
    Kc := sub<G|[G!g:g in Generators(GL2Borel(N))]>;
    Hc := sub<G|[G!g:g in Generators(GL2Borel1(Integers(N)))]>;
    phi1 := CosetActionViaIntermediate(G,Kc,Hc);
    phi2 := CosetAction(G,Hc);
    assert Degree(Image(phi1)) eq Index(G,Hc);
    assert #Kernel(phi1) eq #Kernel(phi2) and #Image(phi1) eq #Image(phi2);
    for i in [1..15] do g := Random(G); assert #Fix(phi1(g)) eq #Fix(phi2(g)); end for;
end for;

print "  GL2PermutationRepresentation";
for N in [8,12] do
    G := GL(2,Integers(N));
    // full-determinant subgroup: exercises the SL2-transversal algorithm (noCosetAction)
    repeat H := sub<G|[Random(G),Random(G),Random(G)]>;
    until #{Determinant(h):h in H} eq EulerPhi(N) and Index(G,H) gt 1 and GL2Level(sub<G|[g:g in Generators(H)]>) eq N;
    Hc := sub<G|[g:g in Generators(H)]>;
    pi1 := GL2PermutationRepresentation(sub<G|[g:g in Generators(H)]>:noCosetAction);
    pi2 := CosetAction(G,Hc);
    for j in [1..15] do g := Random(G); assert #Fix(pi1(g)) eq #Fix(pi2(g)); end for;
    assert #Kernel(pi1) eq #Kernel(pi2);
    // non-full determinant goes through CosetAction
    B := sub<G|[G![1,1,0,1]]>;
    assert Degree(Image(GL2PermutationRepresentation(B))) eq Index(G,B);
end for;

print "  SL2PermutationRepresentation/SL2PermutationCharacter";
for N in [8,9] do
    S := SL(2,Integers(N));
    K := sub<S|[Random(S),Random(S)]>; K`SL := true;
    Kc := sub<S|[g:g in Generators(K)]>;
    rho := SL2PermutationRepresentation(K);
    rho2 := CosetAction(S,Kc);
    Km := sub<S|[g:g in Generators(Kc)]>; Km`SL := true;
    chi := SL2PermutationCharacter(Km);
    for i in [1..10] do g := Random(S); assert #Fix(rho(g)) eq #Fix(rho2(g)); assert chi(g) eq #Fix(rho2(g)); end for;
end for;

print "  GL2RightTransversal/SL2RightTransversal";
for N in [13,16] do      // N>12 exercises the SL2-lift path
    G := GL(2,Integers(N));
    for i in [1..2] do
        H := sub<G|[Random(G),Random(G)]>;
        Hc := sub<G|[g:g in Generators(H)]>;
        if Index(G,Hc) gt 300 then continue; end if;
        T := GL2RightTransversal(sub<G|[g:g in Generators(H)]>);
        assert #T eq Index(G,Hc);
        assert forall{<a,b> : a,b in [1..#T] | a ge b or not T[a]*T[b]^-1 in Hc};
    end for;
end for;
// dindex>1 branch at N>12: <SL2(16),[9,0,0,1]> has determinant index 4
G := GL(2,Integers(16)); S16 := SL(2,Integers(16));
H := sub<G|[G!g : g in Generators(S16)] cat [G![9,0,0,1]]>;
Hc := sub<G|[g:g in Generators(H)]>;
T := GL2RightTransversal(sub<G|[g:g in Generators(H)]>);
assert #T eq Index(G,Hc);
assert forall{<a,b> : a,b in [1..#T] | a ge b or not T[a]*T[b]^-1 in Hc};
for N in [8,16] do
    S := SL(2,Integers(N));
    Bc := sub<S|[S!g:g in Generators(SL2Borel(N))]>;
    Bm := sub<S|[S!g:g in Generators(SL2Borel(N))]>; Bm`SL := true;
    T := SL2RightTransversal(Bm);
    assert #T eq Index(S,Bc);
    assert forall{<a,b> : a,b in [1..#T] | a ge b or not T[a]*T[b]^-1 in Bc};
end for;

print "  GL2PermutationCharacter";
for N in [8,12] do
    G := GL(2,Integers(N));
    for i in [1..2] do
        H := sub<G|[Random(G),Random(G)]>;
        Hc := sub<G|[g:g in Generators(H)]>;
        chi1 := GL2PermutationCharacter(sub<G|[g:g in Generators(H)]>:Algorithm:="cc");
        chi2 := GL2PermutationCharacter(sub<G|[g:g in Generators(H)]>:Algorithm:="enum");
        chi3 := GL2PermutationCharacter(sub<G|[g:g in Generators(H)]>:Algorithm:="action");
        chid := GL2PermutationCharacter(sub<G|[g:g in Generators(H)]>);
        rho := CosetAction(G,Hc);
        for j in [1..10] do
            g := Random(G); v := #Fix(rho(g));
            assert chi1(g) eq v and chi2(g) eq v and chi3(g) eq v and chid(g) eq v;
        end for;
    end for;
end for;

print "  GL2DeterminantImage/GL2DeterminantReps/GL2DeterminantLabel";
for N in [4,8,9,15] do
    G := GL(2,Integers(N));
    for i in [1..2] do
        H := sub<G|[Random(G),Random(G)]>;
        Hc := sub<G|[g:g in Generators(H)]>;
        dets := {Determinant(h):h in Hc};
        assert {d[1][1] : d in GL2DeterminantImage(sub<G|[g:g in Generators(H)]>)} eq dets;
        X := GL2DeterminantReps(sub<G|[g:g in Generators(H)]>);
        assert Keys(X) eq dets;
        for d in Keys(X) do assert X[d] in Hc and Determinant(X[d]) eq d; end for;
    end for;
    assert GL2DeterminantLabel(GL2Ambient(N)) eq "1.1.1";
end for;

print "  GL2Scalars/GL2ScalarSubgroupGL1/GL2ScalarIndex/GL2ContainsScalars/GL2IncludeScalars";
for N in [4,8,9,12] do
    G := GL(2,Integers(N));
    U := [i : i in [1..N] | GCD(i,N) eq 1];
    Zfull := sub<G|[G![u,0,0,u] : u in U]>;
    for i in [1..2] do
        H := sub<G|[Random(G),Random(G)]>;
        Hc := sub<G|[g:g in Generators(H)]>;
        Zb := Hc meet Zfull;                               // brute-force scalar subgroup of H
        Z := GL2Scalars(sub<G|[g:g in Generators(H)]>);
        assert sub<G|[g:g in Generators(Z)]> eq Zb;
        Z1 := GL2ScalarSubgroupGL1(sub<G|[g:g in Generators(H)]>);
        assert {z[1][1]:z in Z1} eq {z[1][1]:z in Zb};
        // NB: GL2ScalarIndex is the index of the scalars of H in the scalars of the AMBIENT
        assert GL2ScalarIndex(sub<G|[g:g in Generators(H)]>) eq EulerPhi(N) div #Zb;
        assert GL2ContainsScalars(sub<G|[g:g in Generators(H)]>) eq (Zfull subset Hc);
        HH := GL2IncludeScalars(sub<G|[g:g in Generators(H)]>);
        assert sub<G|[g:g in Generators(HH)]> eq sub<G|Hc,Zfull>;
        Hi := sub<G|[g:g in Generators(H)]>; _ := GL2Index(Hi);
        assert GL2Index(GL2IncludeScalars(Hi)) eq Index(G,sub<G|Hc,Zfull>);  // Index propagation
    end for;
    assert GL2ScalarIndex(GL2Ambient(N)) eq 1;
end for;

print "  GL2ContainsNegativeOne/GL2IncludeNegativeOne/SL2ContainsNegativeOne/SL2IncludeNegativeOne";
for N in [2,3,4,8,9] do
    G := GL(2,Integers(N)); S := SL(2,Integers(N));
    for i in [1..2] do
        H := sub<G|[Random(G),Random(G)]>;
        Hc := sub<G|[g:g in Generators(H)]>;
        assert GL2ContainsNegativeOne(sub<G|[g:g in Generators(H)]>) eq (-Identity(G) in Hc);
        HH := GL2IncludeNegativeOne(sub<G|[g:g in Generators(H)]>);
        assert sub<G|[g:g in Generators(HH)]> eq sub<G|Hc,-Identity(G)> and HH`NegOne;
        Hi := sub<G|[g:g in Generators(H)]>; _ := GL2Index(Hi);
        assert GL2Index(GL2IncludeNegativeOne(Hi)) eq Index(G,sub<G|Hc,-Identity(G)>);
        K := sub<S|[Random(S)]>; Kc := sub<S|[g:g in Generators(K)]>;
        Km := sub<S|[g:g in Generators(K)]>; Km`SL := true;
        assert SL2ContainsNegativeOne(Km) eq (-Identity(S) in Kc);
        Km := sub<S|[g:g in Generators(K)]>; Km`SL := true;
        KK := SL2IncludeNegativeOne(Km);
        assert KK`SL and KK`NegOne and sub<S|[g:g in Generators(KK)]> eq sub<S|Kc,-Identity(S)>;
    end for;
end for;

print "  GL2ContainsComplexConjugation/GL2ContainsCC/GL2QAdmissible";
// brute-force oracle: cc elements are the GL2-conjugates of [1,0,0,-1] and (N even) [1,1,0,-1]
bfcc := function(Hc,N)
    G := GL(2,Integers(N));
    if exists{z : z in Conjugates(G,G![1,0,0,-1]) | z in Hc} then return true; end if;
    if IsEven(N) and exists{z : z in Conjugates(G,G![1,1,0,-1]) | z in Hc} then return true; end if;
    return false;
end function;
for N in [2,3,4,5,6,7,8,9] do
    G := GL(2,Integers(N));
    for i in [1..3] do
        H := sub<G|[Random(G),Random(G)]>;
        Hc := sub<G|[g:g in Generators(H)]>;
        v := bfcc(Hc,N);
        assert GL2ContainsComplexConjugation(sub<G|[g:g in Generators(H)]>) eq v;
        assert GL2ContainsCC(sub<G|[g:g in Generators(H)]>) eq v;
        CH := GL2SimilarityCounts(sub<G|[g:g in Generators(H)]>);
        assert GL2ContainsComplexConjugation(sub<G|[g:g in Generators(H)]>:CH:=CH) eq v;
        want := (#{Determinant(h):h in Hc} eq EulerPhi(N)) and v;
        assert GL2QAdmissible(sub<G|[g:g in Generators(H)]>) eq want;
        assert GL2QAdmissible(sub<G|[g:g in Generators(H)]>:MustContainNegativeOne) eq (want and -Identity(G) in Hc);
    end for;
end for;
// deep path (index > 1024): cyclic group on a random conjugate of [1,0,0,-1] mod 16
G := GL(2,Integers(16));
z := (G![1,0,0,-1])^(G![3,1,7,2]);
assert GL2ContainsComplexConjugation(sub<G|[z]>);
z2 := (G![1,1,0,-1])^(G![3,1,7,2]);       // class distinct from [1,0,0,-1] when N is even
assert GL2ContainsComplexConjugation(sub<G|[z2]>);
assert not GL2ContainsComplexConjugation(sub<G|[G![3,0,0,3]]>);          // scalars only, even N
assert not GL2ContainsComplexConjugation(sub<GL(2,Integers(25))|[GL(2,Integers(25))![2,0,0,2]]>); // odd N

print "  GL2/SL2 degenerate level-1 inputs";
assert GL2Generators(GL2Ambient(1)) eq [];
assert GL2Index(GL2Ambient(1)) eq 1 and GL2DeterminantIndex(GL2Ambient(1)) eq 1;
assert GL2Level(GL2Ambient(1)) eq 1 and GL2Levels(GL2Ambient(1)) eq [[1,1]];
assert GL2RelativeLevel(GL2Ambient(1)) eq 1;
assert SL2Order(SL2Ambient(1)) eq 1 and SL2Index(SL2Ambient(1)) eq 1 and PSL2Index(SL2Ambient(1)) eq 1;
assert GL2ScalarIndex(GL2Ambient(1)) eq 1 and GL2ContainsComplexConjugation(GL2Ambient(1)) and GL2QAdmissible(GL2Ambient(1));
assert #GL2RightTransversal(GL2Ambient(1)) eq 1 and #SL2RightTransversal(SL2Ambient(1)) eq 1;
T := sub<GL(2,Integers(6))|>;
assert GL2Index(T) eq GL2Size(6) and GL2DeterminantIndex(T) eq 2 and GL2Level(T) eq 6;

print "  GL2Triangular1Subgroup (Borel and trivial cases)";
// brute-force oracle: elements of the Borel with bottom row [0,1]
for N in [3,4,5,6,7,8,9,12] do
    G := GL(2,Integers(N));
    B := GL2Borel(N);
    BF := sub<G|[h:h in B|h[2][1] eq 0 and h[2][2] eq 1]>;
    T1 := GL2Triangular1Subgroup(B);
    assert sub<G|[G!g:g in Generators(T1)]> eq BF and T1`Order eq #BF;
end for;
assert GL2Order(GL2Triangular1Subgroup(sub<GL(2,Integers(5))|>)) eq 1;

print "  GL2PermutationRepresentation (prime level, noCosetAction main path)";
G := GL(2,Integers(7));
B := sub<G|[G![1,1,0,1],G![3,0,0,1],G![1,0,0,3]]>;   // Borel(7), full determinant
pi1 := GL2PermutationRepresentation(sub<G|[g:g in Generators(B)]>:noCosetAction);
pi2 := CosetAction(G,B);
for j in [1..15] do g := Random(G); assert #Fix(pi1(g)) eq #Fix(pi2(g)); end for;
assert #Kernel(pi1) eq #Kernel(pi2);

// =============================== lines 1343-2011 ===============================
// Audit tests for gl2base.m lines 1343-2011 (commutator/agreeable/cusps/genus/Cartan/Borel/Sturm/projective image)
ZZ := Integers();

print "  GL2CommutatorSubgroup";
// [GL2(Zhat),GL2(Zhat)] has level 2 and index 2 in SL2(Zhat) (preimage of A3 in SL(2,2))
K := GL2CommutatorSubgroup(GL2Ambient(2));
assert #BaseRing(K) eq 2 and #K eq 3;
C8 := CommutatorSubgroup(GL(2,Integers(8))); C8`SL := true;
M8,K8 := SL2Level(C8); assert M8 eq 2 and K eq K8;
// brute-force verification: lift H to a level beyond the commutator level and compare
for t in [<GL2Borel(2),16>,<GL2Borel(3),36>,<GL2SplitCartan(3),36>,<GL2SplitCartan1(3),36>,<GL2Borel(4),32>,<GL2NonsplitCartan(5),100>] do
    K := GL2CommutatorSubgroup(t[1]);
    C := CommutatorSubgroup(GL2Lift(t[1],t[2])); C`SL := true;
    M2,K2 := SL2Level(C);
    assert M2 eq #BaseRing(K) and K eq K2;
end for;

print "  GL2IsAgreeable/GL2AgreeableClosure/GL2AgreeableQuotient";
assert GL2IsAgreeable(GL2Ambient(5));
assert GL2IsAgreeable(GL2Borel(9));
assert GL2IsAgreeable(GL2SplitCartan(8));
assert not GL2IsAgreeable(GL2Borel1(5)); // scalar index 4
// entangled group {g in GL(2,Z/6) : sgn(g mod 2) = chi_3(det g)} has agreeable closure GL2(Zhat)
G6 := GL(2,Integers(6)); G2 := GL(2,Integers(2)); S3 := SymmetricGroup(3);
X := [x : x in Set(RSpace(G2)) | x ne RSpace(G2)!0];
sgn := func<g|Sign(S3![Index(X,X[i]*ChangeRing(g,Integers(2))):i in [1..3]])>;
H6 := sub<G6|[g : g in G6 | sgn(g) eq KroneckerSymbol(ZZ!Determinant(g),3)]>;
assert Index(G6,H6) eq 2 and GL2DeterminantIndex(H6) eq 1;
assert not GL2IsAgreeable(H6);
assert GL2Level(GL2AgreeableClosure(H6)) eq 1;
assert GL2AgreeableQuotientInvariants(H6) eq [2];
// closure of Borel1(5) is Borel(5) with cyclic quotient C4
NA,AA := GL2Level(GL2AgreeableClosure(GL2Borel1(5)));
assert NA eq 5 and AA eq GL2Borel(5);
assert GL2IsAgreeable(AA);
assert GL2AgreeableQuotientInvariants(GL2Borel1(5)) eq [4];
NB,B9 := GL2Level(GL2AgreeableClosure(GL2Borel(9)));
assert NB eq 9 and B9 eq GL2Borel(9);
assert GL2AgreeableQuotientInvariants(GL2Ambient(7)) eq [];

print "  GL2CuspCount/GL2CuspOrbits/GL2RationalCuspCount/GL2CuspWidths/GL2EllipticPoints (X_0(N))";
// literature oracles for X_0(N) (Diamond-Shurman 3.7-3.8, Ogg): cusps = sum_{d|N} phi(gcd(d,N/d)),
// one Galois orbit of size phi(gcd(d,N/d)) per divisor d; nu2, nu3 standard
gl2bX0cusps := func<N|&+[EulerPhi(GCD(d,N div d)):d in Divisors(N)]>;
gl2bX0orbits := func<N|Sort([[r[1],r[2]]:r in Eltseq({* EulerPhi(GCD(d,N div d)) : d in Divisors(N) *})])>;
gl2bNu2 := func<N|N mod 4 eq 0 select 0 else &*[ZZ|1+KroneckerSymbol(-4,p):p in PrimeDivisors(N)]>;
gl2bNu3 := func<N|N mod 9 eq 0 select 0 else &*[ZZ|1+KroneckerSymbol(-3,p):p in PrimeDivisors(N)]>;
for N in [1..40] do
    B := GL2Borel(N);
    assert GL2CuspCount(B) eq gl2bX0cusps(N);
    assert GL2CuspOrbits(B) eq gl2bX0orbits(N);
    assert GL2RationalCuspCount(B) eq #[d:d in Divisors(N)|EulerPhi(GCD(d,N div d)) eq 1];
    a,b := GL2EllipticPoints(B);
    if N gt 1 then assert a eq gl2bNu2(N) and b eq gl2bNu3(N); end if;
    idx := SL2Size(N) div (N*EulerPhi(N));
    assert GL2Genus(B:NoGenusData) eq ZZ!(1 + idx/12 - gl2bNu2(N)/4 - gl2bNu3(N)/3 - gl2bX0cusps(N)/2);
end for;
// X_1(N) cusp count for N > 4 is (1/2) sum_{d|N} phi(d) phi(N/d); X_1(p) has (p-1)/2 rational cusps
for N in [5..30] do
    assert GL2CuspCount(GL2BorelK1(N)) eq ExactQuotient(&+[EulerPhi(d)*EulerPhi(N div d):d in Divisors(N)],2);
end for;
for p in [5,7,11,13] do
    assert GL2RationalCuspCount(GL2BorelK1(p)) eq (p-1) div 2;
    assert GL2CuspOrbits(GL2BorelK1(p))[1] eq [1,(p-1) div 2];
end for;
// q = 1 mod N with full determinant: all cusps are Fq-rational
assert GL2RationalCuspCount(GL2Borel(25),51) eq GL2CuspCount(GL2Borel(25));

print "  cusp/genus fast vs slow";
procedure gl2baseCuspCheck(H : qmax:=5)
    assert GL2CuspCount(H) eq GL2CuspCount(H:slow:=true);
    assert GL2CuspOrbits(H) eq GL2CuspOrbits(H:slow:=true);
    assert GL2CuspWidths(H) eq Sort(GL2CuspWidths(H:slow:=true));
    a,b := GL2EllipticPoints(H); c,d := GL2EllipticPoints(H:slow:=true);
    assert a eq c and b eq d;
    R := BaseRing(H);
    if IsFinite(R) then
        assert GL2Genus(sub<GL(2,R)|Generators(H)>:NoGenusData) eq GL2Genus(sub<GL(2,R)|Generators(H)>:NoGenusData,slow:=true);
    end if;
    assert GL2RationalCuspCount(H) eq GL2RationalCuspCount(H:slow:=true);
    M := GL2Level(GL2IncludeNegativeOne(H)); if M eq 1 then return; end if;
    n := 0;
    for q in [x:x in [2..M+1]|GCD(x,M) eq 1] do
        // q = 1 mod M with det index > 1 was mishandled before the 2026-08 audit fix; no longer excluded
        assert GL2RationalCuspCount(H,q) eq GL2RationalCuspCount(H,q:slow:=true);
        n +:= 1; if n ge qmax then break; end if;
    end for;
    cc1 := GL2RationalCuspCounts(H); cc2 := GL2RationalCuspCounts(H:slow:=true);
    assert cc1 eq cc2;
    assert cc1[1] eq GL2CuspCount(H);
    O := GL2CuspOrbits(H);
    assert &+[o[1]*o[2]:o in O] eq GL2CuspCount(H);
    assert (&+[ZZ|o[2]:o in O|o[1] eq 1]) eq GL2RationalCuspCount(H);
end procedure;
for N in [2,3,4,5,7,8,9,12,18,25] do
    zoo := [GL2Borel(N), GL2Borel1(N), GL2BorelK1(N), GL2SplitCartan(N), GL2SplitCartanNormalizer(N), GL2NonsplitCartan(N), GL2NonsplitCartanNormalizer(N), GL2SplitCartan1(N), GL2SplitCartanK1(N)];
    if IsEven(N) then zoo cat:= [GL2Borel12(N), GL2BorelK12(N)]; end if;
    if N mod 4 ne 2 then zoo cat:= [GL2Scalars(N)]; end if;
    for p in PrimeDivisors(N) do zoo cat:= [GL2Arith1(p,N), GL2ArithK1(p,N)]; end for;
    if IsOdd(N) and IsPrimePower(N) then
        r := PrimitiveRoot(N); G := GL(2,Integers(N));
        zoo cat:= [sub<G|[0,-1,1,0],[1,1,0,1],[r^2,0,0,1]>, sub<G|[1,0,0,r^2],[1,1,0,1]>]; // det index 2 examples
    end if;
    for H in zoo do if GL2Index(H) le 2000 then gl2baseCuspCheck(H); end if; end for;
end for;
// 2-power level with index > 1024 exercises the CosetActionViaIntermediate branch of GL2CuspOrbits
H := GL2SplitCartan1(16);
assert GL2Index(H) eq 3072;
assert GL2CuspOrbits(H) eq GL2CuspOrbits(H:slow:=true);

print "  GL2Genus/SL2Genus";
// known genus values: X_0 (Cremona/LMFDB), X_1, X(N), X_ns+(13)=X_s+(13)=3 (cursed curves)
for t in [<11,1>,<15,1>,<22,2>,<23,2>,<37,2>,<50,2>,<49,1>,<48,3>,<64,3>,<36,1>,<25,0>] do
    assert GL2Genus(GL2Borel(t[1]):NoGenusData) eq t[2];
end for;
for t in [<11,1>,<12,0>,<13,2>,<14,1>,<15,1>,<16,2>,<17,5>,<18,2>] do
    assert GL2Genus(GL2BorelK1(t[1]):NoGenusData) eq t[2];
end for;
for t in [<7,3>,<9,10>,<11,26>] do assert GL2Genus(GL2Scalars(t[1]):NoGenusData) eq t[2]; end for;
for t in [<8,5>,<12,25>] do assert GL2Genus(sub<GL(2,Integers(t[1]))|[-1,0,0,-1]>:NoGenusData) eq t[2]; end for;
assert GL2Genus(GL2NonsplitCartanNormalizer(13):NoGenusData) eq 3;
assert GL2Genus(GL2SplitCartanNormalizer(13):NoGenusData) eq 3;
assert GL2Genus(GL2NonsplitCartanNormalizer(11):NoGenusData) eq 1;
assert SL2Genus(SL2Borel(11)) eq 1;
assert SL2Genus(SL2Borel(37)) eq 2;
// LMFDB gps_gl2zhat_fine ground truth (query: label,level,generators,index,genus,cusps,rational_cusps,
// cusp_orbits,cusp_widths,nu2,nu3,psl2index; fetched 2026-08-07)
gl2blmfdb := [*
[* "10.20.1.a.1", 10, [[7,9,7,8],[8,5,9,7]], 20, 1, 2, 0, [[2,1]], [[10,2]], 0, 2, 20 *],
[* "12.144.7.a.1", 12, [[1,6,6,7],[7,0,0,7],[9,4,4,5]], 144, 7, 12, 0, [[4,3]], [[12,12]], 0, 0, 144 *],
[* "15.120.7.a.1", 15, [[1,0,0,11],[8,6,3,7],[10,3,6,5],[11,6,12,1]], 120, 7, 8, 0, [[2,2],[4,1]], [[15,8]], 0, 0, 120 *],
[* "16.128.7.a.1", 16, [[1,15,1,2],[15,0,0,15],[15,4,12,11]], 128, 7, 8, 0, [[8,1]], [[16,8]], 0, 2, 128 *],
[* "20.120.8.a.1", 20, [[3,6,10,9],[5,2,6,15],[19,14,6,5]], 120, 8, 6, 0, [[2,3]], [[20,6]], 0, 0, 120 *],
[* "21.126.7.a.1", 21, [[3,19,19,15],[7,13,20,13],[14,4,4,4]], 126, 7, 6, 0, [[6,1]], [[21,6]], 6, 0, 126 *],
[* "24.144.10.a.1", 24, [[7,4,10,17],[9,16,10,3],[13,4,16,5],[13,8,20,5],[13,20,10,19],[17,8,10,11],[17,16,8,17]], 144, 10, 6, 4, [[1,4],[2,1]], [[24,6]], 0, 0, 144 *],
[* "26.84.5.a.1", 26, [[7,24,0,23],[11,20,0,11]], 84, 5, 6, 6, [[1,6]], [[2,3],[26,3]], 0, 0, 84 *],
[* "28.126.8.a.1", 28, [[3,19,26,9],[9,24,10,7],[11,6,20,7],[21,2,26,21]], 126, 8, 6, 0, [[3,2]], [[14,3],[28,3]], 2, 0, 126 *],
[* "30.120.9.a.1", 30, [[1,2,6,29],[8,9,9,5],[14,15,27,23]], 120, 9, 4, 2, [[1,2],[2,1]], [[30,4]], 0, 0, 120 *],
[* "8.24.0-4.a.1.1", 8, [[1,6,4,1],[3,0,0,7],[3,0,4,7],[5,6,6,3]], 24, 0, 4, 2, [[1,2],[2,1]], [[2,2],[4,2]], 0, 0, 12 *]
*];
for r in gl2blmfdb do
    H := sub<GL(2,Integers(r[2]))|r[3]>;
    assert GL2Index(H) eq r[4];
    g, data, w := GL2Genus(H);
    assert g eq r[5] and data[1] eq r[12];
    assert GL2CuspCount(H) eq r[6];
    assert GL2RationalCuspCount(H) eq r[7];
    assert GL2CuspOrbits(H) eq r[8];
    assert GL2CuspWidths(H) eq r[9];
    n2,n3 := GL2EllipticPoints(H);
    assert n2 eq r[10] and n3 eq r[11];
end for;

print "  GL2CartanSize/GL2Cartan/GL2CartanNormalizer";
// direct unit count in O = Z[w], w = (D+sqrt(D))/2: N(a+bw) = (4a^2+4abD+b^2(D^2-D))/4
for D in [-3,-4,-7,-8,-11,-12,-15,-16] do
    for N in [2..9] do
        u := #[1 : a,b in [0..N-1] | GCD((4*a*a + 4*a*b*D + b*b*(D*D-D)) div 4, N) eq 1];
        assert GL2CartanSize(D,N) eq u;
        C := GL2Cartan(D,N);
        assert #C eq u and IsAbelian(C);
    end for;
end for;
for t in [<-3,5>,<-4,5>,<-7,3>,<-8,9>,<-11,4>,<-15,8>,<-19,6>,<-20,7>,<-4,2>,<-7,2>] do
    C := GL2Cartan(t[1],t[2]); CN := GL2CartanNormalizer(t[1],t[2]);
    assert C subset CN and IsNormal(CN,C);
    assert #CN eq (t[2] eq 2 and t[1] mod 4 eq 0 select #C else 2*#C);
end for;
// split/inert classification: Cartan(-4,13) is split (13 = 1 mod 4), Cartan(-4,7) is nonsplit
assert IsConjugate(GL(2,Integers(13)),GL2Cartan(-4,13),GL2SplitCartan(13));
assert IsConjugate(GL(2,Integers(7)),GL2Cartan(-4,7),GL2NonsplitCartan(7));

print "  GL2NonsplitCartan/GL2SplitCartan normalizers";
for N in [2,3,4,5,7,8,9,11] do
    C := GL2NonsplitCartan(N);
    assert #C eq &*[ZZ| p^(2*Valuation(N,p)-2)*(p^2-1) : p in PrimeDivisors(N)];
    assert IsAbelian(C);
end for;
for p in [5,7,13] do
    CN := GL2NonsplitCartanNormalizer(p);
    assert #CN eq 2*(p^2-1);
    D := -3; while not (IsFundamentalDiscriminant(D) and KroneckerSymbol(D,p) eq -1) do D -:= 4; end while;
    assert CN eq Normalizer(GL2Ambient(p),GL2Cartan(D,p));
end for;
// the algebraic split Cartan normalizer <C,[0,1,1,0]> equals the full normalizer at odd prime powers but not at 2-powers
for N in [5,7,9,25] do
    assert GL2SplitCartanNormalizer(N) eq Normalizer(GL2Ambient(N),GL2SplitCartan(N));
end for;
for N in [4,8] do
    NC := GL2SplitCartanNormalizer(N); FN := Normalizer(GL2Ambient(N),GL2SplitCartan(N));
    assert NC subset FN and NC ne FN;
    assert GL2Lift(GL2SplitCartanFullNormalizer(N),N) eq FN;
end for;
for N in [12,15] do
    assert GL2Lift(GL2SplitCartanFullNormalizer(N),N) eq Normalizer(GL2Ambient(N),GL2SplitCartan(N));
end for;

print "  standard subgroups: set equality and attributes";
for N in [2..8] do
    R := Integers(N); G := GL(2,R); U := [u:u in [1..N]|GCD(u,N) eq 1];
    borel := sub<G|[G![a,b,0,d]:a in U, d in U, b in [0..N-1]]>;
    borel1 := sub<G|[G![1,b,0,d]:d in U, b in [0..N-1]]>;
    borelk1 := sub<G|[G![a,b,0,d]:a in [1,N-1], d in U, b in [0..N-1]]>;
    sc := sub<G|[G![a,0,0,d]:a in U, d in U]>;
    sc1 := sub<G|[G![1,0,0,d]:d in U]>;
    sck1 := sub<G|[G![a,0,0,d]:a in [1,N-1], d in U]>;
    zz := sub<G|[G![a,0,0,a]:a in U]>;
    H := GL2Borel(N); assert H eq borel and H`Order eq #borel;
    H := GL2Borel1(N); assert H eq borel1 and H`Order eq #borel1;
    H := GL2BorelK1(N); assert H eq borelk1 and H`Order eq #borelk1;
    H := GL2SplitCartan(N); assert H eq sc and H`Order eq #sc;
    H := GL2SplitCartan1(N); assert H eq sc1 and H`Order eq #sc1;
    H := GL2SplitCartanK1(N); assert H eq sck1 and H`Order eq #sck1;
    H := GL2Scalars(N); assert H eq zz and H`Order eq #zz;
    assert GL2Arith(N) eq sc1 and GL2ArithK(N) eq sck1;
    if IsEven(N) then
        b12 := sub<G|[G![1,b,0,d]:d in U, b in [0..N-1]|IsEven(b)]>;
        bk12 := sub<G|[G![a,b,0,d]:a in [1,N-1], d in U, b in [0..N-1]|IsEven(b)]>;
        H := GL2Borel12(N); assert H eq b12;
        H := GL2BorelK12(N); assert H eq bk12;
    end if;
    for M in Divisors(N) do
        a1 := sub<G|[G![1,b,0,d]:d in U, b in [0..N-1]|b mod M eq 0]>;
        ak1 := sub<G|[G![a,b,0,d]:a in [1,N-1], d in U, b in [0..N-1]|b mod M eq 0]>;
        H := GL2Arith1(M,N); assert H eq a1 and H`Order eq #a1;
        H := GL2ArithK1(M,N); assert H eq ak1 and H`Order eq #ak1;  // (1,2) Order bug fixed in 2026-08 audit
    end for;
    S := SL(2,R);
    sb := sub<S|[S![a,b,0,e]:a in U, e in U, b in [0..N-1]|a*e mod N eq 1]>;
    H := SL2Borel(N); assert H eq sb and H`Order eq #sb;
    // NegOne attributes (N=2 cases fixed in 2026-08 audit)
    for H in [GL2Borel(N),GL2Borel1(N),GL2BorelK1(N),GL2SplitCartan(N),GL2SplitCartan1(N),GL2SplitCartanK1(N),GL2Scalars(N)] do
        assert GL2ContainsNegativeOne(H) eq (-Identity(H) in sub<GL(2,Integers(N))|Generators(H)>);
    end for;
end for;
assert GL2Level(GL2CartanNormalizer(-4,2)) eq 2;

print "  GL2BorelPC/SL2BorelPC";
for N in [5,8,9,12] do
    G,P,f := GL2BorelPC(N);
    for i in [1..25] do a := Random(G); b := Random(G); assert f(a*b) eq f(a)*f(b); end for;
    assert #{f(x):x in G} eq #G and #G eq #P;
    G,P,f := SL2BorelPC(N);
    for i in [1..25] do a := Random(G); b := Random(G); assert f(a*b) eq f(a)*f(b); end for;
    assert #{f(x):x in G} eq #G and #G eq #P;
end for;
B,P,f := GL2BorelPC(1); assert #P eq 1;
B,P,f := GL2BorelPC(2); assert #B eq 2 and #P eq 2 and f(B![1,1,0,1]) ne Id(P);
B,P,f := SL2BorelPC(2); assert #B eq 2 and #P eq 2;

print "  GL2SturmBound";
assert GL2SturmBound(11) eq 220;
for N in [2..30] do // = psi(N^2)*phi(N)/6 where psi(M) = [SL2(Z):Gamma_0(M)]
    assert GL2SturmBound(N) eq ((SL2Size(N^2) div (N^2*EulerPhi(N^2)))*EulerPhi(N)) div 6;
end for;

print "  GL2ProjectiveImage";
for N in [2..10] do
    assert #GL2ProjectiveImage(GL2Ambient(N)) eq SL2Size(N); // = |PGL(2,Z/N)|
    assert #GL2ProjectiveImage(GL2SplitCartan(N)) eq EulerPhi(N);
end for;
assert #GL2ProjectiveImage(GL2Ambient(1)) eq 1;

print "  GL2MaximalA4/GL2MaximalS4";
for p in [5,7,13,17] do // covers p mod 8 = 5,7,5,1 (both branches of S4)
    H := GL2MaximalA4(p);
    HH := sub<GL(2,Integers(p))|[Eltseq(h):h in Generators(H)]>;
    assert #HH eq 12*(p-1) and IdentifyGroup(GL2ProjectiveImage(HH)) eq <12,3> and GL2DeterminantIndex(HH) eq 2;
    K := GL2MaximalS4(p);
    KK := sub<GL(2,Integers(p))|[Eltseq(h):h in Generators(K)]>;
    assert #KK eq 24*(p-1) and IdentifyGroup(GL2ProjectiveImage(KK)) eq <24,12>;
    assert GL2DeterminantIndex(KK) eq (p mod 8 in [1,7] select 2 else 1);
end for;
// maximality by exhaustive subgroup search at p=5
S5 := Subgroups(GL(2,Integers(5)));
assert Max([r`order : r in S5 | IdentifyGroup(GL2ProjectiveImage(r`subgroup)) eq <12,3>]) eq 48;
assert Max([r`order : r in S5 | IdentifyGroup(GL2ProjectiveImage(r`subgroup)) eq <24,12>]) eq 96;

// =============================== lines 2012-2678 (auditor A) ===============================
print "  GL2SimilarityInvariant/Set/Counts/ClassSize";
// similarity classes vs Magma's ConjugacyClasses for prime powers (incl. p=2,3 to e>=2) and composites
for N in [2..12] cat [16] do
    G := GL(2,Integers(N));
    S := GL2SimilaritySet(N);
    assert #S eq GL2ConjugacyClassCount(N);            // p^2e-p^(e-1) formula (Williams thesis 4.3.8)
    C := ConjugacyClasses(G);
    assert #S eq #C;
    cnts := GL2SimilarityCounts(N);
    assert &+cnts eq GL2Size(N);
    assert Sort(cnts) eq Sort([c[2]:c in C]);
    for c in C do assert GL2SimilarityClassSize(c[3]) eq c[2]; end for;  // per-class size vs builtin
    rep := GL2SimilarityClassRepMap(N);
    for inv in S do assert GL2SimilarityInvariant(rep(inv)) eq inv; end for;  // round trip
    f := GL2SimilarityClassMap(N); ind := GL2SimilarityClassIndexMap(N);
    for i:=1 to 5 do
        g := Random(G); c := Random(G);
        assert f(g) eq GL2SimilarityInvariant(g);
        assert ind(g) eq Index(S,GL2SimilarityInvariant(g));
        assert GL2SimilarityInvariant(g^c) eq GL2SimilarityInvariant(g);  // conjugation invariance
    end for;
end for;
// exhaustive class-map agreement on all of GL(2,Z/6) and on all class reps at N=12
f6 := GL2SimilarityClassMap(6);
assert &and[f6(g) eq GL2SimilarityInvariant(g) : g in GL(2,Integers(6))];
f12 := GL2SimilarityClassMap(12);
assert &and[f12(r[2]) eq r[1] : r in GL2SimilarityClasses(12)];
assert GL2SimilaritySet(1) eq {@ [Universe([[Integers()|]])|] @};
assert GL2ConjugacyClassCount(1) eq 1;
assert GL2SimilarityClassCount(12) eq GL2ConjugacyClassCount(12);
assert GL2SimilarityClassSizeMap(1)([]) eq 1;
for N in [8,9,15] do
    sz := GL2SimilarityClassSizeMap(N); G := GL(2,Integers(N));
    for i:=1 to 5 do g := Random(G); assert sz(GL2SimilarityInvariant(g)) eq GL2SimilarityClassSize(g); end for;
    assert GL2ConjugacyClassSize(Identity(G)) eq 1;
end for;

print "  SL2SimilaritySet/Counts/Reps";
for N in [2..9] cat [12] do
    S := SL2SimilaritySet(N);
    cnts := SL2SimilarityCounts(N);
    assert #cnts eq #S and &+cnts eq SL2Size(N);
    reps := SL2SimilarityReps(N);
    assert &and[Determinant(reps[i]) eq 1 and GL2SimilarityInvariant(reps[i]) eq S[i] : i in [1..#S]];
    assert SL2SimilarityClassCount(N) eq #S;
end for;
// brute-force SL2 counts (every element) at N=4,6
for N in [4,6] do
    S := SL2SimilaritySet(N);
    bc := [0:i in [1..#S]];
    for g in SL(2,Integers(N)) do i := Index(S,GL2SimilarityInvariant(g)); assert i gt 0; bc[i] +:= 1; end for;
    assert bc eq SL2SimilarityCounts(N);
end for;

print "  GL2ConjugacyClasses/GL2SimilarityClasses/SL2GL2ConjugacyClasses";
for N in [2..9] do
    CC := GL2ConjugacyClasses(N);
    C := ConjugacyClasses(GL(2,Integers(N)));
    assert #CC eq #C;
    assert &and[Order(c[3]) eq c[1] and GL2SimilarityInvariant(c[3]) eq c[4] : c in CC];
    assert Sort([<c[1],c[2]>:c in CC]) eq Sort([<c[1],c[2]>:c in C]);  // multiset of (order,length) matches builtin
    S := GL2SimilaritySet(N);
    assert [c[4]:c in CC] eq [s:s in S];                               // ordered by similarity invariant
    SC := GL2SimilarityClasses(N);
    assert [r[1]:r in SC] eq [s:s in S] and &and[GL2SimilarityInvariant(r[2]) eq r[1] : r in SC];
    SGC := SL2GL2ConjugacyClasses(N);
    SS := SL2SimilarityClasses(N);
    assert [c[4]:c in SGC] eq [s[1]:s in SS];
    assert &+[c[2]:c in SGC] eq &+[Integers()|c[2]:c in CC|Determinant(c[3]) eq 1];
end for;
assert #GL2SimilarityClasses(1) eq 1 and #GL2ConjugacyClasses(1) eq 1;

print "  GL2IsConjugate/GL2Conjugator";
for N in [4,9,15] do
    G := GL(2,Integers(N));
    for i:=1 to 8 do
        g := Random(G); h := Random(G);
        assert GL2IsConjugate(g,h) eq IsConjugate(G,g,h);  // vs builtin
    end for;
    for i:=1 to 3 do
        g := Random(G); c := Random(G); h := g^c;
        assert g^GL2Conjugator(g,h) eq h;
        assert g^GL2Conjugator(G,g,h) eq h;
    end for;
end for;

print "  GL2PrimitiveSimilarityIndexes";
// brute-force divisions: classes i~j iff generated cyclic subgroups are conjugate;
// primitive indexes = minimal class index in each division (all cyclic subgroups, any order)
for N in [2..8] do
    S := GL2SimilaritySet(N); SC := GL2SimilarityClasses(N);
    n := #S; seen := [false:i in [1..n]]; divs := [];
    for i:=1 to n do
        if seen[i] then continue; end if;
        g := SC[i][2]; o := Order(g);
        D := {Index(S,GL2SimilarityInvariant(g^m)) : m in [1..o] | GCD(m,o) eq 1};
        for j in D do seen[j] := true; end for;
        Append(~divs,Min(D));
    end for;
    assert IndexedSet(Sort(divs)) eq GL2PrimitiveSimilarityIndexes(N:NoCache,NoFile);
end for;
assert GL2PrimitiveSimilarityIndexes(1) eq {@ 1 @};

print "  GL2/SL2 Primitive Set/Classes/Reps/Counts";
for N in [2..8] do
    P := GL2PrimitiveSimilarityIndexes(N);
    S := GL2SimilaritySet(N);
    PS := GL2PrimitiveSimilaritySet(N);
    assert PS eq {@ S[i] : i in P @};
    assert [r[1]:r in GL2PrimitiveSimilarityClasses(N)] eq [s:s in PS];
    assert [GL2SimilarityInvariant(g):g in GL2PrimitiveSimilarityReps(N)] eq [s:s in PS];
    assert GL2PrimitiveSimilarityCounts(N) eq [c[i]:i in P] where c := GL2SimilarityCounts(N);
    assert GL2PrimitiveSimilarityClassCount(N) eq #P;
    pind := GL2PrimitiveSimilarityClassIndexMap(N);
    for i:=1 to #S do
        j := pind(GL2SimilarityClasses(N)[i][2]);
        if i in P then assert PS[j] eq S[i]; else assert j eq 0; end if;  // 0 on non-primitive classes
    end for;
    // SL2 versions
    P := SL2PrimitiveSimilarityIndexes(N:NoCache,NoFile);
    S := SL2SimilaritySet(N); SC := SL2SimilarityClasses(N);
    n := #S; seen := [false:i in [1..n]]; divs := [];
    for i:=1 to n do
        if seen[i] then continue; end if;
        g := SC[i][2]; o := Order(g);
        D := {Index(S,GL2SimilarityInvariant(g^m)) : m in [1..o] | GCD(m,o) eq 1};
        for j in D do seen[j] := true; end for;
        Append(~divs,Min(D));
    end for;
    assert IndexedSet(Sort(divs)) eq IndexedSet(P);
    assert SL2PrimitiveSimilaritySet(N) eq {@ S[i] : i in P @};
    assert SL2PrimitiveSimilarityClassCount(N) eq #P;
    assert SL2PrimitiveSimilarityCounts(N) eq [c[i]:i in P] where c := SL2SimilarityCounts(N);
end for;

print "  GL2ScalarPrimitiveSimilarityIndexes";
for N in [5] do
    Z := GL2Scalars(N);
    R := GL2ScalarPrimitiveSimilarityIndexes(Z);
    I := GL2PrimitiveSimilarityIndexes(N);
    PR := GL2PrimitiveSimilarityReps(N);
    pind := GL2PrimitiveSimilarityClassIndexMap(N);
    n := #I; B := [true:i in [1..n]];  // brute force: keep minimal non-scalar class in each scalar orbit
    for i:=1 to n do
        if not B[i] then continue; end if;
        if IsScalar(PR[i]) then B[i] := false; continue; end if;
        for z in Z do j := pind(GL(2,Integers(N))!z*PR[i]); if j gt i then B[j] := false; end if; end for;
    end for;
    assert R eq IndexedSet([I[i]:i in [1..n]|B[i]]);
end for;

print "  GL2SimilarityCounts(H)";
tested := [* GL2Borel(8), GL2NonsplitCartan(9), GL2Borel1(6) *];
for H in tested do
    N := #BaseRing(H);
    S := GL2SimilaritySet(N);
    bc := [0:i in [1..#S]];
    for h in H do bc[Index(S,GL2SimilarityInvariant(h))] +:= 1; end for;  // brute force
    for alg in ["enum","cc","action","gl2action"] do
        assert GL2SimilarityCounts(H:Algorithm:=alg) eq bc;
    end for;
    assert GL2SimilarityCounts(H:Sparse:=true) eq [[i,bc[i]]:i in [1..#bc]|bc[i] ne 0];  // pairs are [index,count]
    P := GL2PrimitiveSimilarityIndexes(N);
    for alg in ["enum","cc","action","gl2action"] do
        assert GL2SimilarityCounts(H:Algorithm:=alg,Primitive:=true) eq [bc[i]:i in P];
    end for;
    G := GL(2,Integers(N));
    for i:=1 to 2 do
        g := Random(G); j := Index(S,GL2SimilarityInvariant(g));
        for alg in ["enum","cc","action","gl2action"] do
            assert GL2SimilarityCount(H,g:Algorithm:=alg) eq bc[j];
        end for;
    end for;
end for;

print "  SL2SimilarityCounts(H)";
for N in [4,6,9] do
    H := SL2Intersection(GL2Borel(N));  // full-det intersection, so the action algorithm is valid
    S := SL2SimilaritySet(N);
    bc := [0:i in [1..#S]];
    for h in H do bc[Index(S,GL2SimilarityInvariant(h))] +:= 1; end for;
    for alg in ["enum","cc","action","defaultoraction"] do
        assert SL2SimilarityCounts(H:Algorithm:=alg) eq bc;
    end for;
    assert SL2SimilarityCounts(H:Sparse:=true) eq [[i,bc[i]]:i in [1..#bc]|bc[i] ne 0];
    assert SL2SimilarityCounts(H:Primitive:=true) eq [bc[i]:i in P] where P := SL2PrimitiveSimilarityIndexes(N);
end for;

print "  GL2MaximalA5";
for p in [11,19] do
    H := GL2MaximalA5(p);
    assert #BaseRing(H) eq p and #H eq 60*(p-1);          // full preimage of projective A5
    assert H`Order eq #H and H`Index eq GL2Size(p) div #H;
    Z := GL2Scalars(p);
    assert Z subset H;
    Q := quo<H|H meet Z>;
    assert #Q eq 60 and IsPerfect(Q);                      // projective image is A5
    assert GL2DeterminantIndex(H) eq 2;
    assert GL(2,Integers(p))![-1,0,0,-1] in H;
end for;

print "  GL2ConjugateSubgroup/GL2IsConjugateSubgroup";
for N in [5,8] do
    G := GL(2,Integers(N));
    H := GL2Borel(N);
    g0 := Random(G);
    K := sub<G|[h^g0 : h in Generators(GL2Borel1(N))]>;
    b, c := GL2IsConjugateSubgroup(H,K);
    assert b and K^c subset H;
    c := GL2ConjugateSubgroup(H,K);
    assert K^c subset H;
    K2 := sub<G|Generators(GL2Borel1(N))>;   // already inside H: conjugator must be the identity
    assert IsIdentity(GL2ConjugateSubgroup(H,K2));
    b,c := GL2IsConjugateSubgroup(H,K2);
    assert b and IsIdentity(c);
    assert not GL2IsConjugateSubgroup(H,G);  // full group is not conjugate into a Borel
    K3 := GL2Lift(K2,2*N);                   // compatible level multiple
    b, c := GL2IsConjugateSubgroup(H,K3);
    assert b and K3^c subset GL2Lift(H,2*N);
end for;
assert GL2IsConjugateSubgroup(GL2Ambient(1),GL2Borel(7));  // level-1 H contains everything

print "  GL2MinimizeGenerators/SL2MinimizeGenerators";
for N in [8,32] do  // exercises both the N le 16 and N gt 16 branches
    G := GL(2,Integers(N));
    B := GL2Borel(N);
    H := sub<G|[Random(B):i in [1..8]] cat [B.i : i in [1..Ngens(B)]]>;
    M := GL2MinimizeGenerators(H);
    assert M eq B;
    assert Ngens(M) le 7;  // Borel(8) and Borel(32) have Frattini rank 5
    HS := SL2Intersection(B);
    MS := SL2MinimizeGenerators(HS);
    assert SL2Order(MS) eq SL2Order(HS) and MS subset HS;
end for;
C13 := GL2SplitCartan(13);  // abelian branch: AbelianBasis gives 2 generators
M := GL2MinimizeGenerators(C13);
assert M eq C13 and Ngens(M) le 2;

print "  GL2Standardize";
for N in [5,7] do
    G := GL(2,Integers(N));
    for T in [* GL2Borel(N), GL2SplitCartan(N), GL2NonsplitCartan(N), GL2Borel1(N), GL2SplitCartan1(N), GL2SplitCartanNormalizer(N), GL2NonsplitCartanNormalizer(N) *] do
        c := Random(G);
        H := sub<G|[h^c : h in Generators(T)]>;
        SH, a := GL2Standardize(H);
        assert SH eq Conjugate(H,a) and GL2Order(SH) eq GL2Order(T);
    end for;
end for;
G7 := GL(2,Integers(7)); c7 := Random(G7);
BH := sub<G7|[h^c7 : h in Generators(GL2Borel(7))]>;
SH := GL2Standardize(BH);
assert &and[g[2][1] eq 0 : g in Generators(SH)];  // Borel conjugate standardizes to upper triangular

print "  GL2SimilarityClassRepMap/SL2SimilarityClassRepMap";
for N in [8,12] do
    r1 := GL2SimilarityClassRepMap(N);
    assert &and[GL2SimilarityInvariant(r1(s)) eq s : s in GL2SimilaritySet(N)];
    rs := SL2SimilarityClassRepMap(N);
    assert &and[Determinant(m) eq 1 and GL2SimilarityInvariant(m) eq s where m := rs(s) : s in SL2SimilaritySet(N)];
end for;

// =============================== lines 2012-2678 (auditor B) ===============================
print "  GL2SimilarityClasses/Counts/Invariant vs brute force";
// GL2ConjugacyClassCount(p^e) = p^2e - p^(e-1) (Williams thesis Thm 4.3.8 / arXiv:0708.1608);
// everything below is verified against Magma's own ConjugacyClasses
for N in [2..12] cat [16] do
    G := GL(2,Integers(N));
    S := GL2SimilaritySet(N);
    assert #S eq GL2ConjugacyClassCount(N);
    assert GL2SimilarityClassCount(N) eq #S;
    if IsOdd(N) then _ := GL2ConjugacyClasses(N); end if; // exercise both cache paths
    cnts := GL2SimilarityCounts(N);
    assert &+cnts eq GL2Size(N);
    CC := ConjugacyClasses(G);
    assert #CC eq #S;
    T := [0:i in [1..#S]];
    for c in CC do
        i := Index(S,GL2SimilarityInvariant(c[3]));
        assert i gt 0;
        T[i] +:= c[2];
        assert c[2] eq GL2SimilarityClassSize(c[3]);      // sslen formula = true class size
        assert c[2] eq GL2ConjugacyClassSize(c[3]);
    end for;
    assert T eq cnts;  // similarity invariant <-> conjugacy class bijection with correct sizes
    rep := GL2SimilarityClassRepMap(N);
    for i:=1 to #S do
        assert GL2SimilarityInvariant(rep(S[i])) eq S[i]; // round trip
    end for;
    f := GL2SimilarityClassMap(N); idx := GL2SimilarityClassIndexMap(N);
    szmap := GL2SimilarityClassSizeMap(N);
    for t:=1 to 8 do
        g := Random(G);
        v := GL2SimilarityInvariant(g);
        assert f(g) eq v;
        assert idx(g) eq Index(S,v);
        assert szmap(v) eq GL2SimilarityClassSize(g);
    end for;
    SC := GL2SimilarityClasses(N);
    assert #SC eq #S;
    for i:=1 to #SC do
        assert SC[i][1] eq S[i] and GL2SimilarityInvariant(SC[i][2]) eq S[i];
    end for;
    CCL := GL2ConjugacyClasses(N);
    assert #CCL eq #S;
    for i:=1 to #CCL do
        r := CCL[i];
        assert r[4] eq S[i] and GL2SimilarityInvariant(r[3]) eq S[i];
        assert Order(r[3]) eq r[1] and r[2] eq cnts[i];
    end for;
    assert {* <c[1],c[2]> : c in CC *} eq {* <r[1],r[2]> : r in CCL *};
    R := GL2SimilarityReps(N);
    assert #R eq #S;
    for i:=1 to #R do assert GL2SimilarityInvariant(R[i]) eq S[i]; end for;
end for;

print "  GL2Similarity* at larger prime powers";
for N in [25,27] do
    G := GL(2,Integers(N));
    S := GL2SimilaritySet(N);
    assert #S eq GL2ConjugacyClassCount(N);
    cnts := GL2SimilarityCounts(N);
    assert &+cnts eq GL2Size(N);
    rep := GL2SimilarityClassRepMap(N);
    for i:=1 to #S do assert GL2SimilarityInvariant(rep(S[i])) eq S[i]; end for;
    for t:=1 to 2 do
        g := Random(G);
        assert GL2SimilarityClassSize(g) eq (#G div #Centralizer(G,g));
    end for;
end for;

print "  SL2Similarity*";
for N in [2..12] do
    SL := SL(2,Integers(N));
    SS := SL2SimilaritySet(N);
    assert #SS eq SL2SimilarityClassCount(N);
    scnts := SL2SimilarityCounts(N);
    assert &+scnts eq SL2Size(N);
    f := SL2SimilarityClassMap(N);
    T := [0:i in [1..#SS]];
    for g in SL do i := Index(SS,f(g)); assert i gt 0; T[i] +:= 1; end for;
    assert T eq scnts;  // brute force count over all of SL2
    idx := SL2SimilarityClassIndexMap(N);
    for t:=1 to 5 do g := Random(SL); assert idx(g) eq Index(SS,f(g)); end for;
    reps := SL2SimilarityReps(N);
    SCL := SL2SimilarityClasses(N);
    GCL := SL2GL2ConjugacyClasses(N);
    assert #reps eq #SS and #SCL eq #SS and #GCL eq #SS;
    for i:=1 to #SS do
        assert GL2SimilarityInvariant(reps[i]) eq SS[i] and Determinant(reps[i]) eq 1;
        assert SCL[i][1] eq SS[i] and GL2SimilarityInvariant(SCL[i][2]) eq SS[i];
        assert GCL[i][4] eq SS[i] and Order(GCL[i][3]) eq GCL[i][1] and GCL[i][2] eq scnts[i];
    end for;
end for;

print "  GL2IsConjugate/GL2Conjugator";
for N in [3,4,5,6,8,9,12] do
    G := GL(2,Integers(N));
    for t:=1 to 3 do
        g := Random(G); h := g^Random(G);
        assert GL2IsConjugate(g,h);
        c := GL2Conjugator(g,h); assert g^c eq h;
        c := GL2Conjugator(G,g,h); assert g^c eq h;
        g2 := Random(G);
        assert GL2IsConjugate(g,g2) eq IsConjugate(G,g,g2);
    end for;
end for;

print "  GL2/SL2 PrimitiveSimilarity (divisions)";
for N in [2..9] cat [12] do
    SC := GL2SimilarityClasses(N);
    ind := GL2SimilarityClassIndexMap(N);
    n := #SC;
    // brute-force division minima: classes of generators of the same cyclic group
    done := [false:i in [1..n]]; mins := [];
    for i:=1 to n do
        if done[i] then continue; end if;
        Append(~mins,i);
        g := SC[i][2]; o := Order(g);
        for m in [1..o-1] do if GCD(m,o) eq 1 then done[ind(g^m)] := true; end if; end for;
        done[i] := true;
    end for;
    I := GL2PrimitiveSimilarityIndexes(N:NoFile:=true,NoCache:=true);
    assert IndexedSet(mins) eq I;
    if N le 7 then // divisions <-> conjugacy classes of cyclic subgroups (all orders)
        G := GL(2,Integers(N));
        assert #[r : r in Subgroups(G) | IsCyclic(r`subgroup)] eq #I;
    end if;
    S := GL2SimilaritySet(N); cnts := GL2SimilarityCounts(N);
    assert GL2PrimitiveSimilaritySet(N) eq {@ S[i] : i in I @};
    assert GL2PrimitiveSimilarityClasses(N) eq [SC[i] : i in I];
    assert GL2PrimitiveSimilarityCounts(N) eq [cnts[i] : i in I];
    assert GL2PrimitiveSimilarityClassCount(N) eq #I;
    preps := GL2PrimitiveSimilarityReps(N);
    pidx := GL2PrimitiveSimilarityClassIndexMap(N);
    PS := GL2PrimitiveSimilaritySet(N);
    for j:=1 to #PS do
        assert GL2SimilarityInvariant(preps[j]) eq PS[j] and pidx(preps[j]) eq j;
    end for;
    for i in [1..n] do if not (i in I) then assert pidx(SC[i][2]) eq 0; end if; end for;
    // SL2 primitive classes = det-1 divisions of GL2 (divisions preserve determinant 1)
    SS := SL2SimilaritySet(N);
    expected := [Index(SS,S[i]) : i in I | Index(SS,S[i]) gt 0];
    Isl := SL2PrimitiveSimilarityIndexes(N:NoFile:=true,NoCache:=true);
    assert IndexedSet(expected) eq IndexedSet([i:i in Isl]);
    assert SL2PrimitiveSimilaritySet(N) eq {@ SS[i] : i in Isl @};
    SCL := SL2SimilarityClasses(N);
    assert SL2PrimitiveSimilarityClasses(N) eq [SCL[i]:i in Isl];
    assert SL2PrimitiveSimilarityCounts(N) eq [SL2SimilarityCounts(N)[i] : i in Isl];
    assert SL2PrimitiveSimilarityClassCount(N) eq #Isl;
    spreps := SL2PrimitiveSimilarityReps(N);
    spidx := SL2PrimitiveSimilarityClassIndexMap(N);
    SPS := SL2PrimitiveSimilaritySet(N);
    for j:=1 to #SPS do
        assert GL2SimilarityInvariant(spreps[j]) eq SPS[j] and spidx(spreps[j]) eq j;
    end for;
end for;

print "  GL2SimilarityCounts(H)/GL2SimilarityCount across algorithms";
for N in [6,8] do
    G := GL(2,Integers(N));
    subs := [* GL2Borel(N), GL2NonsplitCartan(N), GL2SplitCartanNormalizer(N) *];
    cnt := 0;
    while cnt lt 2 do
        H := sub<G|[Random(G),Random(G)]>;
        if GL2Index(H) gt 1 then Append(~subs,H); cnt +:= 1; end if;
    end while;
    C := GL2SimilarityClasses(N);
    cntsN := GL2SimilarityCounts(N);
    ind := GL2SimilarityClassIndexMap(N);
    I := GL2PrimitiveSimilarityIndexes(N);
    for H in subs do
        base := GL2SimilarityCounts(H:Algorithm:="enum");
        assert &+base eq GL2Order(H);
        for alg in ["cc","action","gl2action"] do
            assert GL2SimilarityCounts(H:Algorithm:=alg) eq base;
        end for;
        for alg in ["enum","cc","action","gl2action"] do
            assert GL2SimilarityCounts(H:Algorithm:=alg,Primitive:=true) eq [base[i]:i in I];
        end for;
        for t:=1 to 2 do
            i := Random([1..#C]); g := C[i][2];
            for alg in ["enum","cc","action","gl2action"] do
                assert GL2SimilarityCount(H,g:Algorithm:=alg) eq base[i];
            end for;
        end for;
        // permutation characters are rational: counts/classsize constant on divisions
        for i in I do
            g := C[i][2]; o := Order(g);
            v := base[i]/cntsN[i];
            for m in [2..o-1] do
                if GCD(m,o) eq 1 then j := ind(g^m); assert base[j]/cntsN[j] eq v; end if;
            end for;
        end for;
    end for;
end for;

print "  SL2SimilarityCounts(H)";
for N in [6,8] do
    SL := SL2Ambient(N);
    K := SL2Intersection(GL2Borel(N));
    base := SL2SimilarityCounts(K:Algorithm:="enum");
    assert &+base eq SL2Order(K);
    assert SL2SimilarityCounts(K:Algorithm:="cc") eq base;
    assert SL2SimilarityCounts(K:Algorithm:="action") eq base; // valid: K = SL2 meet full-det group
    I := SL2PrimitiveSimilarityIndexes(N);
    assert SL2SimilarityCounts(K:Algorithm:="enum",Primitive:=true) eq [base[i]:i in I];
    assert SL2SimilarityCounts(K:Algorithm:="cc",Primitive:=true) eq [base[i]:i in I];
    for t:=1 to 2 do
        K2 := sub<SL|[Random(SL),Random(SL)]>; K2`SL := true;
        b2 := SL2SimilarityCounts(K2:Algorithm:="enum");
        assert &+b2 eq #K2;
        assert SL2SimilarityCounts(K2:Algorithm:="cc") eq b2;
    end for;
end for;

print "  GL2ScalarPrimitiveSimilarityIndexes";
for N in [5] do
    G := GL(2,Integers(N));
    z := PrimitiveRoot(N);
    for Zgens in [[G![-1,0,0,-1]],[G![z,0,0,z]]] do
        Z := sub<G|Zgens>;
        J := GL2ScalarPrimitiveSimilarityIndexes(Z);
        C := GL2SimilarityClasses(N);
        I := GL2PrimitiveSimilarityIndexes(N);
        pind := GL2PrimitiveSimilarityClassIndexMap(N);
        exp := [];
        for pos:=1 to #I do
            i := I[pos]; g := C[i][2];
            if g[1][2] eq 0 and g[2][1] eq 0 and g[1][1] eq g[2][2] then continue; end if;
            orb := { p : p in { pind(zz*g) : zz in Z } | p gt 0 };
            if Min(orb) eq pos then Append(~exp,i); end if;
        end for;
        assert J eq IndexedSet(exp);
    end for;
end for;

print "  similarity N=1 edge cases";
assert GL2ConjugacyClassCount(1) eq 1;
assert #GL2SimilaritySet(1) eq 1;
assert GL2SimilarityCounts(1) eq [1];
assert #GL2SimilarityClasses(1) eq 1;
assert #GL2ConjugacyClasses(1) eq 1;
assert #SL2SimilaritySet(1) eq 1;
assert SL2SimilarityClassCount(1) eq 1;
assert GL2SimilarityClassCount(1) eq 1;
assert #GL2PrimitiveSimilarityIndexes(1) eq 1;

print "  GL2MaximalA5";
for p in [11,19] do
    H := GL2MaximalA5(p);
    assert #BaseRing(H) eq p and #H eq 60*(p-1);
    assert GL2DeterminantIndex(H) eq 2;
    G := GL(2,Integers(p)); z := PrimitiveRoot(p);
    assert G![z,0,0,z] in H;
    Q := quo<H|sub<H|[G![z,0,0,z]]>>;
    assert #Q eq 60 and IdentifyGroup(Q) eq <60,5>;  // projective image is A5
    assert GL2Level(H) eq p;
end for;
ok := false; try _ := GL2MaximalA5(13); catch e; ok := true; end try; assert ok; // 13 = 3 mod 5

print "  GL2MinimizeGenerators/SL2MinimizeGenerators";
for H in [* GL2Borel(8), GL2NonsplitCartan(9), GL2SplitCartan(15), GL2Ambient(12), GL2Borel(25), sub<GL(2,Integers(8))|> *] do
    assert GL2MinimizeGenerators(H) eq H;
end for;
K := SL2Intersection(GL2Borel(8)); K2 := SL2MinimizeGenerators(K); assert K2 eq K and assigned K2`SL;
KA := SL2Intersection(GL2SplitCartan(7)); assert SL2MinimizeGenerators(KA) eq KA;
K := SL2Intersection(GL2Borel(25)); assert SL2MinimizeGenerators(K) eq K;

print "  GL2Standardize";
for N in [5,8] do
    G := GL(2,Integers(N));
    for H0 in [* GL2Borel(N), GL2Borel1(N), GL2SplitCartan(N), GL2NonsplitCartan(N) *] do
        H := Conjugate(H0,Random(G));
        K, a := GL2Standardize(H);
        assert K eq Conjugate(H,a);
        assert K eq H0;   // recovered the standard model
    end for;
end for;
G2 := GL(2,Integers(2)); // small-N edge cases
for H0 in [* sub<G2|>, sub<G2|[G2![1,1,0,1]]>, sub<G2|[G2![0,1,1,1]]>, G2 *] do
    K,a := GL2Standardize(H0); assert K eq Conjugate(H0,a);
end for;

print "  GL2ConjugateSubgroup/GL2IsConjugateSubgroup";
for N in [9,15] do
    G := GL(2,Integers(N));
    H := GL2Borel(N);
    K := Conjugate(GL2Borel1(N),Random(G));
    b,g := GL2IsConjugateSubgroup(H,K); assert b and Conjugate(K,g) subset H;
    g := GL2ConjugateSubgroup(H,K); assert Conjugate(K,g) subset H;
    g := GL2ConjugateSubgroup(H,GL2Borel1(N)); assert IsIdentity(g);
    assert not GL2IsConjugateSubgroup(GL2Borel(N),GL2NonsplitCartan(N));
end for;
H5 := GL2Borel(5);  // cross-level: H at level 5, K at level 15
K := Conjugate(GL2Lift(GL2Borel1(5),15),Random(GL(2,Integers(15))));
b,g := GL2IsConjugateSubgroup(H5,K); assert b and Conjugate(K,g) subset GL2Lift(H5,15);
g := GL2ConjugateSubgroup(H5,K); assert Conjugate(K,g) subset GL2Lift(H5,15);
b,g := GL2IsConjugateSubgroup(GL2Ambient(9),GL2Ambient(1)); assert b; // K = GL(2,Zhat)
assert IsIdentity(GL2ConjugateSubgroup(GL2Ambient(9),GL2Ambient(1)));

// =============================== lines 2679-3364 ===============================
// ---- audit fragment for gl2base.m lines 2679-3364 ----
print "  GL2SimilarityAlgorithms";
for N in [4,5,8] do
    QT2679 := GL2QuadraticTwists(GL2Borel(N));
    smp2679 := [GL2Borel(N), GL2CartanNormalizer(-4,N)] cat (#QT2679 gt 1 select [QT2679[2]] else []);
    for H in smp2679 do
        S1 := GL2SimilaritySet(H:Algorithm:="enum");
        assert S1 eq GL2SimilaritySet(H:Algorithm:="cc");
        M1 := GL2SimilarityMultiset(H:Algorithm:="enum");
        assert M1 eq GL2SimilarityMultiset(H:Algorithm:="cc");
        assert #M1 eq #H and Set(M1) eq S1;
        assert GL2SimilarityIndexes(H:Algorithm:="enum") eq GL2SimilarityIndexes(H:Algorithm:="cc");
        if GL2DeterminantIndex(H) eq 1 and GL2Index(H) gt 1 then
            assert S1 eq GL2SimilaritySet(H:Algorithm:="action");
            assert S1 eq GL2SimilaritySet(H:Algorithm:="gl2action");
            assert M1 eq GL2SimilarityMultiset(H:Algorithm:="action");
        end if;
        assert GL2PrimitiveSimilaritySet(H:Algorithm:="enum") eq GL2PrimitiveSimilaritySet(H:Algorithm:="cc");
        assert GL2PrimitiveSimilarityCounts(H) eq GL2SimilarityCounts(H:Primitive:=true);
        assert GL2PrimitiveSimilarityIndexes(H) eq [i:i in [1..#C]|C[i] gt 0] where C := GL2PrimitiveSimilarityCounts(H);
        assert #GL2PrimitiveSimilarityMultiset(H) eq &+GL2PrimitiveSimilarityCounts(H);
    end for;
end for;

print "  GL2PrimitiveSimilarityLists";
for N in [4,5] do
    G := GL2Ambient(N);
    for H in [GL2Borel(N), GL2CartanNormalizer(-4,N)] do
        pind := GL2PrimitiveSimilarityClassIndexMap(N);
        cnts := GL2PrimitiveSimilarityCounts(H);
        for alg in ["enum","cc","action"] do
            I,f := GL2PrimitiveSimilarityLists(H:Algorithm:=alg);
            assert I eq [i : i in [1..#cnts] | cnts[i] gt 0];
            for i in I do
                L := f(i);
                assert &and[l in H and pind(G!l) eq i : l in L];
                X := &join[Conjugates(H,H!l) : l in L];
                assert #X eq &+[#Conjugates(H,H!l) : l in L];  // reps lie in distinct H-classes
                assert #X eq cnts[i];                          // and cover all of H's part of the class
            end for;
        end for;
    end for;
end for;

print "  SL2Similarity";
for N in [4,5,8] do
    Hs2679 := [SL2Ambient(N)];
    M2679,K2679 := SL2Level(GL2Borel(N)); if M2679 eq N then Append(~Hs2679,K2679); end if;
    for H in Hs2679 do
        S1 := SL2SimilaritySet(H:Algorithm:="enum");
        assert S1 eq SL2SimilaritySet(H:Algorithm:="cc");
        M1 := SL2SimilarityMultiset(H:Algorithm:="enum");
        assert M1 eq SL2SimilarityMultiset(H:Algorithm:="cc");
        assert #M1 eq SL2Order(H) and Set(M1) eq S1;
        assert SL2SimilarityIndexes(H:Algorithm:="enum") eq SL2SimilarityIndexes(H:Algorithm:="cc");
        cnts := SL2PrimitiveSimilarityCounts(H);
        I,f := SL2PrimitiveSimilarityLists(H);
        assert I eq [i:i in [1..#cnts]|cnts[i] gt 0];
        for i in I do
            X := &join[Conjugates(H,H!l) : l in f(i)];
            assert #X eq cnts[i];
        end for;
    end for;
end for;
H2679 := SL2Ambient(5);
assert SL2PrimitiveSimilarityCounts(H2679) eq SL2SimilarityCounts(H2679:Primitive:=true);
assert SL2PrimitiveSimilaritySet(H2679) eq SL2SimilaritySet(H2679:Primitive:=true);
assert SL2PrimitiveSimilarityIndexes(H2679) eq SL2SimilarityIndexes(H2679:Primitive:=true);
// SL2PrimitiveSimilarityMultiset dispatch (was calling the GL2 version; fixed in 2026-08 audit)
assert SL2PrimitiveSimilarityMultiset(H2679) eq SL2SimilarityMultiset(H2679:Primitive:=true);

print "  SignatureSums";
psi2679 := func<n|n eq 1 select 1 else Integers()!(n*&*[1+1/p : p in PrimeDivisors(n)])>;
for N in [2..10] do
    for H in [GL2Ambient(N), GL2Borel(N), GL2CartanNormalizer(-4,N)] do
        os := GL2OrbitSignature(H,N);
        assert &+[r[2]*r[3] : r in os] eq N^2-1;              // orbits partition nonzero vectors
        ks := GL2KummerSignature(H,N);
        t := IsEven(N) select 4 else 1;                       // # 2-torsion vectors in (Z/N)^2
        assert &+[r[2]*r[3] : r in ks] eq ExactQuotient(N^2-t,2) + (t-1);  // orbits partition ((Z/N)^2-0)/<-1>
        isg := GL2IsogenySignature(H,N);
        assert &+[r[2]*r[3] : r in isg] eq &+[psi2679(d) : d in Divisors(N) | d gt 1]; // psi(d) cyclic submodules of order d
        NN,HH := GL2Level(H);
        if NN gt 1 then
            cs := GL2ClassSignature(HH);
            assert &+[r[4]*r[5] : r in cs] eq #HH;            // conjugacy classes partition H
        end if;
    end for;
    os := SL2OrbitSignature(SL2Ambient(N),N);
    assert &+[r[2]*r[3] : r in os] eq N^2-1;
end for;

print "  TorsionIsogenyDegrees";
ordcnt2679 := func<N|#[1 : a in [0..N-1], b in [0..N-1] | GCD([a,b,N]) eq 1]>;
for N in [2..10] do
    assert GL2TorsionDegree(GL2Ambient(N),N) eq ordcnt2679(N); // full GL2 is transitive on order-N points
    assert GL2IsogenyDegree(GL2Ambient(N),N) eq psi2679(N);    // and on cyclic order-N submodules
    assert GL2TorsionDegree(GL2Borel(N),N) eq EulerPhi(N);     // X_0(N): kernel point defined over degree phi(N)
    assert GL2TorsionDegree(GL2Borel1(N),N) eq 1;              // X_1(N): rational point of order N
    assert GL2IsogenyDegree(GL2Borel(N),N) eq 1;               // X_0(N): rational cyclic N-isogeny
end for;
assert GL2TorsionDegree(GL2Borel(5)) eq 4;
assert GL2IsogenyDegree(GL2Borel(7)) eq 1;

print "  GassmannSignatures";
for N in [4,6,8] do
    G := GL2Ambient(N);
    for H in [GL2Borel(N), GL2CartanNormalizer(-3,N)] do
        r := Random(G);
        assert GL2GassmannSignature(H) eq GL2GassmannSignature(H^r);
        assert GL2GassmannSignature(H:old:=true) eq GL2GassmannSignature(H^r:old:=true);
        assert GL2GassmannHash(H) eq GL2GassmannHash(H^r);
        assert GL2SubgroupKey(H) eq GL2SubgroupKey(H^r);
        NN,HH := GL2Level(H);
        assert GL2SubgroupKey(H) eq GL2SubgroupKey(GL2OrbitSignature(HH),GL2GassmannSignature(HH));
        M2679,K2679 := SL2Level(H);
        if M2679 gt 1 then
            GM := GL(2,Integers(M2679));
            K2 := sub<GM|[GM!h : h in Generators(K2679)]>^Random(GM); K2`SL := true;
            assert SL2GassmannSignature(K2679) eq SL2GassmannSignature(K2);
            assert SL2GassmannHash(K2679) eq SL2GassmannHash(K2);
            assert SL2SubgroupKey(K2679) eq SL2SubgroupKey(K2);
        end if;
    end for;
end for;
assert GL2GassmannSignature(GL2Borel(8)) ne GL2GassmannSignature(GL2CartanNormalizer(-4,8));

print "  Canonicalize";
for N in [4,5,6,8] do
    G := GL2Ambient(N);
    smp2679 := [GL2Borel(N), GL2CartanNormalizer(-4,N), GL2CartanNormalizer(-3,N)];
    QT2679 := GL2QuadraticTwists(GL2Borel(N));
    smp2679 cat:= QT2679[2..#QT2679];
    for H0 in smp2679 do
        if GL2DeterminantIndex(H0) ne 1 then continue; end if;
        K2679,g2679 := GL2Canonicalize(H0);
        NH,H1 := GL2Level(H0);
        if NH eq 1 then continue; end if;
        assert K2679 eq H1^g2679;                                   // documented property of 2nd return value
        assert GL2CanonicalGenerators(H0) eq GL2CanonicalGenerators(H0^Random(G));  // conjugation invariance
    end for;
end for;
for N in [4,5,8] do
    GN := GL(2,Integers(N));
    Hs2679 := [];
    M2679,K2679 := SL2Level(GL2Borel(N)); if M2679 eq N then Append(~Hs2679,K2679); end if;
    M2679,K2679 := SL2Level(GL2CartanNormalizer(-4,N)); if M2679 eq N then Append(~Hs2679,K2679); end if;
    for H in Hs2679 do
        K2679,g2679 := SL2Canonicalize(H);
        M1,H1 := SL2Level(H);
        assert K2679 eq H1^g2679;
        r := Random(GN);
        H2 := sub<GN|[GN!(r^-1*h*r) : h in Generators(H)]>; H2`SL := true;
        assert SL2CanonicalGenerators(H2) eq SL2CanonicalGenerators(H);
    end for;
end for;
// fine (no -I) SL2 subgroups at N=4: canonicalization is a GL2-conjugacy invariant
SL42679 := SL2Ambient(4); G42679 := GL(2,Integers(4));
for K0 in [K`subgroup : K in Subgroups(SL42679) | not -Identity(SL42679) in K`subgroup and #K`subgroup gt 1] do
    K2679 := sub<G42679|[G42679!g : g in Generators(K0)]>; K2679`SL := true;
    r := Random(G42679);
    K2 := sub<G42679|[G42679!(r^-1*g*r) : g in Generators(K0)]>; K2`SL := true;
    assert SL2CanonicalGenerators(K2679) eq SL2CanonicalGenerators(K2);
end for;
// level reduction happens before canonicalization
assert GL2CanonicalGenerators(GL2Lift(GL2Borel(5),15)) eq GL2CanonicalGenerators(GL2Borel(5));

print "  MinimalGenerators";
for N in [3,4,5] do
    G := GL(2,Integers(N));
    for K0 in [K`subgroup : K in Subgroups(G) | K`order le 48] do
        NN,KK := GL2Level(K0);
        if NN eq 1 then continue; end if;
        gens := GL2MinimalGenerators(KK);
        // independent reimplementation of the documented greedy lex-minimal algorithm
        S := {Eltseq(h) : h in KK} diff {Eltseq(Identity(KK))};
        bgens := [];
        while #S gt 0 do
            Append(~bgens,Min(S)); Kc := sub<KK|bgens>;
            if #Kc eq #KK then break; end if;
            S diff:= {Eltseq(x) : x in Kc};
        end while;
        assert gens eq bgens;
        assert sub<KK|gens> eq KK;
    end for;
end for;

print "  GL2MinimalConjugate";
// The audit-flagged pruning bug (GrpMatElt vs Eltseq ordering) is fixed: Magma's element order over
// Z/4 (and only Z/4) compares packed rows little-endian, i.e. by (b,a,d,c), so pruning by GrpMatElt
// Min discarded the conjugate containing the Eltseq-minimal elements (12 of 58 classes at N=4).
// Verified 2026-08-09: zero published/beta labels depend on the changed outputs (the RSZB tiebreaker
// never fires at level 4, and the paper pipeline used a different, correct implementation).
// Exhaustive brute-force check at N=4 (the only affected modulus), including the audit repro:
assert GL2MinimalConjugate(sub<GL(2,Integers(4))|[3,2,0,3]>) eq [[1,2,2,1]];
G4 := GL(2,Integers(4));
for K0 in [K`subgroup : K in Subgroups(G4)] do
    NN,KK := GL2Level(K0);
    if NN ne 4 then continue; end if;
    a := GL2MinimalConjugate(KK);
    b := Min([GL2MinimalGenerators(Conjugate(KK,t)) : t in GL2RightTransversal(Normalizer(G4,KK))]);
    assert a eq b;
end for;
for N in [3,5] do
    G := GL(2,Integers(N));
    for K0 in [K`subgroup : K in Subgroups(G) | K`order le 48] do
        NN,KK := GL2Level(K0);
        if NN eq 1 then continue; end if;
        if Index(G,Normalizer(G,KK)) gt 200 then continue; end if;
        a := GL2MinimalConjugate(KK);
        b := Min([GL2MinimalGenerators(Conjugate(KK,t)) : t in GL2RightTransversal(Normalizer(G,KK))]);
        assert a eq b;
    end for;
end for;
a2679 := GL2MinimalConjugate(GL2Borel(4));
assert IsConjugate(GL2Ambient(4),sub<GL2Ambient(4)|a2679>,GL2Borel(4));

print "  Refinements";
for N in [2..6] do
    for H in [GL2Ambient(N), GL2Borel(N), GL2CartanNormalizer(-3,N)] do
        NN,HH := GL2Level(H); if NN eq 1 then continue; end if;
        if not GL2ContainsNegativeOne(HH) then continue; end if;
        H2 := GL2Lift(HH,2*NN); nI := -Identity(H2);
        S := [K`subgroup : K in MaximalSubgroups(H2:IndexEqual:=2) | not nI in K`subgroup];
        assert GL2HasRefinements(HH) eq (#S gt 0);   // refinements of level-N H all live at level 2N
        R := GL2Refinements(H2);
        for K in R do assert not -Identity(K) in K and 2*#K eq #H2; end for;
        G2 := GL2Ambient(2*NN);
        for i in [1..#R], j in [i+1..#R] do assert not IsConjugate(G2,R[i],R[j]); end for;
        reps := [];
        for K in S do if &and[not IsConjugate(G2,K,J) : J in reps] then Append(~reps,K); end if; end for;
        assert #reps eq #R;
    end for;
end for;

print "  QuadraticTwists";
assert GL2QuadraticTwists(GL2Ambient(1)) eq [GL2Ambient(1)];
for N in [3,4,5,8] do
    G := GL(2,Integers(N));
    for D in [-7,-11] do
        S := GL2QuadraticTwists(GL2CartanNormalizer(D,N));
        HH := S[1];
        assert -Identity(G) in HH;
        for i:=2 to #S do
            K := S[i];
            assert not -Identity(G) in K;
            assert #K*2 eq #HH;
            assert sub<G|K,-Identity(G)> eq HH;
        end for;
    end for;
end for;

print "  CMTwists";
// brute-force completeness: subgroups K of H with <K,zeta> = H, up to GL2-conjugacy
G52679 := GL(2,Integers(5));
H2679 := GL2CartanNormalizer(-4,5); z42679 := G52679![0,1,-1,0];
T2679 := [K`subgroup : K in Subgroups(H2679) | sub<G52679|K`subgroup,z42679> eq H2679];
reps2679 := [];
for K in T2679 do if &and[not IsConjugate(G52679,K,J) : J in reps2679] then Append(~reps2679,K); end if; end for;
S2679 := GL2QuarticCMTwists(5);
assert #reps2679 eq #S2679 and &and[&or[IsConjugate(G52679,K,J) : J in S2679] : K in reps2679];
for N in [4,5] do
    G := GL(2,Integers(N));
    H := GL2CartanNormalizer(-3,N); z6 := -(G![0,1,-1,-1])^2;
    T := [K`subgroup : K in Subgroups(H) | sub<G|K`subgroup,z6> eq H];
    reps := [];
    for K in T do if &and[not IsConjugate(G,K,J) : J in reps] then Append(~reps,K); end if; end for;
    S := GL2SexticCMTwists(N);
    assert #reps eq #S and &and[&or[IsConjugate(G,K,J) : J in S] : K in reps];
end for;
// cached NegOne attributes on returned twists must be correct
for N in [5,8,9] do
    G := GL(2,Integers(N));
    for S in [GL2QuarticCMTwists(N), GL2SexticCMTwists(N)] do
        for K in S do
            assert (not assigned K`NegOne) or (K`NegOne eq (-Identity(G) in sub<G|[G!g:g in Generators(K)]>));
        end for;
    end for;
end for;
// GL2CMTwists(-3,p) fast path structure (Prop 1.16 of arXiv:1508.07660)
for p in PrimesInInterval(5,40) do
    L := GL2CMTwists(-3,p);
    assert #L eq (p mod 9 in [1,8] select 1 else 2);
    assert L[1] eq GL2CartanNormalizer(-3,p);
    if #L eq 2 then
        assert 3*#L[2] eq #L[1] and GL2DeterminantIndex(L[2]) eq 1;
    end if;
end for;
// D < -3 fast path (Thm 1.2.4 of arXiv:1809.02584): single twist at odd prime power N coprime to D
for D in [-7,-8,-11] do for N in [5,9,25] do
    L := GL2CMTwists(D,N);
    assert #L eq 1 and L[1] eq GL2CartanNormalizer(D,N);
end for; end for;

print "  RationalCMPoints";
// LMFDB oracle (2026-08): SELECT cm, bool_or(l = ANY(isogeny_degrees)) FROM ec_curvedata WHERE cm != 0 GROUP BY cm, for l in {2,3,5,7,11,13}
assert GL2RationalCMPoints(GL2Borel(2)) eq [-3,-4,-7,-8,-12,-16,-28];
assert GL2RationalCMPoints(GL2Borel(3)) eq [-3,-12,-27];
assert GL2RationalCMPoints(GL2Borel(5)) eq [];
assert GL2RationalCMPoints(GL2Borel(7)) eq [-7,-28];
assert GL2RationalCMPoints(GL2Borel(11)) eq [-11];
assert GL2RationalCMPoints(GL2Borel(13)) eq [];
assert GL2RationalCMPoints(GL2Ambient(5)) eq [-3,-4,-7,-8,-11,-12,-16,-19,-27,-28,-43,-67,-163];
assert GL2RationalCMPoints(GL2CMTwists(-3,7)[2]) eq [-3];

print "  CMDiscriminantRepresentatives";
cmd2679 := [-3,-4,-7,-8,-11,-12,-16,-19,-27,-28,-43,-67,-163];
for N in [2..15] do
    L := CMDiscriminantRepresentatives(N);
    assert &and[D lt 0 and IsDiscriminant(D) : D in L];
    m := IsEven(N) select 4*N else N;
    resid := {D mod m : D in L};
    if IsEven(N) then assert resid eq {x : x in [0..m-1] | x mod 4 in [0,1]};
    else assert resid eq {x : x in [0..m-1]}; end if;
    assert -3 in L and -4 in L;
    LQ := CMDiscriminantRepresentatives(N:Qonly);
    for D in cmd2679 do assert &or[IsDivisibleBy(D-R,m) : R in LQ]; end for;
end for;

print "  CMMaximalTwists";
for N in [4,5,6] do
    G := GL(2,Integers(N));
    L := GL2CMMaximalTwists(N);
    assert &and[#L[i] ge #L[i+1] : i in [1..#L-1]];
    for i in [1..#L], j in [i+1..#L] do assert not IsConjugate(G,L[i],L[j]); end for;
    for i in [1..#L] do assert GL2ContainsNegativeOne(L[i]); end for;
    L2 := GL2CMTwists(N);
    assert &and[#L2[i] ge #L2[i+1] : i in [1..#L2-1]];
    for K in L do assert &or[IsConjugate(G,K,J) : J in L2 | #J eq #K]; end for;
end for;

print "  GL2RemoveConjugates";
for N in [5,8] do
    G := GL2Ambient(N);
    H := GL2Borel(N); K := GL2CartanNormalizer(-4,N);
    R := GL2RemoveConjugates([H^Random(G), H^Random(G), K^Random(G), H^Random(G), K],G);
    assert #R eq 2;
    assert &or[IsConjugate(G,r,H) : r in R] and &or[IsConjugate(G,r,K) : r in R];
end for;

print "  LevelOneEdges";
G12679 := GL2Ambient(1);
assert GL2OrbitSignature(G12679) eq [] and GL2KummerSignature(G12679) eq [] and GL2IsogenySignature(G12679) eq [];
assert GL2ClassSignature(G12679) eq [];
assert GL2GassmannSignature(G12679:old:=true) eq [];
assert #GL2SimilaritySet(G12679) eq 1 and #GL2SimilarityMultiset(G12679) eq 1;
assert GL2SubgroupKey(G12679) eq djb2("[]")*djb2("[1]");
assert GL2MinimalGenerators(G12679) eq [] and GL2MinimalConjugate(G12679) eq [];

// =============================== regression section ===============================
// ==================================================================================
// Regression tests for the bugs fixed in the 2026-08-06/07 audit of gl2base.m.
// Each block names the bug it pins.
// ==================================================================================
print "  regressions (2026-08 audit fixes)";

// BUG: GL1Project called gl1copyattr with one argument (crash when H`Level assigned and M multiple of it)
P2 := GL1Project(GL1Ambient(4),2); assert #P2 eq 1 and #BaseRing(P2) eq 2;
P2 := GL1Project(GL1Lift(GL1SubgroupFromLabel("4.2.1"),8),4); assert #BaseRing(P2) eq 4;

// BUG: GL1Level crashed via ChangeRing(H,Integers(1)) when H`Level = 1 was cached
lev,K := GL1Level(GL1Ambient(8)); assert lev eq 1 and not IsFinite(BaseRing(K)) and #K eq 1;
assert GL1Label(GL1Ambient(8)) eq "1.1.1";
for lab in GL1Labels(8) do assert GL1Label(GL1Lift(8,lab)) eq lab; end for; // now includes "1.1.1"

// BUG: SL1Ambient(1) returned the degree-2 group sl2N1 instead of sl1N1
assert Degree(SL1Ambient(1)) eq 1 and assigned SL1Ambient(1)`SL;
// BUG: SL1Ambient(R) set NegOne := false even for #R = 2 where -I = I
assert SL1Ambient(Integers(2))`NegOne and not SL1Ambient(Integers(3))`NegOne;

// BUG: GL1Index on the level-1 group asserted gl2N1 (degree mismatch crash) and returned [1] instead of 1
v := GL1Index(sub<GL(1,Integers())|>); assert v eq 1 and Type(v) eq RngIntElt;

// BUG: GL1Characters on the level-1 group asserted gl2N1 (crash)
assert GL1Characters(GL1SubgroupFromLabel("1.1.1")) eq [1];

// BUG: SL2Level second return value was gl2N1 (no SL attribute) when H`Level = 1 was cached
lev,K := SL2Level(SL2Ambient(4)); assert lev eq 1 and assigned K`SL;
assert SL2Lift(K,4) eq SL2Ambient(4);

// BUG: SL2Lifter(M) crashed on the level-1 group sl2N1
assert SL2Lifter(12)(SL2Ambient(1)) eq SL2Ambient(12);

// BUG: PSL2Size/SL2BorelSize had (N:RngIntElt) signature typo (argument type unchecked); values unchanged
for N in [2..24] do
    nsc := #[x : x in [1..N] | x*x mod N eq 1];
    assert PSL2Size(N) eq SL2Size(N) div nsc;
    assert SL2BorelSize(N) eq EulerPhi(N)*N;
end for;

// BUG: GL2TriangularSubgroup set K`NegOne := true whenever H`NegOne was assigned (even false)
K := GL2TriangularSubgroup(GL2Borel1(5)); assert K`NegOne eq false and not -Identity(K) in K;
K := GL2TriangularSubgroup(GL2Borel(5)); assert K`NegOne eq true;

// BUG: GL2Borel1PC returned mutually inconsistent (G,P,pi): G had upper-left-1 generators while
// the presentation/map assumed bottom-right-1, and pi was not a homomorphism (missing /g[1][1])
for N in [2,3,4,5,8,9,12,16] do
    G,P,f := GL2Borel1PC(N);
    R := Integers(N); GG := GL(2,R);
    B1 := sub<GG|[GG![u,0,0,1] : u in [1..N] | GCD(u,N) eq 1] cat [GG![1,1,0,1]]>; // {[a,b;0,1]}
    assert sub<GG|[GG!g:g in Generators(G)]> eq B1;
    assert #B1 eq #P;
    assert #{f(x):x in B1} eq #B1;                     // injective
    for i in [1..20] do a := Random(B1); b := Random(B1); assert f(a*b) eq f(a)*f(b); end for; // homomorphism
end for;

// BUG: GL2Triangular1Subgroup stored T[z] := a*g (breaking the Schreier transversal), consumed the
// broken GL2Borel1PC map, mishandled Upper:=false entirely, and could corrupt H`Order / NegOne.
// Oracle: brute-force H meet Borel1 for both orientations.
for N in [3,4,5,6,7,8,9,12,15,16] do
    R := Integers(N); G := GL(2,R); U := [u : u in [1..N] | GCD(u,N) eq 1];
    B1u := sub<G|[G![u,0,0,1] : u in U] cat [G![1,1,0,1]]>;   // upper triangular, bottom-right 1
    B1l := sub<G|[G![u,0,0,1] : u in U] cat [G![1,0,1,1]]>;   // lower triangular, bottom-right 1
    inputs := [* G, GL2Borel(N), GL2Borel1(N), sub<G|> *];
    for i in [1..4] do Append(~inputs, sub<G|[Random(G),Random(G)]>); end for;
    for i in [1..2] do Append(~inputs, sub<G|[Random(GL2Borel(N))]>); end for;
    for H0 in inputs do
        gens := [Eltseq(g) : g in Generators(H0)];
        Hf := sub<G|gens>;
        K := GL2Triangular1Subgroup(sub<G|gens>);
        BF := Hf meet B1u;
        assert sub<G|[G!g:g in Generators(K)]> eq BF and K`Order eq #BF;
        assert K`NegOne eq (-Identity(G) in BF);
        Hc := sub<G|gens>; _ := GL2Triangular1Subgroup(Hc);      // input Order attribute not corrupted
        assert (not assigned Hc`Order) or Hc`Order eq #Hf;
        K2 := GL2Triangular1Subgroup(sub<G|gens>:Upper:=false);
        BF2 := Hf meet B1l;
        assert sub<G|[G!g:g in Generators(K2)]> eq BF2 and GL2Order(K2) eq #BF2;
    end for;
end for;
G2r := GL(2,Integers(2));
K := GL2Triangular1Subgroup(G2r); assert K eq sub<G2r|[G2r![1,1,0,1]]> and K`NegOne;
// specific case that used to corrupt the input's Order attribute (H`Order was set to 20, true order 4)
G5r := GL(2,Integers(5)); H10 := sub<G5r|[G5r![1,1,0,2]]>;
T10 := GL2Triangular1Subgroup(H10);
assert H10`Order eq 4 and GL2Order(T10) eq 1;

// BUG: GL2Levels crashed at prime N (accessed unassigned H`Level)
G7r := GL(2,Integers(7)); B7 := sub<G7r|[G7r![1,1,0,1],G7r![3,0,0,1],G7r![1,0,0,3]]>;
assert GL2Levels(B7) eq [[1,1],[7,8]];
assert GL2Levels(sub<G7r|[g:g in Generators(G7r)]>) eq [[1,1]];

// BUG: GL2PermutationRepresentation/SL2PermutationRepresentation used the invalid constructor
// map<H->Sym(1)|> (crash) for level-1 and SL2-level-1 (index-1) inputs
r := GL2PermutationRepresentation(GL2Ambient(1)); assert Degree(Image(r)) eq 1;
G12r := GL(2,Integers(12)); Hfull := sub<G12r|[g:g in Generators(G12r)]>;
r := GL2PermutationRepresentation(Hfull); assert #Fix(r(Random(G12r))) eq 1;
assert GL2SimilarityCounts(sub<G12r|[g:g in Generators(G12r)]>:Algorithm:="gl2action")
    eq GL2SimilarityCounts(sub<G12r|[g:g in Generators(G12r)]>:Algorithm:="enum");
r := SL2PermutationRepresentation(SL2Ambient(1)); assert Degree(Image(r)) eq 1;

// BUG: GL2DeterminantReps on the level-1 group returned the integer 1 instead of an Assoc
X := GL2DeterminantReps(GL2Ambient(1)); assert Type(X) eq Assoc and #Keys(X) eq 1;

// BUG: GL2RationalCuspCount(H,q) was wrong (prime level) or crashed (odd prime power level)
// when q = 1 mod N and GL2DeterminantIndex(H) > 1
assert GL2RationalCuspCount(GL2Scalars(3),4) eq 8;      // was 24
assert GL2RationalCuspCount(GL2Scalars(3),7) eq 8;
assert GL2RationalCuspCount(GL2Scalars(3),4) eq GL2RationalCuspCount(GL2Scalars(3),4:slow:=true);
assert GL2RationalCuspCount(GL2Scalars(9),10) eq GL2CuspCount(GL2Scalars(9));  // was a crash
assert GL2RationalCuspCount(GL2Scalars(9),10) eq GL2RationalCuspCount(GL2Scalars(9),10:slow:=true);

// BUG: GL2ArithK1(1,2) set Order := 4 on a group of order 2 (corrupting #H and GL2Index)
H := GL2ArithK1(1,2);
assert H`Order eq 2 and #sub<GL(2,Integers(2))|[Eltseq(g):g in Generators(H)]> eq 2;
assert GL2Index(GL2ArithK1(1,2)) eq 3;

// BUG: GL2CartanNormalizer(D,2) with D = 5 mod 8 (2 inert) is all of GL(2,Z/2) but had Level := 2
H := GL2CartanNormalizer(-3,2); assert #H eq 6 and H`Level eq 1 and GL2Level(H) eq 1;
assert GL2Level(GL2CartanNormalizer(-4,2)) eq 2;        // proper subgroup: level 2 unchanged

// BUG: GL2SplitCartan1/GL2Arith1/GL2Borel1 (and GL2BorelK1 via GL2Borel1) set NegOne := false at N=2
// where -I = I lies in every subgroup
assert GL2SplitCartan1(2)`NegOne and GL2Borel1(2)`NegOne and GL2Arith1(1,2)`NegOne and GL2BorelK1(2)`NegOne;
assert GL2ContainsNegativeOne(GL2Borel1(2));
for N in [3..9] do
    for H in [* GL2SplitCartan1(N), GL2Borel1(N), GL2Arith1(1,N) *] do
        assert H`NegOne eq (-Identity(H) in sub<GL(2,Integers(N))|[Eltseq(g):g in Generators(H)]>);
    end for;
end for;

// BUG: GL2SturmBound(1) crashed on an empty &* (correct value 0 since S_2(SL2(Z)) = 0)
assert GL2SturmBound(1) eq 0;

// BUG: GL2CartanSize(D,1) crashed on an empty &* (correct value 1 = #(O/O)*)
assert GL2CartanSize(-4,1) eq 1 and GL2CartanSize(-3,1) eq 1;

// BUG: SL2BorelPC(1) returned gl2N1 (no SL attribute) instead of sl2N1
B,P,f := SL2BorelPC(1); assert assigned B`SL and #P eq 1;

// BUG: dead copy-paste block in GL2NonsplitCartanNormalizer built (and discarded) a SPLIT Cartan
// at odd primes; deleted.  Values unchanged (oracle: Magma Normalizer of the chosen Cartan).
for p in [5,7,13] do
    CN := GL2NonsplitCartanNormalizer(p);
    assert #CN eq 2*(p^2-1);
    D := -3; while not (IsFundamentalDiscriminant(D) and KroneckerSymbol(D,p) eq -1) do D -:= 4; end while;
    assert CN eq Normalizer(GL2Ambient(p),GL2Cartan(D,p));
end for;
assert #GL2NonsplitCartanNormalizer(9) eq 144 and #GL2NonsplitCartanNormalizer(12) eq 192;

// BUG: GL2IsConjugateSubgroup(H,K) crashed (assert) instead of returning false when K = GL(2,Zhat)
// (level 1) and H is a proper subgroup
assert GL2IsConjugateSubgroup(GL2Borel(7),GL2Ambient(1)) eq false;
b,g := GL2IsConjugateSubgroup(GL2Ambient(9),GL2Ambient(1)); assert b;
assert GL2IsConjugateSubgroup(GL2Ambient(1),GL2Borel(7));

// BUG: GL2SimilarityClassIndexMap(1) returned [] instead of the index 1 (copy-paste from ClassMap)
assert GL2SimilarityClassIndexMap(1)(Identity(GL2Ambient(1))) eq 1;
assert SL2SimilarityClassIndexMap(1)(0) eq 1;
assert GL2PrimitiveSimilarityClassIndexMap(1)(0) eq 1;
assert SL2PrimitiveSimilarityClassIndexMap(1)(0) eq 1;

// BUG: SL2PrimitiveSimilarityMultiset dispatched to GL2SimilarityMultiset (require error on all valid input)
K := SL2Intersection(GL2Borel(8));
assert SL2PrimitiveSimilarityMultiset(K) eq SL2SimilarityMultiset(K:Primitive:=true);

// BUG: GL2TorsionDegree/GL2IsogenyDegree crashed on level-1 input (Divisors(Infinity))
assert GL2TorsionDegree(GL2Ambient(3)) eq 1 and GL2IsogenyDegree(GL2Ambient(3)) eq 1;
assert GL2TorsionDegree(GL2Ambient(1)) eq 1 and GL2IsogenyDegree(GL2Ambient(1)) eq 1;
assert GL2TorsionDegree(GL2Borel(3),1) eq 1 and GL2IsogenyDegree(GL2Borel(3),1) eq 1;

// BUG: GL2SubgroupKey(H:old:=true) crashed (old-style gsig does not match the 2-arg overload's
// signature); now inlined.  Values with old:=false are unchanged.
for H in [* GL2Borel(5), GL2NonsplitCartan(8), GL2SplitCartan(12) *] do
    k := GL2SubgroupKey(H);
    NN,HH := GL2Level(H);
    assert k eq GL2SubgroupKey(GL2OrbitSignature(HH),GL2GassmannSignature(HH));
    kold := GL2SubgroupKey(H:old:=true);
    assert Type(kold) eq RngIntElt;
end for;
// pinned key values (must never change: gl2tab tables are keyed on these)
assert GL2SubgroupKey(GL2Ambient(1)) eq djb2("[]")*djb2("[1]");

// FIXED (audit item 6, 2026-08-09): GL2GassmannSignature/SL2GassmannSignature now return [1] at
// level 1 (GL2SubgroupKey convention, matching GL2SimilarityCounts at level 1 and the hardcoded
// key djb2("[]")*djb2("[1]")), so the two GL2/SL2SubgroupKey overloads now agree at level 1.
// The old:=true form still returns [] at level 1 (pinned in LevelOneEdges above); key values for
// levels > 1 are unchanged (pinned in the GassmannSignatures and GL2SubgroupKey sections above).
assert GL2GassmannSignature(GL2Ambient(1)) eq [1];
assert SL2GassmannSignature(SL2Ambient(1)) eq [1];
assert GL2SubgroupKey(GL2Ambient(1)) eq GL2SubgroupKey(GL2OrbitSignature(GL2Ambient(1)),GL2GassmannSignature(GL2Ambient(1)));
assert SL2SubgroupKey(SL2Ambient(1)) eq GL2SubgroupKey(SL2OrbitSignature(SL2Ambient(1)),SL2GassmannSignature(SL2Ambient(1)));

// FIXED (audit item 7, 2026-08-09): Borel constructors narrowed from R::Rng to R::RngIntRes (their
// Order/Index/Level attributes use Z/N-only formulas; GL2Borel(GF(4)) used to return a corrupted
// group claiming order 16 when the true order is 36).  GF(4) must now fail signature matching.
ok := false; try _ := GL2Borel(GF(4)); catch e ok := true; end try; assert ok;
ok := false; try _ := SL2Borel(GF(4)); catch e ok := true; end try; assert ok;
ok := false; try _ := GL2Borel1(GF(4)); catch e ok := true; end try; assert ok;
ok := false; try _ := GL2Borel12(GF(4)); catch e ok := true; end try; assert ok;
ok := false; try _ := GL2BorelK1(GF(4)); catch e ok := true; end try; assert ok;
ok := false; try _ := GL2BorelK12(GF(4)); catch e ok := true; end try; assert ok;
ok := false; try _ := GL2BorelPC(GF(4)); catch e ok := true; end try; assert ok;
ok := false; try _ := GL2Borel1PC(GF(4)); catch e ok := true; end try; assert ok;
ok := false; try _ := SL2BorelPC(GF(4)); catch e ok := true; end try; assert ok;
B := GL2Borel(Integers(4)); assert B`Order eq GL2BorelSize(4) and B eq GL2Borel(4); // RngIntRes path unchanged

// AUDIT dead code removed (2026-08-09): GL2MaximalS4 unreachable 'elif p mod 8 eq 1' branch
// (a = 1 whenever p mod 8 in [1,7]) and unused variable t; outputs verified bit-identical
// before/after at a fixed seed.  Pin order and conjugacy class of the result (the exact
// representative returned depends on the RNG state via ConjugateToRationalSubgroup).
for t in [* <5,[[1,4,1,1],[2,0,0,2],[3,3,4,1]]>, <7,[[2,1,1,1],[3,0,0,3],[4,1,0,2]]>,
           <13,[[2,0,0,2],[3,0,12,9],[5,3,3,10]]>, <17,[[3,0,0,3],[4,9,3,7],[9,7,4,7]]> *] do
    p := t[1]; H := GL2MaximalS4(p);
    assert GL2Order(H) eq 24*(p-1);
    assert IsConjugate(GL(2,Integers(p)),H,sub<GL(2,Integers(p))|t[2]>);
end for;

// AUDIT dead code removed (2026-08-09): the GL2SimilarityCount catch block's Denominator/Numerator
// lines (ExactQuotient returns an integer or raises; the ExactQuotient retry itself is kept).
g8 := GL2Ambient(8)![1,1,0,1];
assert GL2SimilarityCount(GL2Borel(8),g8) eq #[h : h in GL2Borel(8) | GL2SimilarityInvariant(h) eq GL2SimilarityInvariant(g8)];

// AUDIT dead code removed (2026-08-09): the intrinsic GL2SimilarityClassRepMap2 (an exact
// functional duplicate of GL2SimilarityClassRepMap with zero callers) was removed entirely;
// GL2SimilarityClassRepMap round trips are pinned in the similarity sections above.

// FLAGGED (audit 2026-08-06): SL2PrimitiveSimilarityIndexes(1) returns the SeqEnum [1] where the GL2
// version returns the SetIndx {@ 1 @} (declared return type SetIndx).


print "ALL TESTS PASSED test_gl2base.m";
quit;
