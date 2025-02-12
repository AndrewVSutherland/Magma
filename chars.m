freeze;
/*
    Dependencies: utils.m
    Various functions useful for working with Dirichlet characters, their Galois orbits, and Conrey labels

    Copyright (c) Andrew V. Sutherland, 2019-2025.  See License file for details on copying and usage.
*/

import "utils.m": plog;

intrinsic IsCyclic (N::RngIntElt) -> BoolElt
{ Returns true if (Z/NZ)* is cyclic, false otherwise. }
    return N lt 8 or (N mod 4 eq 2 and IsPrimePower(N div 2)) or IsPrimePower(N);
end intrinsic;

intrinsic Parity (chi::GrpDrchElt) -> RngIntElt
{ The value of the character on -1. }
    return Integers()!Evaluate(chi,-1);
end intrinsic;

intrinsic IsReal (chi::GrpDrchElt) -> BoolElt
{ Whether the character takes only real values (trivial or quadratic) or not. }
    return Order(chi) le 2;
end intrinsic;

intrinsic Degree (chi::GrpDrchElt) -> RngIntElt
{ The degree of the number field Q(chi). }
    return EulerPhi(Order(chi));
end intrinsic;

intrinsic UnitGenerators (chi::GrpDrchElt) -> SeqEnum[RngIntElt]
{ Lift to Z of standard generators for (Z/NZ)* where N is the modulus of chi. }
    return UnitGenerators(Parent(chi));
end intrinsic;

intrinsic UnitGenerators (N::RngIntElt) -> SeqEnum[RngIntElt]
{ Lift to Z of standard generators for (Z/NZ)*. }
    return UnitGenerators(DirichletGroup(N));
end intrinsic;

intrinsic UnitGeneratorOrders (N::RngIntElt) -> SeqEnum[RngIntElt]
{ Lift of orders of standard generators for (Z/NZ)*. }
    G,pi:=MultiplicativeGroup(Integers(N));
    return [Order(Inverse(pi)(n)):n in UnitGenerators(N)];
end intrinsic;

intrinsic UnitGeneratorOrders (chi::GrpDrchElt) -> SeqEnum[RngIntElt]
{ List of orders of standard generators for (Z/NZ)* where N is the modulus of chi. }
    return UnitGeneratorOrders(Modulus(chi));
end intrinsic;

intrinsic Factorization (chi::GrpDrchElt) -> List
{ Returns a list of Dirichlet characters of prime power modulus whose product is equal to chi (the empty list if chi has modulus 1). }
    N := Modulus(chi);  F := Codomain(chi);
    if N eq 1 then return [**]; end if;
    Q := [a[1]^a[2]:a in Factorization(N)];
    lift := func<i,n|CRT([j eq i select n else 1 : j in [1..#Q]],Q)>;
    return [* DirichletCharacterFromValuesOnUnitGenerators(DirichletGroup(Q[i],F),[chi(lift(i,n)):n in UnitGenerators(Q[i])]) : i in [1..#Q] *];
end intrinsic;

intrinsic Product (chis::List) -> GrpDrchElt
{ Returns the product of the given list of Dirichlet characters (the trivial character for an empty list). }
    if #chis eq 0 then return DirichletGroup(1)!1; end if;
    chi := chis[1]; for i:=2 to #chis do chi *:= chis[i]; end for;
    return chi;
end intrinsic;

intrinsic IsMinimal (chi::GrpDrchElt) -> BoolElt
{ Returns true if the specified Dirichlet character is minimal in the sense of Booker-Lee-Strombergsson (Twist-minimal trace formulas and Selberg eignvalue conjedcture). }
    c := Conductor(chi);
    for chip in Factorization(chi) do
        b,p,e := IsPrimePower(Modulus(chip));  assert b;
        s := Valuation(c,p);
        if p gt 2 then
            if s ne 0 and s ne e and Order(chip) ne 2^Valuation(p-1,2) then return false; end if;
        else
            if s ne e div 2 and s ne e then
                if e le 3 then
                    if s ne 0 then return false; end if;
                else
                    if IsEven(e) then return false; end if;
                    if s ne 0 and s ne 2 then return false; end if;
                end if;
            end if;
        end if;
    end for;
    return true;
end intrinsic;

intrinsic IsMinimalSlow (chi::GrpDrchElt) -> BoolElt
{ Slow version of IsMinimal. }
    b,p,e := IsPrimePower(Modulus(chi));
    if not b then return &and[$$(chip):chip in Factorization(chi)]; end if;
    N := Modulus(chi); c := Conductor(chi);
    if c*c gt N and c ne N then return false; end if;
    if p eq 2 and e gt 3 and IsEven(e) and c lt Sqrt(N) then return false; end if;
    n := Order(chi);
    return #[psi: psi in Elements(FullDirichletGroup(N))|Conductor(psi)*Conductor(psi*chi) le N and (Order(chi*psi^2) lt n or Conductor(chi*psi^2) lt c)] eq 0;
end intrinsic;

intrinsic UnitGeneratorsLogMap (N::RngIntElt, u::SeqEnum[RngIntElt]) -> UserProgram
{ Given a list of generators for (Z/NZ)* returns a function that maps integers coprime to N to a list of exponents writing the input as a power product over the given generators. }
    // We use an O(#(Z/NZ)*) algorithm to compute a discrete log lookup table; for small N this is faster than being clever (but for large N it won't be)
    // Impelemnts Algorithm 2.2 in https://arxiv.org/abs/0903.2785, but we don't bother saving power relations
    if N le 2 then return func<x|[]>; end if;
    ZNZ := Integers(N);  r := [Integers()|];
    n := #u;
    T := [ZNZ!1];
    g := ZNZ!u[1]; h := g; while h ne 1 do Append(~T,h); h *:= g; end while;
    r := [#T];
    for i:=2 to n do
        X := Set(T); S := T; j := 1;
        g := u[i];  h := g; while not h in X do S cat:= [h*t:t in T]; h *:= g; j +:= 1; end while;
        Append(~r,j);  T := S;
    end for;
    ZZ := Integers();
    // Stupid apporach to computing a mapg that given n in [1..N] returns the number of positive integers < n coprime to N
    // (doesn't really matter since we are already spending linear time, but wastes memory and could be eliminated).
    A := [ZZ|0:i in [1..N]];
    for i:=1 to #T do A[ZZ!T[i]] := i-1; end for;
    rr := [ZZ|1] cat [&*r[1..i-1]:i in [2..n]];
    return func<x|[(A[ZZ!x] div rr[i]) mod r[i] : i in [1..n]]>;
end intrinsic;

intrinsic NumberOfCharacterOrbits (N::RngIntElt:OrderBound:=0) -> RngIntElt
{ The number of Galois orbits of Dirichlet characters of modulus N (of order <= OrderBound, if specified). }
    require N gt 0: "Modulus N must be a positive integer";
    if N le 2 then return 1; end if;
    if N mod 4 eq 2 then N div:= 2; end if;
    b,p,e := IsPrimePower(N);  if b and OrderBound eq 0 then return p eq 2 select 2*(e-1) else e*NumberOfDivisors(p-1); end if;
    X := OrderStats(MultiplicativeGroup(Integers(N)));  S := Set(X);  if OrderBound gt 0 then S := {n: n in S| n le OrderBound}; end if;
    return &+[Multiplicity(X,n) div EulerPhi(n):n in S];
end intrinsic;

intrinsic CharacterOrbitLabels(N::RngIntElt:OrderBound:=0) -> SeqEnum[MonStgElt]
{ List of labels of Galois orbits of Dirichlet characters of modulus N (of order <= OrderBound, if specified). }
    return [Sprintf("%o.%o",N,Base26Encode(i-1)): i in [1..n]] where n:=NumberOfCharacterOrbits(N:OrderBound:=OrderBound);
end intrinsic;

intrinsic IsCharacterLabel (s::MonStgElt) -> BoolElt, RngIntElt, RngIntElt
{ Determines if s is a valid conrey label q.n with n an integer in [1..q] coprime to q. }
    b, s, t := Regexp("([1-9][0-9]*)\\.([1-9][0-9]*)", s);
    if not b then return false,_,_; end if;
    q := atoi(t[1]); n := atoi(t[2]);
    if n gt q or GCD(q,n) ne 1 then return false,_,_; end if;
    return true, q, n;
end intrinsic;

intrinsic IsConreyLabel (s::MonStgElt) -> BoolElt, RngIntElt, RngIntElt
{ Determines if s is a valid conrey label q.n with n an integer in [1..q] coprime to q. }
    return IsCharacterLabel(s);
end intrinsic;

intrinsic IsCharacterOrbitLabel (s::MonStgElt:validate:=true) -> BoolElt, RngIntElt, RngIntElt
{ Determines if s is a valid conrey label q.n with n an integer in [1..q] coprime to q. }
    b, s, t := Regexp("([1-9][0-9]*)\\.([a-z]+)", s);
    if not b then return false,_,_; end if;
    if t[2][1] eq "a" and t[2] ne "a" then return false,_,_; end if;
    q := atoi(t[1]);
    i := Base26Decode(t[2])+1;
    if not validate then return true, q, i; end if;
    if i gt NumberOfCharacterOrbits(q) then return false,_,_; end if;
    return true, q, i;
end intrinsic;

intrinsic CharacterOrbitLabel (N::RngIntElt,o::RngIntElt) -> MonStgElt
{ Label N.o of the character orbit of modulus N and orbit index o (converts o to base26 encoding). }
    return Sprintf("%o.%o",N,Base26Encode(o-1));
end intrinsic;

intrinsic CharacterOrbitLabel (s::MonStgElt) -> MonStgElt
{ Returns the character orbit label N.a for the specified Conrey character or character orbit. }
    if IsCharacterOrbitLabel(s) then return s; end if;
    b,q,n := IsCharacterLabel(s);
    require b: "Input string must be a valid Conrey label q.n with q,n positive coprime integers, or a valid character orbit label q.a, where a is a base-26 encoded Galois orbit index.";
    return CharacterOrbitLabel(q,ConreyCharacterOrbitIndex(q,n));
end intrinsic;

intrinsic ConreyCharacterOrbitLabel(q::RngIntElt, n::RngIntElt) -> MonStgElt
{ The label q.o of the Galois orbit of the specified Conrey character q.n. }
    return CharacterOrbitLabel(q,ConreyCharacterOrbitIndex(q,n));
end intrinsic;

intrinsic ConreyCharacterOrbitLabel(s::MonStgElt) -> MonStgElt
{ The label q.o of the Galois orbit of the specified Conrey character q.n. }
    return CharacterOrbitLabel(s);
end intrinsic;

intrinsic CharacterOrbitIndex (s::MonStgElt) -> RngIntElt
{ Returns the character orbit index for the specified Conrey character or character orbit. }
    b,q,i := IsCharacterOrbitLabel(s);
    if b then return i; end if;
    b,q,n := IsCharacterLabel(s);
    require b: "Input string must be a valid Conrey label q.n with q,n positive coprime integers, or a valid character orbit label q.a, where a is a base-26 encoded Galois orbit index.";
    return ConreyCharacterOrbitIndex(q,n);
end intrinsic;

intrinsic SplitCharacterLabel (s::MonStgElt) -> SeqEnum[RngIntElt]
{ Integers [q,n] for Conrey character label q.n. }
    b,q,n := IsCharacterLabel(s);
    if b then return [q,n]; end if;
    b,q,i := IsCharacterOrbitLabel(s);
    require b: "Input string must be a valid Conrey label q.n with q,n positive coprime integers, or a valid character orbit label q.a, where a is a base-26 encoded Galois orbit index.";
    return [q,ConreyCharacterOrbitRep(q,i)];
end intrinsic;

intrinsic SplitCharacterOrbitLabel (label::MonStgElt) -> SeqEnum[RngIntElt]
{ Modulus N and orbit index o of character orbit label N.o (where o is base26 encoded). }
    b,q,i := IsCharacterOrbitLabel(label:validate:=false);
    require b: "Input string must be a valid character orbit label q.a with q a positive integer and a base-26 encoded Galois orbit index.";
    return [q,i];
end intrinsic;

intrinsic CompareCharacterOrbitLabels (s::MonStgElt,t::MonStgElt) -> RngIntElt
{ Compares character orbit labels (returns an integer less than, equal to, or greater than 0 indicating the result). }
    return s eq t select 0 else (SplitCharacterOrbitLabel(s) lt SplitCharacterOrbitLabel(t) select -1 else 1);
end intrinsic;

intrinsic CharacterOrbitOrder (N::RngIntElt,n::RngIntElt) -> RngIntElt
{ The order of the characters in the nth orbit of modulus N. }
    require N gt 0 and n gt 0: "Modulus N and orbit index n must be positive integers";
    X :=  OrderStats(MultiplicativeGroup(Integers(N)));  S := Sort({@ o : o in X @});
    m := 0; for i:=1 to #S do m +:= Multiplicity(X,S[i]) div EulerPhi(S[i]); if m ge n then return S[i]; end if; end for;
    require m ge n: Sprintf("Specified n=%o is not a valid orbit index for the specified modulus N=%o (there are only %o orbits)\n", n, N, m);
end intrinsic;

intrinsic CharacterOrbitOrder (label::MonStgElt) -> RngIntElt
{ The order of the characters in the specified character orbit. }
    return CharacterOrbitOrder(a[1],a[2]) where a := SplitCharacterOrbitLabel(label); 
end intrinsic;

intrinsic CharacterOrbitDegree (label::MonStgElt) -> RngIntElt
{ The order of the characters in the specified character orbit. }
    return EulerPhi(CharacterOrbitOrder(label));
end intrinsic;

intrinsic NumberOfTrivialCharacterOrbits (N::RngIntElt) -> RngIntElt
{ The number of trivial Galois orbits of Dirichlet characters of modulus N (number of characters of degree 1). }
    require N gt 0: "Modulus N must be a positive integer";
    w := #PrimeDivisors(N);
    if Valuation(N,2) eq 1 then w -:= 1; end if;
    if Valuation(N,2) gt 2 then w +:= 1; end if;
    return 2^w;
end intrinsic;

intrinsic IsConjugate (chi1::GrpDrchElt,chi2::GrpDrchElt) -> BoolElt
{ Returns true if chi1 and chi2 are Galois conjugate Dirichlet characters. }
    e := Order(chi1);
    if Order(chi2) ne e then return false; end if;
    chi1 := MinimalBaseRingCharacter(chi1);  chi2 := MinimalBaseRingCharacter(chi2);
    v1 := ValuesOnUnitGenerators(chi1);  v2 := ValuesOnUnitGenerators(chi2);
    if [OrderOfRootOfUnity(a,e):a in v1] ne [OrderOfRootOfUnity(a,e): a in v2] then return false; end if;
    return #Set(GaloisConjugacyRepresentatives([chi1,Parent(chi1)!chi2])) eq 1 select true else false;
end intrinsic;

intrinsic CompareCharacters (chi1::GrpDrchElt,chi2::GrpDrchElt) -> RngIntElt
{ Compare Dirichlet characters based on order and lexicographic ordering of traces. }
    N := Modulus(chi1);  assert Modulus(chi2) eq N;
    n1 := Order(chi1); n2 := Order(chi2);
    if n1 ne n2 then return n1-n2; end if;
    // this will be very slow when the characters are actually conjugate, try to avoid this use case
    for a:=2 to N-1 do
        if GCD(a,N) ne 1 then continue; end if;
        t1 := Trace(chi1(a));  t2 := Trace(chi2(a));
        if t1 ne t2 then return t1-t2; end if;
    end for;
    return 0;
end intrinsic;

intrinsic CompareConreyCharacters (q::RngIntElt, n1::RngIntElt, n2::RngIntElt) -> RngIntElt
{ Compare two Conrey characters of modulus q based on order and lexicographic ordering of traces. }
    Zq := Integers(q);
    m1 := Order(Zq!n1); m2 := Order(Zq!n2);
    if m1 ne m2 then return m1-m2; end if;
    for a:=2 to q-1 do
        if a eq 100 and IsConreyConjugate(q,n1,n2) then return 0; end if;
        if GCD(a,q) ne 1 then continue; end if;
        t1 := ConreyCharacterTrace(q,n1,a);  t2 := ConreyCharacterTrace(q,n2,a);
        if t1 ne t2 then return t1-t2; end if;
    end for;
    return 0;
end intrinsic;

intrinsic CompareConreyCharacters (q::RngIntElt, n1::RngIntElt, n2::RngIntElt, amin::RngIntElt) -> RngIntElt
{ Compare two Conrey characters of modulus q based on lex ordering of traces starting from amin (assumes characters have same order and agree on traces for a < amin). }
    for a:=amin to q-1 do
        if a-amin eq 100 and IsConreyConjugate(q,n1,n2) then return 0; end if;
        if GCD(a,q) ne 1 then continue; end if;
        t1 := ConreyCharacterTrace(q,n1,a);  t2 := ConreyCharacterTrace(q,n2,a);
        if t1 ne t2 then return t1-t2; end if;
    end for;
    return 0;
end intrinsic;

intrinsic CharacterOrbitReps (N::RngIntElt:RepTable:=false,OrderBound:=0) -> List, Assoc
{ The list of Galois orbit representatives of the full Dirichlet group of modulus N with minimal codomains sorted by order and trace vectors.
  If the optional boolean argument RepTable is set then a table mapping Dirichlet characters to indexes in this list is returned as the second return value. }
    require N gt 0: "Modulus N must be a positive integer";
    if OrderBound eq 1 then chi1:=DirichletGroup(N)!1; if RepTable then T:=AssociativeArray(Parent(chi1)); T[chi1]:=1; return [chi1],T; else return [chi1]; end if; end if;
    if not RepTable and OrderBound eq 0 and IsCyclic(N) then return [* DirichletCharacter(s):s in ConreyCharacterOrbitReps(N) *]; end if;
    // The call to MinimalBaseRingCharacter can be very slow when N is large (this makes no sense it should be easy) */
    G := [* MinimalBaseRingCharacter(chi): chi in GaloisConjugacyRepresentatives(FullDirichletGroup(N)) *];
    X := [i:i in [1..#G]];
    X := Sort(X,func<i,j|CompareCharacters(G[i],G[j])>);
    G := OrderBound eq 0 select [* G[i] : i in X *] else [* G[i] : i in X | Order(G[i]) le OrderBound *];
    if not RepTable then return G; end if;
    H := Elements(FullDirichletGroup(N));
    A := AssociativeArray();
    for i:=1 to #G do v:=[OrderOfRootOfUnity(a,Order(G[i])):a in ValuesOnUnitGenerators(G[i])]; if IsDefined(A,v) then Append(~A[v],i); else A[v]:=[i]; end if; end for;
    if OrderBound gt 0 then H := [chi : chi in H | Order(chi) le OrderBound]; end if;
    T := AssociativeArray(Parent(H[1]));
    for h in H do
        v := [OrderOfRootOfUnity(a,Order(h)):a in ValuesOnUnitGenerators(h)];
        m := A[v];
        if #m eq 1 then
            T[h] := m[1];
        else
            for i in m do if IsConjugate(h,G[i]) then T[h]:=i; break; end if; end for;
        end if;
    end for;
    return G, T;
end intrinsic;

intrinsic MinimalConreyConjugate(q::RngIntElt, n::RngIntElt) -> RngIntElt
{ The minimal Conrey index among all conjugates of q.n. }
    if n eq 1 then return 1; end if;
    R := Integers(q); U, pi := MultiplicativeGroup(R); x := Inverse(pi)(n);
    return i where i := Min([Integers()|pi(n*x):n in [1..m]|GCD(m,n) eq 1]) where m := Order(R!n);
end intrinsic;

intrinsic MinimalConreyConjugate(s::MonStgElt) -> RngIntElt
{ The minimal Conrey index among all conjugates of q.n. }
    b,q,n := IsCharacterLabel(s);
    require b: "Input string must be a valid Conrey label q.n with q,n positive coprime integers";
    return Sprintf("%o.%o",q,MinimalConreyConjugate(q,n));
end intrinsic;

intrinsic MaximalConreyConjugate(q::RngIntElt, n::RngIntElt) -> RngIntElt
{ The maximal Conrey index among all conjugates of q.n. }
    if n eq 1 then return 1; end if;
    R := Integers(q); U, pi := MultiplicativeGroup(R); x := Inverse(pi)(n);
    return Max([Integers()|pi(n*x):n in [1..m]|GCD(m,n) eq 1]) where m := Order(R!n);
end intrinsic;

intrinsic MaximalConreyConjugate(s::MonStgElt) -> RngIntElt
{ The maximal Conrey index among all conjugates of q.n. }
    b,q,n := IsCharacterLabel(s);
    require b: "Input string must be a valid Conrey label q.n with q,n positive coprime integers";
    return Sprintf("%o.%o",q,MaximalConreyConjugate(q,n));
end intrinsic;

intrinsic IsConreyConjugate(q::RngIntElt, n1::RngIntElt, n2::RngIntElt) -> BoolElt
{ Whether the specified Conrey characters are conjugate or not. }
    if n1 eq n2 then return true; end if;
    a := Integers(q)!n1; b := Integers(q)!n2;
    if Order(a) ne Order(b) then return false; end if;
    return Log(a,b) ge 0;
end intrinsic;

intrinsic IsConreyConjugate(s::MonStgElt,t::MonStgElt) -> BoolElt
{ Whether the specified Conrey characters are conjugate or not. }
    a := SplitCharacterLabel(s);  b := SplitCharacterLabel(t);
    if a[1] ne b[1] then return false; end if;
    return IsConreyConjugate(a[1],a[2],b[1],b[2]);
end intrinsic;

intrinsic IsConjugate(s::MonStgElt,t::MonStgElt) -> BoolElt
{ Whether the specified Conrey characters are conjugate or not. }
    return IsConreyConjugate(s,t);
end intrinsic;

intrinsic ConreyCharacterOrbitRepIndexes(q::RngIntElt:ParityEquals:=0,ConductorDivides:=0,ConductorBound:=0,DegreeBound:=0,OrderBound:=0,PrimitiveOnly:=false) -> SeqEnum[MonStgElt]
{ The list of minimal index Conrey labels of Galois orbit representatives of the full Dirichlet group sorted by order and trace vectors. }
    require q gt 0: "Modulus must be positive.";
    if PrimitiveOnly then
        require ConductorBound eq 0 or ConductorBound gt 0: "Invalid ConductorBound when PrimitiveOnly is set";
        require ConductorDivides eq 0 or ConductorDivides mod q ne 0: "Invalid ConductorDivides when PrimitiveOnly is set";
    end if;
    if q le 2 then return ParityEquals eq -1 select [] else [1]; end if;
    U,pi := MultiplicativeGroup(Integers(q));
    A := [Integers()|Min([pi(n*x):n in [1..m]|GCD(m,n) eq 1]) where m:=Order(x):x in CyclicGenerators(U)];
    if #A lt 100 then
        X := Sort(A,func<a,b|CompareConreyCharacters(q,Integers()!a,Integers()!b)>);
    else
        Y := IndexFibers(A,func<n|[Order(Zq!n)] cat ConreyCharacterTraces(q,n,[a:a in [1..99]|GCD(q,a) eq 1])>) where Zq := Integers(q);
        K := Sort([k:k in Keys(Y)]);
        X := &cat[Sort(Y[k],func<a,b|CompareConreyCharacters(q,Integers()!a,Integers()!b,100)>):k in K];
    end if;
    if ParityEquals ne 0 then X := [n:n in X|Parity(q,n) eq ParityEquals]; end if;
    if OrderBound ne 0 then X := [n:n in X|Order(q,n) le OrderBound]; end if;
    if DegreeBound ne 0 then X := [n:n in X|Degree(q,n) le DegreeBound]; end if;
    if PrimitiveOnly then X := [n:n in X|Conductor(q,n) eq q]; return X; end if;
    if ConductorBound ne 0 then X := [n:n in X|Conductor(q,n) le ConductorBound]; end if;
    if ConductorDivides ne 0 then X := [n:n in X|ConductorDivides mod Conductor(q,n) eq 0]; end if;
    return X;
end intrinsic;

intrinsic ConreyCharacterOrbitReps(q::RngIntElt:ParityEquals:=0,ConductorDivides:=0,ConductorBound:=0,DegreeBound:=0,OrderBound:=0,PrimitiveOnly:=false) -> SeqEnum[MonStgElt]
{ The list of minimal index Conrey labels of Galois orbit representatives of the full Dirichlet group sorted by order and trace vectors. }
    return [s cat IntegerToString(n): n in X] where X:=ConreyCharacterOrbitRepIndexes(q:ParityEquals:=ParityEquals,
                                                                                        ConductorDivides:=ConductorDivides,
                                                                                        ConductorBound:=ConductorBound,
                                                                                        DegreeBound:=DegreeBound,
                                                                                        OrderBound:=OrderBound,
                                                                                        PrimitiveOnly:=PrimitiveOnly) where s:=IntegerToString(q) cat ".";
end intrinsic;

intrinsic ConreyCharacterOrbitRep (s::MonStgElt) -> MonStgElt
{ The minimal index Conrey label that occurs in the specifed Galois orbit. }
    b,q,n := IsCharacterLabel(s);
    if b then return Sprintf("%o.%o",q,MinimalConreyConjugate(q,n)); end if;
    b,q,o := IsCharacterOrbitLabel(s);
    require b: "Input string must be a valid Conrey label q.n with q,n positive coprime integers, or character orbit label q.a";
    return Sprintf("%o.%o",q,ConreyCharacterOrbitRep(q,o));
end intrinsic;

intrinsic ConreyCharacterOrbitRep (q::RngIntElt,o::RngIntElt) -> RngIntElt
{ The minimal index Conrey label that occurs in the specifed Galois orbit. }
    if o eq 1 then return 1; end if;
    U,pi := MultiplicativeGroup(Integers(q));
    S := Sort(CyclicGenerators(U),func<a,b|Order(a)-Order(b)>);
    require o le #S: Sprintf("Specified character orbit does not exist, there are only %o character orbits of modulus %o.", #S, q);
    m := Order(S[o]);
    if #Generators(U) eq 1 then return Min([Integers()|pi(n*x):n in [1..m]|GCD(m,n) eq 1]) where x:=S[o]; end if;
    i := o; while i gt 1 and Order(S[i-1]) eq m do i -:= 1; end while;
    j := o; while j lt #S and Order(S[j+1]) eq m do j +:= 1; end while;
    T := Sort([Integers()|pi(x):x in S[i..j]],func<n1,n2|CompareConreyCharacters(q,n1,n2)>);
    return MinimalConreyConjugate(q,T[o-i+1]);
end intrinsic;

intrinsic ConreyCharacterOrbitIndex (q::RngIntElt,n::RngIntElt) -> RngIntElt
{ The index of representative of the Galois orbit of the Conrey character q.n in the list returned by CharacterOrbitReps(q). }
    require q gt 0 and n gt 0 and GCD(q,n) eq 1: "Conrey characters must be specified by a pair of coprime positive integers q,n.";
    if n eq 1 then return 1; end if;
    R := Integers(q); U,pi := MultiplicativeGroup(R); m := Order(Integers(q)!n);
    S := Sort(CyclicGenerators(U),func<a,b|Order(a)-Order(b)>);
    i := Index([Order(a):a in S], m);
    j := i; while j lt #S and Order(S[j+1]) eq m do j +:= 1; end while;
    if i eq j then return i; end if;
    T := Sort([Integers()|pi(x):x in S[i..j]],func<n1,n2|CompareConreyCharacters(q,n1,n2)>);
    for nn in T do if Log(R!nn,R!n) ge 0 then return i; end if; i +:= 1; end for;
    assert false;
end intrinsic;

intrinsic ConreyCharacterOrbitIndex (s::MonStgElt) -> RngIntElt
{ The index of representative of the Galois orbit of the Conrey character with label s in the list returned by CharacterOrbitReps(q). }
    return ConreyCharacterOrbitIndex(a[1],a[2]) where a:=SplitCharacterLabel(s);
end intrinsic;

intrinsic CharacterOrbitLabel (chi::GrpDrchElt) -> RngIntElt
{ Label N.o of the orbit of the specified Dirichlet character. }
    return Sprintf("%o.%o",Modulus(chi),Base26Encode(CharacterOrbitIndex(chi)-1));
end intrinsic;

intrinsic CharacterOrbitRep (label::MonStgElt) -> GrpDrchElt
{ Representative element for the Dirichlet character orbit indentified by the label. }
    return DirichletCharacter(ConreyCharacterOrbitRep(label));
end intrinsic;

intrinsic CharacterOrbitIndex (chi::GrpDrchElt) -> RngIntElt
{ The index of the orbit of the specified Dirichlet character in the list of orbit representatives returned by CharacterOrbitReps (this can also be determined using the RepTable parameter). }
    m := Order(chi);
    if m eq 1 then return 1; end if;
    if IsCyclic(MultiplicativeGroup(Integers(Modulus(chi)))) then return Index(Divisors(EulerPhi(Modulus(chi))),m); end if;
    v := [Trace(z):z in ValueList(MinimalBaseRingCharacter(chi))];
    G := CharacterOrbitReps(Modulus(chi));
    M := [i : i in [1..#G] | Order(G[i]) eq m and [Trace(z):z in ValueList(G[i])] eq v];
    assert #M eq 1;
    return M[1];
end intrinsic;

intrinsic KroneckerDiscriminant (chi::GrpDrchElt) -> RngIntElt
{ Returns the discriminant of the Kronecker symbold corresponding to the specified character, or zero if none exists (1 for trivial character). }
    if Order(chi) gt 2 then return 0; end if;
    if Order(chi) eq 1 then return 1; end if;
    D := Parity(chi)*Conductor(chi);
    return D mod 4 in [0,1] select D else 0;
end intrinsic;

intrinsic KroneckerCharacterOrbits (M::RngIntElt) -> RngIntElt
{ A list of paris <D,i> where D is a fundamental discriminant dividing the modulus M and i is the orbit index of the corresponding Kronecker character. }
    require M gt 0: "The modulus M should be a positive integer.";
    D := [-d:d in Divisors(M)|IsFundamentalDiscriminant(-d)] cat [d:d in Divisors(M)|IsFundamentalDiscriminant(d)];
    if #D eq 0 then return []; end if;
    if #D eq 1 then return [<D[1],2>]; end if;
    G := DirichletGroup(M);
    X := [G|KroneckerCharacter(d):d in D];
    B := 32;
    while true do T := [[X[i](n):n in [1..B]]:i in [1..#X]]; if #Set(T) eq #T then break; end if; B *:=2; end while;
    X := Sort([<T[i],D[i]>:i in [1..#D]]);
    return [<X[i][2],1+i>:i in [1..#X]];
end intrinsic;

intrinsic KroneckerCharacterOrbit (D::RngIntElt,M::RngIntElt) -> RngIntElt
{ The index of the orbit of the Kronecker character for the fundamental discriminant D in modulus M. }
    require IsFundamentalDiscriminant(D): "D should be a fundamental quadratic discriminant.";
    require M gt 0 and IsDivisibleBy(M,D): "The modulus M should be a positive integer divisible by the fundamental discriminant D.";
    return [r[2] : r in KroneckerCharacterOrbits(M) | r[1] eq D][1];
end intrinsic;

intrinsic ConreyGenerator (p::RngIntElt) -> RngIntElt
{ For an odd prime p, the least positive integer a that generates (Z/p^eZ)^times for all e. }
    require IsOdd(p) and IsPrime(p): "p must be an odd prime";
    return PrimitiveRoot(p^2);
end intrinsic;

intrinsic ConreyLogModEvenPrimePower (e::RngIntElt,n::RngIntElt) -> RngIntElt, RngIntElt
{ Given an exponent e > 2 and an odd integer n returns unique integers a,s such that n = s*5^a mod 2^e with s in [-1,1] and a in [0..e-1]. }
    require e gt 2 and IsOdd(n): "e must be at least 3 and n must be an odd integers";
    R := Integers(2^e);
    s := n mod 4 eq 1 select 1 else -1;
    x := R!s*n;
    a := plog(2,e-2,R!5,x); assert a ge 0;
    return a,s;
end intrinsic;

intrinsic ConreyLogModOddPrimePower (p::RngIntElt,e::RngIntElt,n::RngIntElt) -> RngIntElt, RngIntElt
{ Given n coprime to the odd prime p returns the integer x in [0..phi(p^e)-1] for which n = r^x mod p^e, where r is the Conrey generator for p. }
    require IsOdd(p) and GCD(p,n) eq 1: "p must be an odd prime and n must not be divisible by p";
    r := ConreyGenerator(p);
    if e eq 1 then return Log(GF(p)!r,GF(p)!n); end if;
    R := Integers(p^e);  pp := p^(e-1);
    x1 := plog(p,e-1,(R!r)^(p-1),(R!n)^(p-1)); assert x1 ge 0;
    x2 := Log(GF(p)!(R!r)^pp,GF(p)!(R!n)^pp); assert x2 ge 0;
    return CRT([x1,x2],[pp,p-1]);
end intrinsic;

intrinsic ConreyCharacterValue (q::RngIntElt,n::RngIntElt,m::RngIntElt) -> FldCycElt
{ The value chi_q(n,m) of the Dirichlet character with Conrey label q.n at the integer m. }
    require q gt 0 and n gt 0 and GCD(q,n) eq 1: "Conrey characters must be specified by a pair of coprime positive integers q,n (very slow, switch to sparse representation once magma bug is fixed).";
    if q eq 1 then return CyclotomicField(1)!1; end if;
    F := CyclotomicField(Order(Integers(q)!n));
    if GCD(q,m) ne 1 then return F!0; end if;
    if q eq 1 or n mod q eq 1 or m mod q eq 1 then return F!1; end if;
    a := ConreyCharacterAngle(q,n,m);
    return RootOfUnity(Denominator(a),F)^Numerator(a);
end intrinsic;

intrinsic ConreyCharacterValue (s::MonStgElt,m::RngIntElt) -> FldCycElt
{ The value chi_q(n,m) of the Dirichlet character with Conry label q.n at the integer m. }
    return ConreyCharacterValue(a[1],a[2],m) where a:=SplitCharacterLabel(s);
end intrinsic;

intrinsic ConreyCharacterValues (q::RngIntElt,n::RngIntElt,S::SeqEnum[RngIntElt]:Sparse:=false) -> SeqEnum[FldCycElt]
{ The list of values of the Dirichlet character with Conrey label q.n on the integers in S. }
    require q gt 0 and n gt 0 and GCD(q,n) eq 1: "Conrey characters must be specified by a pair of coprime positive integers q,n.";
    require not Sparse: "There is a Magma bug that currently causes unexpected behavior when Sparse is specified :(";
    if q eq 1 then return [1:i in S]; end if;
    F := CyclotomicField(Order(Integers(q)!n):Sparse:=Sparse);
    if n mod q eq 1 then return [F|GCD(q,m) eq 1 select 1 else 0 : m in S]; end if;
    A := ConreyCharacterAngles(q,n,S);
    return [F|a eq 0 select 0 else RootOfUnity(Denominator(a),F)^Numerator(a):a in A];
end intrinsic;

intrinsic ConreyCharacterValues (q::RngIntElt,n::RngIntElt:Sparse:=false) -> SeqEnum[FldCycElt]
{ The list of values of the Dirichlet character with Conrey label q.n on standard generators for (Z/qZ)* (as returned by UnitGenerators(q)). }
    return ConreyCharacterValues(q,n,UnitGenerators(q):Sparse:=Sparse);
end intrinsic;

intrinsic CharacterValues( q::RngIntElt,n::RngIntElt:Sparse:=false) -> SeqEnum[FldCycElt]
{ The list of values of the Dirichlet character with Conrey label q.n on standard generators for (Z/qZ)* (as returned by UnitGenerators(q)). }
    return ConreyCharacterValues(q,n:Sparse:=Sparse);
end intrinsic;

intrinsic CharacterValues (chi::GrpDrchElt) -> SeqEnum[FldCycElt]
{ The list of values of the specifed Dirichlet character of modulus N on standard generators for (Z/NZ)* (as returned by UnitGenerators(N)). }
    return [chi(u):u in UnitGenerators(Modulus(chi))];
end intrinsic;

intrinsic ConreyCharacterTrace (q::RngIntElt,n::RngIntElt,m::RngIntElt) -> RngIntElt
{ The trace of chi_q(n,m) as an element of the field of values of chi_q(n,.). }
    a := ConreyCharacterAngle(q,n,m);
    if a eq 0 then return 0; end if;
    return MoebiusMu(d) * ExactQuotient(Degree(q,n), EulerPhi(d)) where d:=Denominator(a);
end intrinsic;

intrinsic ConreyCharacterTrace (s::MonStgElt,m::RngIntElt) -> RngIntElt
{ The trace of chi_q(n,m) as an element of the field of values of chi_q(n,.). }
    return ConreyCharacterTrace(a[1],a[2],m) where a:=SplitCharacterLabel(s);
end intrinsic;

intrinsic ConreyCharacterTraces (q::RngIntElt,n::RngIntElt,S::SeqEnum[RngIntElt]) -> SeqEnum[RngIntElt]
{ The traces of chi_q(n,m) as elements of the field of values of chi_q(n,.) for m in S. }
    A := ConreyCharacterAngles(q,n,S); D := Degree(q,n);
    return [Integers()| a eq 0 select 0 else MoebiusMu(d) * ExactQuotient(D, EulerPhi(d)) where d:=Denominator(a): a in A];
end intrinsic;

intrinsic ConreyCharacterTraces (s::MonStgElt,S::SeqEnum[RngIntElt]) -> SeqEnum[RngIntElt]
{ The traces of chi_q(n,m) as elements of the field of values of chi_q(n,.) for m in S. }
    return ConreyCharacterTraces(a[1],a[2],S) where a:=SplitCharacterLabel(s);
end intrinsic;

intrinsic NormalizedAngle (r::FldRatElt) -> FldRatElt
{ Given a rational number r return unique positive rational number s <= 1 such that r-s is an integer. }
    b:=Denominator(r); a:=Numerator(r) mod b;
    return a eq 0 select Rationals()!1 else a/b;
end intrinsic;

intrinsic ConjugateAngles (v::SeqEnum[FldRatElt]) -> SeqEnum[FldRatElt]
{ Given a list of angles v returns the (normalized) orbit of v under the action of (Z/phi(N)Z)* where N is the LCM of the denominators of v. }
    if #v eq 0 then return v; end if;
    G,pi:=MultiplicativeGroup(Integers(LCM([Denominator(r):r in v])));
    return [[NormalizedAngle((Integers()!pi(g))*r):r in v]:g in G];
end intrinsic;

intrinsic CharacterAngles (chi::GrpDrchElt, S::SeqEnum[RngIntElt]) -> SeqEnum[FldRatElt]
{ The list of angles (r in Q corresponding to e(r) in C) of the specifed Dirichlet character of modulus N on standard generators for (Z/NZ)* (as returned by UnitGenerators(N)). }
    N := Modulus(chi); m := Order(chi); z := RootOfUnity(m,Codomain(chi));
    return [Rationals()|Min([i:i in [1..m]|z^i eq v])/m where v:=chi(u): u in S];
end intrinsic;

intrinsic CharacterAngles (chi::GrpDrchElt) -> SeqEnum[FldRatElt]
{ The list of angles (r in Q corresponding to e(r) in C) of the specifed Dirichlet character of modulus N on standard generators for (Z/NZ)* (as returned by UnitGenerators(N)). }
    return CharacterAngles(chi,UnitGenerators(Modulus(chi)));
end intrinsic;

intrinsic ConreyCharacterAngle (q::RngIntElt,n::RngIntElt,m::RngIntElt) -> FldRatElt
{ The rational number r such that chi_q(n,m) = e(r) or 0 if m is not coprime to q. }
    require q gt 0 and n gt 0 and GCD(q,n) eq 1: "Conrey characters must be specified by a pair of coprime positive integers q,n.";
    if GCD(q,m) ne 1 then return Rationals()!0; end if;
    if q eq 1 or n mod q eq 1 or m mod q eq 1 then return Rationals()!1; end if;
    b,p,e:= IsPrimePower(q);
    if not b then return NormalizedAngle(&+[Rationals()|$$(a[1]^a[2],n,m):a in Factorization(q)]); end if;
    if p gt 2 then
        a := ConreyLogModOddPrimePower(p,e,n);  b := ConreyLogModOddPrimePower(p,e,m); d := (p-1)*p^(e-1);
        return NormalizedAngle((a*b) / d);
    else
        if e eq 2 then assert n mod q eq 3 and m mod q eq 3; return 1/2; end if; assert e gt 2;
        a,ea := ConreyLogModEvenPrimePower(e,n);  b,eb := ConreyLogModEvenPrimePower(e,m); d:= 2^(e-2);
        return NormalizedAngle(((1-ea)*(1-eb)) / 8 + (a*b) / d);
    end if;
end intrinsic;

intrinsic ConreyCharacterComplexValue (q::RngIntElt,n::RngIntElt,m::RngIntElt,CC::FldCom) -> FldComElt
{ Value of chi_q(m,n) in specified complex field. }
    return GCD(q,m) eq 1 select Exp(2*Pi(CC)*CC.1*ConreyCharacterAngle(q,n,m)) else 0;
end intrinsic;

intrinsic ConreyCharacterRealValue (q::RngIntElt,n::RngIntElt,m::RngIntElt,RR::FldRe) -> FldReElt
{ Real part of chi_q(m,n) in specified real field. }
    return GCD(q,m) eq 1 select Cos(2*Pi(RR)*ConreyCharacterAngle(q,n,m)) else 0;
end intrinsic;

intrinsic ConreyCharacterAngles (q::RngIntElt,n::RngIntElt,S::SeqEnum[RngIntElt]) -> SeqEnum[FldRatElt]
{ The list of angles (r in Q corresponding to e(r) in C) of the Dirichlet character with Conrey label q.n on the integers m in S (or 0 for m in S not coprime to Q). }
    require q gt 0 and n gt 0 and GCD(q,n) eq 1: "Conrey characters must be specified by a pair of coprime positive integers q,n.";
    if q eq 1 then return [Rationals()|1:i in S]; end if;
    if n mod q eq 1 then return [Rationals()|GCD(i,q) eq 1 select 1 else 0 : i in S]; end if;
    b,p,e:= IsPrimePower(q);
    if not b then 
        X := [$$(a[1]^a[2],n,S):a in Factorization(q)];
        return [Rationals()|GCD(S[j],q) eq 1 select NormalizedAngle(&+[X[i][j]:i in [1..#X]]) else 0 : j in [1..#S]];
    end if;
    R := Integers(q);
    if p gt 2 then
        a := ConreyLogModOddPrimePower(p,e,n);  d := (p-1)*p^(e-1);
        return [Rationals()|GCD(m,p) eq 1 select NormalizedAngle((a*b)/d) where b := ConreyLogModOddPrimePower(p,e,m) else 0 : m in S];
    else
        if e eq 2 then assert n mod q eq 3; return [Rationals()|IsOdd(m) select (IsEven(ExactQuotient(m-1,2)) select 1 else 1/2) else 0 : m in S]; end if; assert e gt 2;
        a,ea := ConreyLogModEvenPrimePower(e,n);  d:= 2^(e-2);
        return [Rationals()|GCD(m,p) eq 1 select NormalizedAngle(((1-ea)*(1-eb)) / 8 + (a*b) / d) where b,eb := ConreyLogModEvenPrimePower(e,m) else 0 : m in S];
    end if;
end intrinsic;

intrinsic ConreyCharacterAngles (q::RngIntElt,n::RngIntElt) -> SeqEnum[FldRatElt]
{ The list of angles (r in Q corresponding to e(r) in C) of the Dirichlet character with Conrey label q.n on standard generators for (Z/qZ)* (as returned by UnitGenerators(q)). }
    return ConreyCharacterAngles(q,n,UnitGenerators(q));
end intrinsic;

intrinsic ConreyCharacterAngles (s:MonStgEt) -> SeqEnum[FldRatElt]
{ The list of angles (r in Q corresponding to e(r) in C) of the Dirichlet character with Conrey label q.n on standard generators for (Z/qZ)* (as returned by UnitGenerators(q)). }
    b,q,n := IsCharacterLabel(s);
    require b: "Conrey labels must have the form q.n with n <= q positive coprime integers";
    return ConreyCharacterAngles(q,n);
end intrinsic;

intrinsic CharacterAngles (q::RngIntElt,n::RngIntElt) -> SeqEnum[FldRatElt]
{ The list of angles (r in Q corresponding to e(r) in C) of the Dirichlet character with Conrey label q.n on standard generators for (Z/qZ)* (as returned by UnitGenerators(q)). }
    return ConreyCharacterAngles(q,n,UnitGenerators(q));
end intrinsic;

intrinsic CharacterAngles (s:MonStgEt) -> SeqEnum[FldRatElt]
{ The list of angles (r in Q corresponding to e(r) in C) of the Dirichlet character with Conrey label q.n on standard generators for (Z/qZ)* (as returned by UnitGenerators(q)). }
    b,q,n := IsCharacterLabel(s);
    require b: "Conrey labels must have the form q.n with n <= q positive coprime integers";
    return ConreyCharacterAngles(q,n);
end intrinsic;

intrinsic ConreyCharacterComplexValues (q::RngIntElt,n::RngIntElt,S::SeqEnum[RngIntElt],CC::FldCom) -> SeqEnum[FldComElt]
{ List of values of chi_q(n,m) for m in S in specified complex field. }
    return [Exp(2*Pi(CC)*CC.1*t): t in ConreyCharacterAngles(q,n,S)];
end intrinsic;

intrinsic ComplexConreyCharacter (q::RngIntElt,n::RngIntElt,CC::FldCom) -> Map
{ The Dirichlet character with Conrey label q.n with values in the specified complex field. }
    require q gt 0 and n gt 0 and GCD(q,n) eq 1: "Conrey characters must be specified by a pair of coprime positive integers q,n.";
    chi := CyclotomicConreyCharacter(q,n);
    F := Codomain(chi);
    phi := Degree(F) gt 1 select hom<F->CC|Conjugates(F.1:Precision:=Precision(CC))[1]> else hom<F->CC|>;
    xi := map<Integers()->CC|n:->phi(chi(n))>;
    U := UnitGenerators(chi);
    V := ConreyCharacterComplexValues(q,n,U,CC);
    assert &and[Abs(xi(U[i])-V[i]) lt 10.0^-(Precision(CC) div 2):i in [1..#U]];
    return xi;
end intrinsic;

intrinsic ComplexConreyCharacter (s::MonStgElt,CC::FldCom) -> Map
{ The Dirichlet character with Conrey label q.n. with values in the specific complex field. }
    b, q, n := IsCharacterLabel(s);
    require b: "Conrey labels must have the form q.n with n <= q positive coprime integers";
    return ComplexConreyCharacter(q,n,CC);
end intrinsic;

intrinsic ConreyIndex (chi::GrpDrchElt) -> RngIntElt
{ The integer n such that q.n is the Conrey label of the specified Dirichlet character of modulus q. }
    q := Modulus(chi);  m := Order(chi);
    G,pi := MultiplicativeGroup(Integers(q));  psi:=Inverse(pi);
    v := CharacterAngles(chi);
    M := [n : n in [1..q] | GCD(q,n) eq 1 and Order(psi(n)) eq m and ConreyCharacterAngles(q,n) eq v];
    assert #M eq 1;
    return M[1];
end intrinsic;

intrinsic ConreyLabel (chi::GrpDrchElt) -> MonStgElt
{ Conrey label q.n of the specified Dirichlet character (as a string). }
    return Sprintf("%o.%o",Modulus(chi),ConreyIndex(chi));
end intrinsic;

intrinsic ConreyCharacterFromLabel (s::MonStgElt) -> RngIntElt, RngIntElt
{ The coprime integers n <= q corresponding to the Conrey label q.n, or the minimal representative of the character orbit with label q.a. }
    b,q,n := IsCharacterLabel(s);
    if b then return q,n; end if;
    b,q,n := IsCharacterLabel(ConreyCharacterOrbitRep(s));
    require b: "Conrey labels must have the form q.n with n <= q positive coprime integers";
    return q,n;
end intrinsic;

intrinsic CharacterOrder (q::RngIntElt, n::RngIntElt) -> RngIntElt
{ The order of the Conrey character q.n. }
    return q le 2 select 1 else Order(Integers(q)!n);
end intrinsic;

intrinsic CharacterOrder (s::MonStgElt) -> RngIntElt
{ The order of the Conrey character q.n or character orbit q.a. }
    return IsCharacterLabel(s) select (a[1] le 2 select 1 else Order(Integers(a[1])!a[2]) where a := SplitCharacterLabel(s)) else CharacterOrbitOrder(s);
end intrinsic;

intrinsic Degree (q::RngIntElt, n::RngIntElt) -> RngIntElt
{ The degree of the number field generated by the values of the specified Conrey character. }
    return q le 2 select 1 else EulerPhi(Order(Integers(q)!n));
end intrinsic;

intrinsic Degree (s::MonStgElt) -> RngIntElt
{ The degree of the number field generated by the values of the specified Conrey character. }
    return EulerPhi(CharacterOrder(s));
end intrinsic;

intrinsic IsReal (q::RngIntElt, n::RngIntElt) -> BoolElt
{ Whether the specifed Conrey character takes only real values (trivial or quadratic) or not. }
    return q le 2 select true else Order(Integers(q)!n) le 2;
end intrinsic;

intrinsic IsReal (s::MonStgElt) -> BoolElt
{ Whether the specifed Conrey character takes only real values (trivial or quadratic) or not. }
    return CharacterOrder(s) le 2;
end intrinsic;

intrinsic IsMinimal (q::RngIntElt, n::RngIntElt) -> BoolElt
{ Returns true if the specified Conrey character q.n is minimal in the sense of Booker-Lee-Strombergsson (Twist-minimal trace formulas and Selberg eignvalue conjedcture). }
    c := Conductor(q,n);
    for pp in Factorization(q) do
        p := pp[1]; e:= pp[2]; qp := p^e;
        s := Valuation(c,p);
        if p gt 2 then
            if s ne 0 and s ne e and CharacterOrder(qp, n mod qp) ne 2^Valuation(p-1,2) then return false; end if;
        else
            if s ne e div 2 and s ne e then
                if e le 3 then
                    if s ne 0 then return false; end if;
                else
                    if IsEven(e) then return false; end if;
                    if s ne 0 and s ne 2 then return false; end if;
                end if;
            end if;
        end if;
    end for;
    return true;
end intrinsic;

intrinsic IsMinimal (s::MonStgElt) -> BoolElt
{ Returns true if the specified Conrey character q.n is minimal in the sense of Booker-Lee-Strombergsson (Twist-minimal trace formulas and Selberg eignvalue conjedcture). }
    q,n := ConreyCharacterFromLabel(s);
    return IsMinimal(q,n);
end intrinsic;

intrinsic Factorization (q::RngIntElt, n::RngIntElt) -> SeqEnum
{ Returns the factorization of the Conrey character q.n into Conrey characters q_i.n_i of prime power moduli q_i as a list of pairs of integers [q_i,n_i]. }
    require q gt 0 and n gt 0 and GCD(q,n) eq 1: "Conrey characters must be specified by a pair of coprime positive integers q,n.";
    return [[qi,n mod qi] where qi:=a[1]^a[2]:a in Factorization(q)];
end intrinsic;

intrinsic Factorization (s::MonStgElt) -> SeqEnum
{ Returns the factorization of the Conrey character q.n into Conrey characters q_i.n_i of prime power moduli q_i as a list of Conrey labels q_i.n_i. }
    b,q,n := IsCharacterLabel(s);
    require b: "Conrey labels must have the form q.n with n <= q positive coprime integers";
    return [Sprintf("%o.%o",x[1],x[2]):x in Factorization(q,n)];
end intrinsic;

intrinsic Parity (q::RngIntElt, n::RngIntElt) -> RngIntElt
{ The parity of the Conrey character q.n, given by its value +/-1 on -1. }
    require q gt 0 and n gt 0 and GCD(q,n) eq 1: "Conrey characters must be specified by a pair of coprime positive integers q,n.";
    return &*[Integers()|KroneckerSymbol(n,p):p in PrimeDivisors(q)|IsOdd(p)]*(q mod 4 ne 0 or n mod 4 eq 1 select 1 else -1);
end intrinsic;

intrinsic IsEven (q::RngIntElt, n::RngIntElt) -> RngIntElt
{ True if the Conrey character q.n has even parity (takes value 1 on -1). }
    return Parity(q,n) eq 1;
end intrinsic;

intrinsic IsOdd (q::RngIntElt, n::RngIntElt) -> RngIntElt
{ True if the Conrey character q.n has odd parity (takes value -1 on -1). }
    return Parity(q,n) eq -1;
end intrinsic;

intrinsic Parity (s::MonStgElt) -> RngIntElt
{ The parity of the Conrey character q.n, given by its value +/-1 on -1. }
    q,n := ConreyCharacterFromLabel(s);
    return Parity(q,n);
end intrinsic;

intrinsic Conductor (q::RngIntElt, n::RngIntElt) -> RngIntElt
{ The conductor of the Conrey character q.n. }
    require q gt 0 and n gt 0 and GCD(q,n) eq 1: "Conrey characters must be specified by a pair of coprime positive integers q,n.";
    return &*[Integers()|n mod pp eq 1 select 1 else p^(Valuation(Order(Integers(pp)!n),p)+(IsOdd(p) or n mod pp eq pp-1 select 1 else 2)) where pp:=p^qq[2] where p:=qq[1]:qq in Factorization(q)];
end intrinsic;

intrinsic Conductor (s::MonStgElt) -> RngIntElt
{ The conductor of the Conrey character q.n. }
    q,n := ConreyCharacterFromLabel(s);
    return Conductor(q,n);
end intrinsic;

intrinsic Modulus (s::MonStgElt) -> RngIntElt
{ The modulus q of the Conrey character q.n. }
    b,q,n := IsCharacterLabel(s);
    if not b then b,q,i := IsCharacterOrbitLabel(s:validate:=false); end if;
    require b: "Conrey labels must have the form q.n with n <= q positive coprime integers";
    return q;
end intrinsic;

intrinsic IsPrimitiveCharacter (q::RngIntElt, n::RngIntElt) -> BoolElt
{ Whether the specifed Conrey character q.n is primitive (conductor = modulus = q) or not. }
    return q eq Conductor(q,n);
end intrinsic;

intrinsic IsPrimitiveCharacter (s::MonStgElt) -> BoolElt
{ Whether the specifed Conrey character q.n is primitive (conductor = modulus = q) or not. }
    q,n := ConreyCharacterFromLabel(s);
    return IsPrimitive(q,n);
end intrinsic;

intrinsic CharacterOrder (xi::Map, N::RngIntElt) -> RngIntElt
{ Given a map xi:ZZ -> K that is a Dirichlet character of modulus N, returns its order (results are undefined if xi is not of modulus N). }
    e := Exponent(MultiplicativeGroup(Integers(N)));
    U := UnitGenerators(DirichletGroup(N));
    return LCM([Min([d: d in Divisors(e)|a^d eq 1]) where a:=xi(u) : u in U]);
end intrinsic;

intrinsic Conductor (xi::Map, N::RngIntElt) -> RngIntElt
{ Given a map ZZ -> K that is a Dirichlet character of modulus N, returns its conductor (results are undefined if xi is not of modulus N). }
    U := UnitGenerators(DirichletGroup(N));
    V := [xi(u):u in U];
    if Set(V) eq {1} then return 1; end if;
    if IsPrime(N) then return N; end if;
    return Min([M : M in Divisors(N) | M gt 2 and &and[&and[xi(u) eq xi(u+r*M):r in [1..ExactQuotient(N,M)-1]]:u in U]]);
end intrinsic;

intrinsic Degree (xi::Map, N::RngIntElt) -> RngIntElt
{ Given a map ZZ -> K that is a Dirichlet character of modulus N, returns the degree of the (cyclotomic) subfield of K generated by its image. }
    U := UnitGenerators(DirichletGroup(N));
    if #U eq 0 then return 1; end if;
    if Codomain(xi) eq Rationals() then return {xi(u):u in U} eq {1} select 1 else 2; end if;
    return Degree(sub<Codomain(xi) | [xi(u) : u in U]>);
end intrinsic;

intrinsic Parity (xi::Map) -> RngIntElt
{ Given a map ZZ -> K that is a Dirichlet character, returns its parity xi(-1). }
    return Integers()!xi(-1);
end intrinsic;

intrinsic IsReal (xi::Map, N::RngIntElt) -> Bool
{ Given a map ZZ -> K that is a Dirichlet character, returns a boolean indicating whether the character takes only real values (trivial or quadratic) or not. }
    return CharacterOrder(xi,N) le 2;
end intrinsic;

intrinsic AssociatedCharacter (m::RngIntElt,chi::GrpDrchElt) -> GrpDrchElt
{ The Dirichlet character of modulus m induced by the primitive character inducing chi (whose conductor must divide m). }
    return MinimalBaseRingCharacter(FullDirichletGroup(m)!chi);
end intrinsic;

intrinsic AssociatedCharacter (qq::RngIntElt,q::RngIntElt,n::RngIntElt) -> RngIntElt
{ The Conrey index nn of the Conrey character qq.nn of modulus qq induced by the primitive character inducing the Conrey character q.n. }
    require q gt 0 and n gt 0 and GCD(q,n) eq 1: "Conrey characters must be specified by a pair of coprime positive integers q,n.";
    if q eq 1 or n mod q eq 1 then return 1; end if;
    if qq eq q then return n mod qq; end if;
    b,p,e := IsPrimePower(q);
    if not b then return Integers()!&*[Integers(qq)|$$(qq,r[1],r[2]):r in Factorization(q,n)]; end if;
    ee := Valuation(qq,p); qqp := p^ee; qqnp := qq div qqp;
    if ee eq e then return CRT([n,1],[qqp,qqnp]); end if;
    if IsOdd(p) then
        a := ConreyLogModOddPrimePower(p,e,n);
        require ee ge e or IsDivisibleBy(a,p^(e-ee)): "Target modulus must be divisible by conductor";
        if ee gt e then a *:= p^(ee-e); else a div:= p^(e-ee); end if;
        return CRT([Integers()!(Integers(qqp)!ConreyGenerator(p))^a,1],[qqp,qqnp]);
    else
        if e eq 2 then assert n eq 3; require ee ge e: "Target modulus must be divisible by conductor"; return CRT([qqp-1,1],[qqp,qqnp]); end if;
        assert e gt 2;
        a,s := ConreyLogModEvenPrimePower(e,n);
        require ee ge e or IsDivisibleBy(a,2^(e-ee)): "Target modulus must be divisible by conductor";
        if ee gt e then a *:= 2^(ee-e); else a div:= 2^(e-ee); end if;
        return CRT([Integers()!(s*(Integers(qqp)!5)^a),1],[qqp,qqnp]);
    end if;
end intrinsic;

intrinsic AssociatedCharacter (qq::RngIntElt,s::MonStgElt) -> MonStgElt
{ Conrey character qq.nn of modulus qq induced by the primitive character inducing the Conrey character q.n. }
    b,q,n := IsCharacterLabel(s);
    require b: "Conrey labels must have the form q.n with n <= q positive coprime integers";
    return Sprintf("%o.%o",qq,AssociatedCharacter(qq,q,n));
end intrinsic;

intrinsic AssociatedPrimitiveCharacter (q::RngIntElt,n::RngIntElt) -> RngIntElt, RngIntElt
{ The primitive Conrey character qq.nn inducing the Conrey character q.n (returns qq and nn). }
    qq := Conductor(q,n);
    return qq, AssociatedCharacter(qq,q,n);
end intrinsic;

intrinsic AssociatedPrimitiveCharacter (s::MonStgElt) -> MonStgElt
{ Conrey character qq.nn of modulus qq induced by the primitive character inducing the Conrey character q.n. }
    q, n := AssociatedPrimitiveCharacter(a[1],a[2]) where a:=SplitCharacterLabel(s);
    return IsCharacterOrbitLabel(s) select ConreyCharacterOrbitLabel(q,n) else Sprintf("%o.%o",q,n);
end intrinsic;

intrinsic ConreyCharacterProduct (q1::RngIntElt, n1::RngIntElt, q2::RngIntElt, n2::RngIntElt) -> RngIntElt, RngIntElt
{ Computes the product q.n of the Conrey characters q1.n1 and q2.n2, returning q=LCM(q1,q2) and n. }
    if q1 eq 1 then return q2,n2; end if;
    if q2 eq 1 then return q1,n1; end if;
    q := LCM(q1,q2); return q,(AssociatedCharacter(q,q1,n1)*AssociatedCharacter(q,q2,n2)) mod q;
end intrinsic;

intrinsic ConreyCharacterProduct (s1::MonStgElt, s2::MonStgElt) -> MonStgElt
{ Computes the product q.n of the Conrey characters q1.n1 and q2.n2, returning the Conrey label q.n }
    b1,q1,n1 := IsCharacterLabel(s1);  b2,q2,n2 := IsCharacterLabel(s2);
    require b1 and b2: "Conrey labels must have the form q.n with n <= q positive coprime integers";
    return Sprintf("%o.%o",q,n) where q,n := ConreyCharacterProduct(q1,n1,q2,n2);
end intrinsic;

intrinsic ConreyInverse (q::RngIntElt, n::RngIntElt) -> RngIntElt
{ The Conrey index  of the inverse of the Conrey character q.n. }
    require q ge 1 and n ge 1 and n le q and GCD(q,n) eq 1: "n <= q must be positive coprime integers";
    return Integers()!((Integers(q)!n)^-1);
end intrinsic;

intrinsic ConreyInverse (s::MonStgElt) -> MonStgElt
{ The Conrey index  of the inverse of the Conrey character q.n. }
    b,q,n := IsCharacterLabel(s);
    require b: "Conrey labels must have the form q.n with n <= q positive coprime integers";
    return Sprintf("%o.%o",q,ConreyInverse(q,n));
end intrinsic;

intrinsic ConductorProductBound (M::RngIntElt, N::RngIntElt) -> RngIntElt
{ Quickly computes an integer guaranteed to divide the conductor of any product of Dirichlet characters of conductors M and N. }
    d := GCD(M,N);  m := LCM(M,N);
    return (m div d) * &*[Integers()|p^Valuation(d,p):p in PrimeDivisors(d)|Valuation(m,p) ne Valuation(d,p)];
end intrinsic;

intrinsic ConductorProduct (q1::RngIntElt, n1::RngIntElt, q2::RngIntElt, n2::RngIntElt) -> RngIntElt
{ The conductor of the product of the Conrey characters q1.n1 and q2.n2. }   
    c1 := Conductor(q1,n1);  c2 := Conductor(q2,n2);
    P := Set(PrimeDivisors(c1) cat PrimeDivisors(c2));
    c := 1; 
    for p in P do
        e1 := Valuation(c1,p);  e2 := Valuation(c2,p);
        if e1 ne e2 then c *:= p^Max(e1,e2); continue; end if;
        qp1 := p^Valuation(q1,p);  qp2 := p^Valuation(q2,p); cp := p^e1;
        n := (AssociatedCharacter(cp,qp1,n1 mod qp1)*AssociatedCharacter(cp,qp2,n2 mod qp2)) mod cp;
        if n eq 1 then continue; end if;
        c *:= p^(Valuation(Order(Integers(cp)!n),p)+1);
        if p eq 2 and e1 gt 2 and ConreyCharacterValue(cp,n,5) ne 1 then c *:= 2; end if;
    end for;
    return c;
end intrinsic;

intrinsic ConductorProduct (s1::MonStgElt, s2::MonStgElt) -> RngIntElt
{ The conductor of the product of the Conrey characters q1.n1 and q2.n2. }
    b1,q1,n1 := IsCharacterLabel(s1);  b2,q2,n2 := IsCharacterLabel(s2);
    require b1 and b2: "Conrey labels must have the form q.n with n <= q positive coprime integers";
    return ConductorProduct(q1,n1,q2,n2);
end intrinsic;

intrinsic PrimitiveConductorProduct (q1::RngIntElt, n1::RngIntElt, q2::RngIntElt, n2::RngIntElt) -> RngIntElt
{ The conductor of the product of the primitive Conrey characters q1.n1 and q2.n2 (primitivity is not verified). }   
    P := Set(PrimeDivisors(q1) cat PrimeDivisors(q2));
    c := 1; 
    for p in P do
        e1 := Valuation(q1,p);  e2 := Valuation(q2,p);
        if e1 ne e2 then c *:= p^Max(e1,e2); continue; end if;
        R := Integers(p^e1); n := (R!n1)*(R!n2);
        if n eq 1 then continue; end if;
        c *:= p^(Valuation(Order(n),p)+1);
        if p eq 2 and e1 gt 2 and ConreyCharacterValue(2^e1,Integers()!n,5) ne 1 then c *:= 2; end if;
    end for;
    return c;
end intrinsic;

intrinsic PrimitiveConductorProduct (s1::MonStgElt, s2::MonStgElt) -> RngIntElt
{ The conductor of the product of the primitive Conrey characters q1.n1 and q2.n2 (primitivity not verified). }   
    b1,q1,n1 := IsCharacterLabel(s1);  b2,q2,n2 := IsCharacterLabel(s2);
    require b1 and b2: "Conrey labels must have the form q.n with n <= q positive coprime integers";
    return PrimitiveConductorProduct(q1,n1,q2,n2);
end intrinsic;

intrinsic Twist (q1::RngIntElt, n1::RngIntElt, q2::RngIntElt, n2::RngIntElt) -> RngIntElt, RngIntElt
{ Given Conrey characters chi:=q1.n1 and psi:=q2.n2 returns the character tchi:=q.n of modulus q:=LCM(Mudulus(chi),Conductor(psi)*Conductor(chi*psi)) associated to chi*psi^2; if chi is minimal the twist of a twist-minimal newform f of character chi by psi will lie in S_k(q,tchi)^new. }
    q3,n3 := ConreyCharacterProduct (q1,n1,q2,n2);  q4,n4 := ConreyCharacterProduct (q3,n3,q2,n2);
    q := LCM(q1,Conductor(q2,n2)*Conductor(q3,n3));
    return q, AssociatedCharacter (q,q4,n4);
end intrinsic;

intrinsic Twist (s1::MonStgElt, s2::MonStgElt) -> MonStgElt
{ Given Conrey characters chi:=q1.n1 and psi:=q2.n2 returns the character tchi:=q.n of modulus q:=LCM(Mudulus(chi),Conductor(psi)*Conductor(chi*psi)) associated to chi*psi^2; if chi is minimal the twist of a twist-minimal newform f of character chi by psi will lie in S_k(q,tchi)^new. }
    s3 := ConreyCharacterProduct (s1,s2);  return AssociatedCharacter (LCM(Modulus(s1),Conductor(s2)*Conductor(s3)),ConreyCharacterProduct (s3,s2));
end intrinsic;

intrinsic Twist (chi::GrpDrchElt, psi::GrpDrchElt) -> GrpDrchElt
{ Given Dirichlet characters chi and psi returns the character tchi of modulus N:=LCM(Mudulus(chi),Conductor(psi)*Conductor(chi*psi)) associated to chi*psi^2; if chi is minimal the twist of a twist-minimal newform f of character chi by psi will lie in S_k(N,tchi)^new. }
    return DirichletCharacter(Twist(ConreyLabel(chi),ConreyLabel(psi)));
end intrinsic;

// Given an nth-root of unity z in a number field K return angles of conjugates (in standard order of embeddings of K)
function EmbeddedConjugateAngles(z,n)
    C := Conjugates(z);
    CC := Parent(z[1]);
    pi := Pi(RealField());
    return [ NormalizedAngle(Round(n*Argument(c)/(2*pi))/n) : c in C];
end function;

intrinsic ConreyConjugates (chi::GrpDrchElt, xi::Map: ConreyIndexList:=ConreyIndexes(chi)) -> SeqEnum[RngIntElt]
{ Given a Dirichlet character chi embedded as xi with values in a number field K, returns a list of the Conrey labels corresponding to the embeddings of K in C, as ordered by Conjugates. }
    if #ConreyIndexList eq 1 then return [ConreyIndexList[1]:i in [1..Degree(Codomain(xi))]]; end if;
    q := Modulus(chi);  e := Order(chi);
    S := UnitGenerators(chi);
    T := AssociativeArray();
    for n in ConreyIndexList do T[ConreyCharacterAngles(q,n,S)] := n; end for;
    A := [EmbeddedConjugateAngles(xi(m),e) : m in S];
    return [T[[A[i][j] : i in [1..#S]]] : j in [1..#A[1]]];
end intrinsic;

intrinsic TranslatedCharacterAngles (N::RngIntElt, u::SeqEnum[RngIntElt], v::SeqEnum, U::SeqEnum[RngIntElt]) -> SeqEnum[FldRatElt]
{ Given arbitrary generators u for (Z/NZ)* and a corresponding list of angles v defining a character of modulus N, compute a list of angles giving values of character on the integers in S.  Does not verify the validity of v! }
    require N ge 1: "Modulus N must be a positive integer";
    require #u eq #v: "You must specify an angle for each generator";
    require #u gt 0 and &and[(n mod N) ne 1 and GCD(N,n) eq 1:n in u]: "Generators must be coprime to N and not 1 modulo N.";
    v := [NormalizedAngle(x):x in v];
    if U eq u then return v; end if;  // Don't waste time on the (easy) expected case
    if N le 2 then return [Rationals()|1:n in U]; end if;
    evec := UnitGeneratorsLogMap(N,u);
    V := [NormalizedAngle(&+[e[i]*v[i]:i in [1..#u]]) where e:=evec(x): x in U];
    return V;
end intrinsic;

function TestCharacterAngles(M)
    for N:=3 to M do
        U := UnitGenerators(N);
        gm,pi := UnitGroup(Integers(N));
        for chi in CharacterOrbitReps(N) do
            L := ConreyIndexes(chi);
            for n in L do
                V := ConreyCharacterAngles(N,n,U);
                for i:=1 to 3 do
                    S := [Random(gm):i in [1..#U]];
                    while sub<gm|S> ne gm do S := [Random(gm):i in [1..#U]]; end while;
                    u := [Integers()!pi(s):s in S];
                    v := ConreyCharacterAngles(N,n,u);
                    assert TranslatedCharacterAngles(N,u,v,U) eq V;
                end for;
            end for;
        end for;
        printf "Passed three random tests for each Conrey character of modulus %o\n", N;
    end for;
    return true;
end function;

intrinsic DirichletCharacterFromAngles (N::RngIntElt,u::SeqEnum[RngIntElt],v::SeqEnum[FldRatElt]) -> GrpDrchElt
{ Given a modulus N, a list of generators for (Z/NZ)*, and a list of angles v returns the Dirichlet character with values in Q(zeta_n) mapping u[i] to zeta_n^(n*v[i]), where n is the LCM of the denominators in v. }
    require N gt 0: "Modulus N must a positive integer";
    if N lt 3 then assert #v eq 0; return DirichletGroup(N)!1; end if;
    V := TranslatedCharacterAngles(N,u,v,UnitGenerators(N)); // compute angles on standard Magma generators for (Z/NZ)*
    n := LCM([Denominator(e):e in V]);
    if n eq 1 then return DirichletGroup(N)!1; end if;
    if n eq 2 then return DirichletCharacterFromValuesOnUnitGenerators(DirichletGroup(N),[(-1)^(Integers()!(n*e)) : e in V]); end if;
    F := CyclotomicField(n);
    return DirichletCharacterFromValuesOnUnitGenerators(DirichletGroup(N,F),[F|F.1^(Integers()!(n*e)) : e in V]);
end intrinsic;

intrinsic DirichletCharacterFromAngles (N::RngIntElt,v::SeqEnum) -> GrpDrchElt
{ Given a modulus N, a positive integer n, a list of integers u giving standard generates for (Z/NZ)*, and a suitable list of integers v, returns the Dirichlet character with values in Q(zeta_n) mapping u[i] to zeta_n^v[i]. }
    require N gt 0: "Modulus N must a positive integer";
    if N lt 3 then assert #v eq 0; return DirichletGroup(N)!1; end if;
    n := LCM([Denominator(e):e in v]);
    if n eq 1 then return DirichletGroup(N)!1; end if;
    if n eq 2 then return DirichletCharacterFromValuesOnUnitGenerators(DirichletGroup(N),[(-1)^(Integers()!(n*e)) : e in v]); end if;
    F := CyclotomicField(n);
    return DirichletCharacterFromValuesOnUnitGenerators(DirichletGroup(N,F),[F|F.1^(Integers()!(n*e)) : e in v]);
end intrinsic;

intrinsic SquareRoots (chi::GrpDrchElt) -> SeqEnum[GrpDrchElt]
{ A list of the Dirichlet characters psi in the ambient group of chi for which psi^2 = chi (note that only psi in the ambient group of chi will be returned). }
    if IsOdd(Order(chi)) then
        psi := Sqrt(chi);   // this is just computing psi^e where e = 1/2 mod Order(chi), but we'll let Magma do it
    else
        // Deal with the even order case that Magma does not know how to handle
        u := UnitGeneratorOrders(chi);
        v := [r:r in CharacterAngles(chi)];
        if not &and[IsOdd(u[i]) or IsDivisibleBy(u[i],2*Denominator(v[i])):i in [1..#u]] then return [Parent(chi)|]; end if;
        psi := DirichletCharacterFromAngles (Modulus(chi), [r/2:r in v]);
    end if;
    assert psi^2 eq chi;
    // Every square root of chi is psi*xi for some 2-torsion element xi of G; such xi are precisely the rational characters returned by DirichletGroup
    return [Parent(chi)|psi*xi : xi in Elements(DirichletGroup(Modulus(chi)))];
end intrinsic;

intrinsic CyclotomicConreyCharacter (q::RngIntElt,n::RngIntElt) -> GrpDrchElt
{ The Dirichlet character with Conrey label q.n. }
    return DirichletCharacterFromAngles(q,UnitGenerators(q),ConreyCharacterAngles(q,n));
end intrinsic;

intrinsic CyclotomicConreyCharacter (s::MonStgElt) -> GrpDrchElt
{ The Dirichlet character with the specified Conrey label or character orbit label. }
    return CyclotomicConreyCharacter (a[1],a[2]) where a := SplitCharacterLabel(s);
end intrinsic;

intrinsic DirichletCharacter (chi:GrpDrchElt) -> GrpDrchElt
{ The Dirichlet character. }
    return chi;
end intrinsic;

intrinsic DirichletCharacter (q::RngIntElt,n::RngIntElt) -> GrpDrchElt
{ The Dirichlet character with Conrey label q.n, equivalent to CyclotomicConreyCharacter(q,n). }
    return DirichletCharacterFromAngles(q,UnitGenerators(q),ConreyCharacterAngles(q,n));
end intrinsic;

intrinsic DirichletCharacter (s::MonStgElt) -> GrpDrchElt
{ Returns the Dirichlet character with the specified Conrey label or character orbit label. }
    return CyclotomicConreyCharacter(a[1],a[2]) where a := SplitCharacterLabel(s);
end intrinsic;

intrinsic Conjugates (chi::GrpDrchElt) -> SeqEnum[GrpDrchElt]
{ List of Galois conjugates of chi. }
    N :=Modulus(chi); if N le 2 then return [chi]; end if;
    u := UnitGenerators(N); v := CharacterAngles(chi,u);
    return [Parent(chi)|DirichletCharacterFromAngles(N,u,w) : w in ConjugateAngles(v)];
end intrinsic;

intrinsic ConreyConjugates (q::RngIntElt,n::RngIntElt) -> SeqEnum[RngIntElt]
{ Sorted list of Conrey indexes m of all Conrey characters q.m conjugate to q.n. }
    return Sort([Integers()|z^a:a in [1..m]|GCD(m,a)eq 1]) where m:=Order(z) where z := Integers(q)!n;
end intrinsic;

intrinsic ConreyConjugates (s::MonStgElt) -> SeqEnum[MonStgElt]
{ Returns a sorted list of labels of all Conrey characters q.m conjugate to specified Conrey character or in specified character orbit. }
    return ConreyConjugates(a[1],a[2]) where a:=SplitCharacterLabel(s);
end intrinsic;

intrinsic ConreyIndexes (chi::GrpDrchElt) -> SeqEnum[RngIntElt]
{ Sorted list of Conrey indexes of the Galois conjugates of the specified Dirichlet charatacter. }
    return Sort([ConreyIndex(psi):psi in Conjugates(chi)]);
end intrinsic;

intrinsic ConreyIndexes (s::MonStgElt) -> SeqEnum[RngIntElt]
{ Sorted list of integers n giving the Conrey labels q.n of the conjugates in the specifeid Galois orbit of modulus N. }
    return ConreyConjugates (a[1],a[2]) where a:=SplitCharacterLabel(s);
end intrinsic;

intrinsic ConreyLabels (chi::GrpDrchElt) -> SeqEnum[RngIntElt]
{ Sorted list of Conrey indexes of the Galois conjugates of the specified Dirichlet charatacter. }
    qs := sprint(Modulus(chi));
    return [qs cat "." cat IntegerToString(n): n in ConreyIndexes(chi)];
end intrinsic;

intrinsic ConreyLabels (s::MonStgElt) -> SeqEnum[MonSTgElt]
{ Returns a sorted list of labels of all Conrey characters q.m conjugate to specified Conrey character or in specified character orbit. }
    qs := Split(s,".")[1];
    return [qs cat "." cat IntegerToString(n): n in ConreyIndexes(s)];
end intrinsic;

intrinsic ConreyOrbitTable (filename::MonStgElt, M::RngIntElt) -> SeqEnum[SeqEnum[RngIntElt]]
{ Given the name of input file containing records N:o:L:... where L is a list of Conrey indexes n of Conrey characters N.n with orbit index o, creates table T[N][n] := o. }
    require M gt 0: "Second argument must be a positive integer.";
    S := [Split(r,":"):r in Split(Read(filename))];
    T := [[0:n in [1..N]]:N in [1..M]];
    for r in S do N := StringToInteger(r[1]); if N le M then o := StringToInteger(r[2]); for n in StringToIntegerArray(r[3]) do T[N][n] := o; end for; end if; end for;
    return T;
end intrinsic;

intrinsic ConreyOrbitLabelTable (filename::MonStgElt,M::RngIntElt) -> SeqEnum[SeqEnum[MonStgElt]]
{ Given the name of input file containing records N:o:L:... where L is a list of Conrey indexes n of Conrey characters N.n with orbit index o, creates table T[N][n] := N.a where N.a is the lable of the character orbit of modulus N and index o. }
    require M gt 0: "Second argument must be a positive integer.";
    S := [Split(r,":"):r in Split(Read(filename))];
    T := [["":n in [1..N]]:N in [1..M]];
    for r in S do N:=atoi(r[1]); if N le M then s := r[1] cat "." cat Base26Encode(atoi(r[2])-1); for n in atoii(r[3]) do T[N][n]:=s; end for; end if; end for;
    return T;
end intrinsic;

intrinsic CharacterFromValues (N::RngIntElt,u::SeqEnum[RngIntElt],v::SeqEnum:Orbit:=false) -> Map
{ Given a modulus N, a list of generators of (Z/NZ)*, and a corresponding list of roots of unity in a number/cyclotomic field K, returns a map ZZ -> K for the Dirichlet character. }
    require N gt 0: "Modulus must be a positive integer";
    require #u eq #v: "List of unit generators and values must be lists of the same length";
    K := Universe(v);
    if N le 2 then psi:=map< Integers()->K | x :-> GCD(N,x) eq 1 select 1 else 0 >; if Orbit then return psi,1; else return psi; end if; end if;
    A,pi := UnitGroup(Integers(N)); ipi:=Inverse(pi);
    u0 := [pi(A.i):i in [1..NumberOfGenerators(A)]];
    if u ne u0 then assert sub<A|[ipi(n):n in u]> eq A; end if;
    // handle trivial character quickly
    if &and[z eq 1:z in v] then psi:=map< Integers()->K | x :-> GCD(N,x) eq 1 select 1 else 0 >; if Orbit then return psi,1; else return psi; end if; end if;
    if u ne u0 then
        f := UnitGeneratorsLogMap(N,u);
        v0 := [prod([v[i]^e[i]:i in [1..#u]]) where e:=f(g):g in u0];
        u := u0; v := v0;
    end if;
    psi := map< Integers()->K | x :-> GCD(N,x) eq 1 select &*[v[i]^(Eltseq(ipi(x))[i]):i in [1..#v]] else K!0>;
    if not Orbit then return psi; end if;
    // if Orbit flag is set, determine the character orbit by comparing traces (note that we need tot take traces from the subfield of K generated by the image of psi)
    m := LCM([Min([d:d in Divisors(EulerPhi(N))|z^d eq 1]):z in v]);
    d := EulerPhi(m); e := ExactQuotient(Degree(K),d);
    t := [ExactQuotient(Trace(psi(n)),e) : n in [1..N]];
    G := CharacterOrbitReps(N);
    M := [i : i in [1..#G] | Order(G[i]) eq m and [Trace(z):z in ValueList(G[i])] eq t];
    assert #M eq 1;
    return psi,M[1];
end intrinsic;

intrinsic NewModularSymbols (s::MonStgElt, k::RngIntElt) -> ModSym
{ Returns newspace of modular symbols of weight k for the Dirichlet character chi with sign -1. }
    return NewSubspace(CuspidalSubspace(ModularSymbols(DirichletCharacter(s),k,-1)));
end intrinsic;

intrinsic NewModularSymbols (s::MonStgElt) -> ModSym
{ Returns newspace of modular symbols of weight k for the newspace with label s. }
    t := Split(s,".");
    return NewSubspace(CuspidalSubspace(ModularSymbols(DirichletCharacter(t[1] cat "." cat t[3]),atoi(t[2]),-1)));
end intrinsic;
