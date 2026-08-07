AttachSpec("magma.spec");
SetSeed(1);
print "test_gl2tab.m";

print "  GL2CompareRSZBLabels";
// total-order sanity on a sample, plus documented -1/0/1 range and '?' sorting last
rszb := ["1.1.0.1","2.2.0.1","2.3.0.1","2.6.0.1","4.2.0.1","4.4.0.2","4.4.0.1","8.2.0.1","8.2.0.2","16.24.1.13","3.4.0.1","?"];
for a in rszb, b in rszb do
    ca := GL2CompareRSZBLabels(a,b); cb := GL2CompareRSZBLabels(b,a);
    assert ca in [-1,0,1] and Sign(ca) eq -Sign(cb);            // antisymmetry
    assert (ca eq 0) eq (a eq b);
end for;
assert GL2CompareRSZBLabels("2.3.0.1","2.2.0.1") eq 1;          // index 3 > 2
assert GL2CompareRSZBLabels("4.2.0.1","16.24.1.13") eq -1;      // level 4 < 16 (numeric, not lex)
assert GL2CompareRSZBLabels("8.2.0.1","?") eq -1;               // "?" sorts last
// determinant-prefixed labels: GL1 prefix compared first, trivial det (no prefix) sorts first
assert GL2CompareRSZBLabels("2.2.1-4.8.0.1","4.8.0.1") eq 1 and GL2CompareRSZBLabels("4.8.0.1","2.2.1-4.8.0.1") eq -1;
assert GL2CompareRSZBLabels("2.2.1-4.8.0.1","2.2.1-4.8.0.2") eq -1;
assert GL2CompareRSZBLabels("2.2.1-4.8.0.1","3.2.1-4.8.0.1") eq -1;

print "  GL2CompareLMFDBLabels";
lm := ["1.1.0.a.1","2.2.0.a.1","2.6.0.a.1","4.24.0.b.1","4.24.0-2.a.1.1","4.24.0-4.a.1.1","4.24.0-4.b.1.2","4.24.0-4.b.1.1",
       "4.24.0.a.1","4.12.0.c.1","8.12.0.a.1","10.12.0.a.1","4.24.0.z.1","4.24.0.ba.1","?"];
for a in lm, b in lm do
    ca := GL2CompareLMFDBLabels(a,b); cb := GL2CompareLMFDBLabels(b,a);
    assert Sign(ca) eq -Sign(cb) and ((ca eq 0) eq (a eq b));
end for;
assert GL2CompareLMFDBLabels("10.12.0.a.1","8.12.0.a.1") eq 2;      // level compared numerically
assert GL2CompareLMFDBLabels("4.24.0.z.1","4.24.0.ba.1") lt 0;      // base26: z=25 < ba=26
// coarse label sorts immediately before its own quadratic refinements, after refinements of earlier classes
assert GL2CompareLMFDBLabels("4.24.0.b.1","4.24.0-4.b.1.1") lt 0;
assert GL2CompareLMFDBLabels("4.24.0-4.a.1.1","4.24.0.b.1") lt 0;
assert GL2CompareLMFDBLabels("4.24.0-2.a.1.1","4.24.0-4.a.1.1") lt 0;  // coarse level 2 < 4

print "  GL2SortLabels";
S := GL2SortRSZBLabels(rszb);
for i in [1..#S-1] do assert GL2CompareRSZBLabels(S[i],S[i+1]) lt 0; end for;
assert GL2SortRSZBLabels(S) eq S;                                    // idempotent
T := GL2SortLMFDBLabels(lm);
for i in [1..#T-1] do assert GL2CompareLMFDBLabels(T[i],T[i+1]) lt 0; end for;
assert GL2SortLMFDBLabels(T) eq T;
assert GL2SortLabels(["4.2.0.1","2.2.0.1"]) eq ["2.2.0.1","4.2.0.1"];        // RSZB dispatch (4 parts)
assert GL2SortLabels(["4.2.0.a.1","2.2.0.a.1"]) eq ["2.2.0.a.1","4.2.0.a.1"];// LMFDB dispatch (5 parts)
assert GL2SortLabels([Strings()|]) eq [Strings()|];
assert GL2MinRSZBLabel(rszb) eq "1.1.0.1" and GL2MaxRSZBLabel(rszb) eq "?";
assert GL2MinLMFDBLabel(lm) eq "1.1.0.a.1" and GL2MaxLMFDBLabel(lm) eq "?";

print "  GL2CompareLabelLists";
assert GL2CompareRSZBLabelLists(["2.2.0.1"],["2.2.0.1","4.2.0.1"]) eq -1;   // prefix sorts first
assert GL2CompareRSZBLabelLists(["2.2.0.1","4.2.0.1"],["2.2.0.1"]) eq 1;
assert GL2CompareRSZBLabelLists(["2.3.0.1"],["2.2.0.1","4.2.0.1"]) eq 1;
assert GL2CompareLMFDBLabelLists(["2.2.0.a.1"],["2.2.0.a.1"]) eq 0;
assert GL2CompareLMFDBLabelLists(["2.2.0.a.1","4.2.0.a.1"],["2.3.0.a.1"]) eq -1;
LL := [["2.2.0.1","4.2.0.1"],["2.2.0.1"],["2.3.0.1"],["2.2.0.1","2.3.0.1"]];
SL := GL2SortRSZBLabelLists(LL);
assert SL eq [["2.2.0.1"],["2.2.0.1","2.3.0.1"],["2.2.0.1","4.2.0.1"],["2.3.0.1"]];
assert GL2SortLMFDBLabelLists([["2.3.0.a.1"],["2.2.0.a.1"]]) eq [["2.2.0.a.1"],["2.3.0.a.1"]];

print "  GL2CoarseLabel";
// ground truth from LMFDB: SELECT label,coarse_label FROM gps_gl2zhat_fine WHERE contains_negative_one='f'
for r in [<"3.8.0-3.a.1.1","3.4.0.a.1">, <"4.4.0-2.a.1.1","2.2.0.a.1">, <"4.4.0-4.a.1.1","4.2.0.a.1">,
          <"4.12.0-2.a.1.2","2.6.0.a.1">, <"4.24.0-4.d.1.2","4.12.0.d.1">, <"4.48.0-4.c.1.1","4.24.0.c.1">,
          <"5.24.0-5.a.1.1","5.12.0.a.1">] do
    assert GL2CoarseLabel(r[1]) eq r[2];
end for;
assert GL2CoarseLabel("8.8.0.a.1") eq "8.8.0.a.1";  // coarse labels are fixed points

print "  GL2Save/GL2Load";
// build records via a lattice file (header label:gens:parents dispatches GL2Load->GL2LoadLattice)
fp := Open("tests/tmp_gl2tab_lat.txt","w");
Puts(fp,"label:gens:parents");
Puts(fp,"2.2.0.a.1:[[0,1,1,1]]:[\"1.1.0.a.1\"]");
Puts(fp,"2.3.0.a.1:[[0,1,1,0]]:[\"1.1.0.a.1\"]");
Puts(fp,"4.2.0.a.1:[[0,3,1,0],[1,1,1,2],[3,0,2,3]]:[\"1.1.0.a.1\"]");
Flush(fp); delete fp;
X := GL2Load("tests/tmp_gl2tab_lat.txt");
assert Sort([k:k in Keys(X)]) eq ["2.2.0.a.1","2.3.0.a.1","4.2.0.a.1"];
assert GL2Index(X["2.3.0.a.1"]`subgroup) eq 3 and X["2.3.0.a.1"]`negone and X["2.3.0.a.1"]`genus eq 0;
// filters (each label component parsed numerically off the front of the line)
X2 := GL2LoadLattice("tests/tmp_gl2tab_lat.txt" : N:=2);
assert Sort([k:k in Keys(X2)]) eq ["2.2.0.a.1","2.3.0.a.1"];
X3 := GL2LoadLattice("tests/tmp_gl2tab_lat.txt" : IndexLimit:=2);
assert Sort([k:k in Keys(X3)]) eq ["2.2.0.a.1","4.2.0.a.1"];
// REGRESSION (colsplit bug, gl2tab.m line 33): serialized records whose last data
// column (secs) is empty must roundtrip through GL2RecToString/GL2RecFromString and
// GL2Save/GL2Load; the old colsplit appended a spurious extra field to lines ending in ":".
s := GL2RecToString(X["2.3.0.a.1"]);      // secs unassigned => serialized line ends with ":"
assert s[#s] eq ":";
r := GL2RecFromString(s);
assert r`label eq "2.3.0.a.1" and r`level eq 2 and r`index eq 3 and r`negone and not assigned r`secs;
GL2Save("tests/tmp_gl2tab_dat0.txt",X);
X0 := GL2Load("tests/tmp_gl2tab_dat0.txt");
assert Keys(X0) eq Keys(X);
// save/load roundtrip (with secs assigned so the last serialized column is nonempty)
for k in Keys(X) do r := X[k]; r`secs := 1.5; X[k] := r; end for;
GL2Save("tests/tmp_gl2tab_dat.txt",X);
X4 := GL2Load("tests/tmp_gl2tab_dat.txt");
assert Keys(X4) eq Keys(X);
for k in Keys(X) do
    assert X4[k]`level eq X[k]`level and X4[k]`index eq X[k]`index and X4[k]`genus eq X[k]`genus;
    assert X4[k]`gens eq X[k]`gens and X4[k]`negone eq X[k]`negone and X4[k]`parents eq X[k]`parents;
end for;
X5 := GL2Load("tests/tmp_gl2tab_dat.txt" : N:=4);
assert [k:k in Keys(X5)] eq ["4.2.0.a.1"];
X6 := GL2Load("tests/tmp_gl2tab_dat.txt" : IndexLimit:=2);
assert Sort([k:k in Keys(X6)]) eq ["2.2.0.a.1","4.2.0.a.1"];
// GL2RecToString/GL2RecFromString direct roundtrip
s := GL2RecToString(X["2.3.0.a.1"]);
r := GL2RecFromString(s);
assert r`label eq "2.3.0.a.1" and r`level eq 2 and r`index eq 3 and r`negone and GL2Index(r`subgroup) eq 3;
// REGRESSION (GL2Load filter bug, gl2tab.m lines 310/314/320): the N and IndexLimit
// filters parsed labels via S[i][1..32], crashing on data lines shorter than 32 chars.
fp := Open("tests/tmp_gl2tab_short.txt","w");
Puts(fp,"label:level:index:negone:gens");
Puts(fp,"2.2.0.a.1:2:2:1:[[0,1,1,1]]");    // 27-character line
Flush(fp); delete fp;
// (GL2Load prints a warning about absent columns for this minimal file; that is expected)
XS0 := GL2Load("tests/tmp_gl2tab_short.txt");
assert #XS0 eq 1;
XS1 := GL2Load("tests/tmp_gl2tab_short.txt" : N:=2);
assert #XS1 eq 1 and IsDefined(XS1,"2.2.0.a.1") and XS1["2.2.0.a.1"]`index eq 2;
XS2 := GL2Load("tests/tmp_gl2tab_short.txt" : N:=3);
assert #XS2 eq 0;
XS3 := GL2Load("tests/tmp_gl2tab_short.txt" : IndexLimit:=2);
assert #XS3 eq 1;
XS4 := GL2Load("tests/tmp_gl2tab_short.txt" : N:=2, IndexLimit:=1);
assert #XS4 eq 0;

print "  GL2LoadLattice fine groups";
Hf := GL2SubgroupFromRZBLabel("X2a"); _,Hf := GL2Level(Hf);  // 4.4.0-2.a.1.1 (LMFDB RZBlabel=X2a)
fp := Open("tests/tmp_gl2tab_lat2.txt","w");
Puts(fp,"label:gens:parents");
Puts(fp,"2.2.0.a.1:[[0,1,1,1]]:[\"1.1.0.a.1\"]");
Puts(fp,Sprintf("4.4.0-2.a.1.1:%o:[\"2.2.0.a.1\"]", sprint(GL2Generators(Hf))));
Flush(fp); delete fp;
XL := GL2LoadLattice("tests/tmp_gl2tab_lat2.txt");
r := XL["4.4.0-2.a.1.1"];
assert r`level eq 4 and r`index eq 4 and not r`negone and r`genus eq 0;
assert not GL2ContainsNegativeOne(r`subgroup);
XLf := GL2LoadLattice("tests/tmp_gl2tab_lat2.txt" : fineN:=2);      // drops fine groups of level ne 2
assert [k:k in Keys(XLf)] eq ["2.2.0.a.1"];
XLi := GL2LoadLattice("tests/tmp_gl2tab_lat2.txt" : IndexLimit:=2); // fine groups get 2*IndexLimit
assert Sort([k:k in Keys(XLi)]) eq ["2.2.0.a.1","4.4.0-2.a.1.1"];

print "  SL2LoadLattice";
SH := SL2Intersection(GL2Borel(2)); _,SH := SL2Level(SH);           // SL2 level 2, index 3
fp := Open("tests/tmp_gl2tab_slat.txt","w");
Puts(fp,"label:gens:parents");
Puts(fp,Sprintf("2.3.0.a.1:%o:[\"1.1.0.a.1\"]", sprint(SL2Generators(SH))));
Flush(fp); delete fp;
XS := SL2LoadLattice("tests/tmp_gl2tab_slat.txt");
r := XS["2.3.0.a.1"];
assert r`level eq 2 and r`index eq 3 and assigned r`subgroup`SL;

print "  GL2LookupTable/GL2LookupLabel";
H22 := sub<GL(2,Integers(2))|[[0,1,1,1]]>;   // 2.2.0.a.1
H23 := sub<GL(2,Integers(2))|[[0,1,1,0]]>;   // 2.3.0.a.1
fp := Open("tests/tmp_gl2tab_key.txt","w");
Puts(fp,"label:key:gens");
Puts(fp,Sprintf("2.2.0.a.1:%o:%o", GL2SubgroupKey(H22), sprint(GL2Generators(H22))));
Puts(fp,Sprintf("2.3.0.a.1:%o:%o", GL2SubgroupKey(H23), sprint(GL2Generators(H23))));
Flush(fp); delete fp;
Z := GL2LookupTable("tests/tmp_gl2tab_key.txt");
assert GL2LookupLabel(Z,H23) eq "2.3.0.a.1";
assert GL2LookupLabel(Z,H23^Random(GL(2,Integers(2)))) eq "2.3.0.a.1";  // conjugation-invariant
assert GL2LookupLabel(Z,GL2Borel(3)) eq "?";                            // not in table
Zg := GL2LookupTable("tests/tmp_gl2tab_key.txt" : makegroups:=true);
assert GL2LookupLabel(Zg,H22) eq "2.2.0.a.1";
// REGRESSION (gl2keytab/gl2finetab Genus bug, gl2tab.m lines 381/432): with makegroups
// the Genus attribute was assigned a string instead of an integer.
for k -> v in Zg do for t in v do assert Type(t[2]`Genus) eq RngIntElt; end for; end for;
assert Type(GL2Genus(Zg[GL2SubgroupKey(H23)][1][2] : NoGenusData)) eq RngIntElt;
// two-file (coarse,fine) lookup table finds fine groups up to conjugacy
fp := Open("tests/tmp_gl2tab_fine.txt","w");
Puts(fp,"label:gens");
Puts(fp,Sprintf("4.4.0-2.a.1.1:%o", sprint(GL2Generators(Hf))));
Flush(fp); delete fp;
ZT := GL2LookupTable("tests/tmp_gl2tab_key.txt","tests/tmp_gl2tab_fine.txt");
assert GL2LookupLabel(ZT,H22) eq "2.2.0.a.1";
assert GL2LookupLabel(ZT,Hf) eq "4.4.0-2.a.1.1";
assert GL2LookupLabel(ZT,Hf^Random(GL(2,Integers(4)))) eq "4.4.0-2.a.1.1";
assert GL2LookupLabel(ZT,GL2Borel(3)) eq "?";
ZTg := GL2LookupTable("tests/tmp_gl2tab_key.txt","tests/tmp_gl2tab_fine.txt" : makegroups:=true);
assert GL2LookupLabel(ZTg,Hf) eq "4.4.0-2.a.1.1";
// REGRESSION (Genus bug in gl2finetab, gl2tab.m line 432): fine-table groups too
for k -> v in ZTg[2] do for t in v do assert Type(t[2]`Genus) eq RngIntElt; end for; end for;
// REGRESSION (GL2LoadLattice lookup bug, gl2tab.m lines 339/355): lookup:=true always
// raised 'Logical expected' from 'require key: ...' (key is an integer column index).
fp := Open("tests/tmp_gl2tab_klat.txt","w");
Puts(fp,"label:key:gens:parents");
Puts(fp,Sprintf("2.2.0.a.1:%o:%o:[\"1.1.0.a.1\"]", GL2SubgroupKey(H22), sprint(GL2Generators(H22))));
Puts(fp,Sprintf("2.3.0.a.1:%o:%o:[\"1.1.0.a.1\"]", GL2SubgroupKey(H23), sprint(GL2Generators(H23))));
Flush(fp); delete fp;
XK,ZK := GL2LoadLattice("tests/tmp_gl2tab_klat.txt" : lookup:=true);
assert Sort([k:k in Keys(XK)]) eq ["2.2.0.a.1","2.3.0.a.1"];
assert GL2LookupLabel(ZK,H23) eq "2.3.0.a.1";
// a lattice file without a key column must still be rejected when lookup is requested
ok := true;
try XB,ZB := GL2LoadLattice("tests/tmp_gl2tab_lat.txt" : lookup:=true); ok := false; catch e assert "key" in e`Object; end try;
assert ok;
// SL2 flavor (also exercises the line-355 fix: table must carry the SL flag)
fp := Open("tests/tmp_gl2tab_sklat.txt","w");
Puts(fp,"label:key:gens:parents");
Puts(fp,Sprintf("2.3.0.a.1:%o:%o:[\"1.1.0.a.1\"]", SL2SubgroupKey(SH), sprint(SL2Generators(SH))));
Flush(fp); delete fp;
XSK,ZSK := SL2LoadLattice("tests/tmp_gl2tab_sklat.txt" : lookup:=true);
assert assigned ZSK`SL;
assert SL2LookupLabel(ZSK,SH) eq "2.3.0.a.1";

print "  GL2LabelTable/GL2LookupGroup";
ZL := GL2LabelTable(Z);
assert Sort([k:k in Keys(ZL)]) eq ["2.2.0.a.1","2.3.0.a.1"];
G := GL2LookupGroup(ZL,"2.3.0.a.1");
assert GL2Index(G) eq 3 and IsConjugate(GL2Ambient(2),G,H23);
ZL2 := GL2LabelTable(Z : N:=2);
assert #ZL2 eq 2;
ZLf := GL2LabelTable("tests/tmp_gl2tab_key.txt");
assert GL2Index(GL2LookupGroup(ZLf,"2.2.0.a.1")) eq 2;
// REGRESSION (GL2LabelTable/SL2LabelTable makegroups bug, gl2tab.m lines 457/469):
// the N filter read r`Level off the tuple instead of the group, crashing with
// "Invalid attribute 'Level'" on makegroups tables.
ZgL2 := GL2LabelTable(Zg : N:=2);
assert Sort([k:k in Keys(ZgL2)]) eq ["2.2.0.a.1","2.3.0.a.1"];
assert GL2Index(GL2LookupGroup(ZgL2,"2.3.0.a.1")) eq 3;
ZgL3 := GL2LabelTable(Zg : N:=3);
assert #ZgL3 eq 0;

print "  SL2LookupTable/SL2LookupLabel/SL2LabelTable";
fp := Open("tests/tmp_gl2tab_skey.txt","w");
Puts(fp,"label:key:gens");
Puts(fp,Sprintf("2.3.0.a.1:%o:%o", SL2SubgroupKey(SH), sprint(SL2Generators(SH))));
Flush(fp); delete fp;
ZS := SL2LookupTable("tests/tmp_gl2tab_skey.txt");
assert SL2LookupLabel(ZS,SH) eq "2.3.0.a.1";
ZSg := SL2LookupTable("tests/tmp_gl2tab_skey.txt" : makegroups:=true);
assert SL2LookupLabel(ZSg,SH) eq "2.3.0.a.1";
ZSL := SL2LabelTable(ZS);
assert SL2Index(SL2LookupGroup(ZSL,"2.3.0.a.1")) eq 3;
// REGRESSION (SL2LabelTable makegroups bug, gl2tab.m line 469): N filter on makegroups table
ZSgL2 := SL2LabelTable(ZSg : N:=2);
assert SL2Index(SL2LookupGroup(ZSgL2,"2.3.0.a.1")) eq 3;
ZSgL3 := SL2LabelTable(ZSg : N:=3);
assert #ZSgL3 eq 0;
System("rm -f tests/tmp_gl2tab_*.txt");

// FLAGGED (audit 2026-08-06): GL2LookupLabel(Z::Tup)/SL2LookupLabel(Z::Tup) contain dead code
// after 'return NotFound;' (would return an integer index instead of a label if re-enabled).

print "  GL2SLabel";
// ground truth from LMFDB: SELECT label,"Slabel",generators FROM gps_gl2zhat_fine WHERE "Slabel" IS NOT NULL AND level IN (5,7,11)
slp := [
 <5, [[1,2,2,0],[2,0,2,4]], "5S4">, <5, [[2,2,0,1],[3,4,0,3]], "5B">, <5, [[3,4,1,2],[4,4,0,1]], "5Nn">,
 <5, [[4,2,0,3],[4,2,0,4]], "5B.4.1">, <5, [[1,0,0,4],[2,2,0,4]], "5B.4.2">, <5, [[0,1,2,0],[4,0,0,3]], "5Ns">,
 <5, [[1,4,2,1]], "5Cn">, <5, [[0,4,1,1],[3,2,4,2]], "5Nn.1.1.1">, <5, [[1,0,0,2],[3,0,0,3]], "5Cs">,
 <5, [[0,3,4,0],[4,0,0,1]], "5Ns.2.1">, <5, [[1,0,0,2],[4,0,0,4]], "5Cs.4.1">, <5, [[0,1,3,0]], "5Cn.0.1">,
 <7, [[5,3,0,6],[6,2,0,4]], "7B">, <7, [[3,3,5,0],[4,0,3,3]], "7Nn">, <7, [[2,1,0,6],[5,5,0,6]], "7B.6.3">,
 <7, [[1,3,0,6],[5,5,0,5]], "7B.6.2">, <7, [[6,0,0,5],[6,5,0,1]], "7B.6.1">, <7, [[0,3,4,0],[1,0,0,5]], "7Ns">,
 <7, [[1,1,5,1]], "7Cn">, <7, [[4,6,0,3],[6,0,1,1]], "7Nn.1.3">, <7, [[3,0,0,2],[3,0,0,3]], "7Cs">,
 <7, [[0,5,6,0],[3,0,0,5]], "7Ns.3.1">, <7, [[0,4,3,0],[2,0,0,5]], "7Ns.6.1.2">, <7, [[5,0,0,2],[6,0,0,6]], "7Cs.6.2">,
 <7, [[3,0,0,1],[6,0,0,6]], "7Cs.6.1">, <11, [[5,2,0,2],[6,3,0,3]], "11B">, <11, [[2,7,5,9],[6,1,6,5]], "11Nn">,
 <11, [[3,2,9,4],[10,3,2,8]], "11S4">, <11, [[7,2,0,10],[8,9,0,1]], "11B.10.2">, <11, [[4,0,0,7],[10,2,0,1]], "11B.10.3"> ];
for r in slp do
    H := sub<GL(2,Integers(r[1]))|r[2]>;
    assert GL2SLabel(H) eq r[3];
end for;

print "  GL2SubgroupFromSLabel";
for r in slp do
    H := GL2SubgroupFromSLabel(r[3]);
    assert GL2SLabel(H) eq r[3];                                     // roundtrip
    assert IsConjugate(GL(2,r[1]),ChangeRing(H,GF(r[1])),sub<GL(2,GF(r[1]))|r[2]>);
end for;
// GL(2,2) special cases: GL(2,2)=S3, groups of order 1,2,3,6 -> 2Cs,2B,2Cn,2G
assert GL2SLabel(sub<GL(2,Integers(2))|>) eq "2Cs";
assert GL2SLabel(sub<GL(2,Integers(2))|[[0,1,1,0]]>) eq "2B";
assert GL2SLabel(sub<GL(2,Integers(2))|[[0,1,1,1]]>) eq "2Cn";
assert GL2SLabel(GL(2,Integers(2))) eq "2G";
for s in ["2Cs","2B","2Cn","2G"] do assert GL2SLabel(GL2SubgroupFromSLabel(s)) eq s; end for;

print "  GL2SZLabel";
// ground truth from LMFDB: SELECT label,"SZlabel" FROM gps_gl2zhat_fine WHERE "SZlabel" IS NOT NULL
szp := [ <"2.2.0.a.1","2A0-2a">, <"2.3.0.a.1","2B0-2a">, <"2.6.0.a.1","2C0-2a">, <"3.3.0.a.1","3A0-3a">,
 <"3.4.0.a.1","3B0-3a">, <"3.6.0.b.1","3C0-3a">, <"3.12.0.a.1","3D0-3a">, <"4.2.0.a.1","2A0-4a">,
 <"4.4.0.a.1","4A0-4a">, <"4.6.0.e.1","4C0-4a">, <"4.6.0.d.1","4C0-4b">, <"4.6.0.c.1","4B0-4b">,
 <"4.6.0.b.1","4B0-4a">, <"4.6.0.a.1","2C0-4a">, <"4.8.0.b.1","4D0-4a">, <"4.12.0.f.1","4F0-4a">,
 <"4.24.0.c.1","4G0-4b"> ];
for r in szp do
    assert GL2SZLabel(r[1]) eq r[2];
    assert GL2LabelFromSZLabel(r[2]) eq r[1];
    H := GL2SubgroupFromSZLabel(r[2]);
    l := Split(r[1],"."); N,HH := GL2Level(H);
    assert N eq atoi(l[1]);
    if N gt 1 then assert GL2Index(HH) eq atoi(l[2]) and GL2Genus(HH) eq atoi(l[3]); end if;
end for;
assert GL2SZLabel("7.8.0.a.1") eq "7B0-7a";  // X0(7); LMFDB SZlabel
assert GL2SZLabel("11.12.1.a.1") eq "";      // X0(11) has finitely many rational points, no SZ label
assert GL2SubgroupFromSZLabel("1A0-1a") eq GL2Ambient(1);

print "  GL2RZBLabel";
// ground truth from LMFDB: SELECT label,"RZBlabel" FROM gps_gl2zhat_fine WHERE "RZBlabel" IS NOT NULL
rzp := [ <"1.1.0.a.1","X1">, <"2.2.0.a.1","X2">, <"2.3.0.a.1","X6">, <"2.6.0.a.1","X8">,
 <"4.2.0.a.1","X3">, <"4.4.0.a.1","X7">, <"4.4.0-4.a.1.1","X3a">, <"4.4.0-2.a.1.1","X2a">,
 <"4.6.0.e.1","X11">, <"4.6.0.d.1","X12">, <"4.6.0.c.1","X13">, <"4.6.0.b.1","X9">, <"4.6.0.a.1","X10">,
 <"4.8.0.a.1","X21">, <"4.8.0.b.1","X20">, <"4.12.0-4.c.1.2","X13f">, <"4.24.0-4.a.1.2","X24d"> ];
for r in rzp do
    assert GL2RZBLabel(r[1]) eq r[2];
    assert GL2LabelFromRZBLabel(r[2]) eq r[1];
    H := GL2SubgroupFromRZBLabel(r[2]);
    l := Split(r[1],"."); N,HH := GL2Level(H);
    assert N eq atoi(l[1]);
    if N gt 1 then
        assert GL2Index(HH) eq atoi(l[2]) and GL2Genus(HH) eq atoi(Split(l[3],"-")[1]);
        assert GL2ContainsNegativeOne(HH) eq (#l eq 5);
    end if;
end for;
assert GL2RZBLabel("3.4.0.a.1") eq "";  // only 2-power levels have RZB labels

print "  GL2CPLabels";
// ground truth from LMFDB: SELECT label,"CPlabel",generators FROM gps_gl2zhat_fine WHERE "CPlabel" IS NOT NULL
cpp := [ <5, [[1,2,2,0],[2,0,2,4]], "5A0">, <5, [[2,2,0,1],[3,4,0,3]], "5B0">, <5, [[3,4,1,2],[4,4,0,1]], "5C0">,
 <7, [[5,3,0,6],[6,2,0,4]], "7B0">, <7, [[1,1,5,1]], "7A1">, <7, [[3,0,0,2],[3,0,0,3]], "7B1">,
 <11, [[5,2,0,2],[6,3,0,3]], "11A1">, <11, [[3,2,9,4],[10,3,2,8]], "11B1"> ];
for r in cpp do
    H := sub<GL(2,Integers(r[1]))|r[2]>;
    assert r[3] in GL2CPLabels(H);
end for;
assert GL2CPLabels(GL2Ambient(1)) eq ["1A0"];

print "  SL2SubgroupFromCPLabel";
for lbl in ["1A0","2A0","5B0","7A1","11A1","6C1","8A2","12B13","10C2"] do
    H := SL2SubgroupFromCPLabel(lbl);
    assert lbl in GL2CPLabels(H);                                    // roundtrip
    // CP label format: level then letter(s) then genus
    i := 1; while lbl[i] ge "0" and lbl[i] le "9" do i +:= 1; end while;
    j := #lbl; while lbl[j] ge "0" and lbl[j] le "9" do j -:= 1; end while;
    N := atoi(lbl[1..i-1]); g := atoi(lbl[j+1..#lbl]);
    assert GL2Genus(H) eq g;
    if N gt 1 then assert SL2Level(H) eq N; end if;
end for;
// REGRESSION (error-message doc-bug, gl2tab.m line 1169): message said "Rouse--Zureick-Brown"
ok := true;
try H := SL2SubgroupFromCPLabel("nonsense"); ok := false; catch e assert "Cummins-Pauli" in e`Object; end try;
assert ok;

print "ALL TESTS PASSED test_gl2tab.m";
quit;
