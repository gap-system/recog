testFDPM := function(deg, field, alternating)
local old_info_level, g, gens, mgens, m, cf, dims, max, pos, x, new_gens,
  h, result;
old_info_level := InfoLevel(InfoRecog);
if alternating then
  g := AlternatingGroup(deg);
else
  g := SymmetricGroup(deg);
fi;
repeat
  gens := List([1..5],x->PseudoRandom(g));
until Size(Group(gens)) = Size(g);
mgens := List(gens,x->PermutationMat(x,deg,field));
m := GModuleByMats(mgens,field);
cf := MTX.CompositionFactors(m);
dims := List(cf,x->x.dimension);
max := Maximum(dims);
pos := Position(dims,max);
x := PseudoRandom(GL(max,field));
new_gens := List(cf[pos].generators,y->y^x);
h := Group(new_gens);
return RecogniseGroup(h);
return RECOG.TestGroup(h,false,Size(g));
end;;

MakeReadWriteGlobal("NUM_MANDARINS_DEFAULT_VALUE");
NUM_MANDARINS_DEFAULT_VALUE := 0;
ri := testFDPM(88, GF(3), false);
riAlt := testFDPM(88, GF(3), true);
ProfileLineByLine("FDPM-dim-87-gf3-sym-membershiptests-10.gz");
List([1..10], i -> SLPforElement(ri, PseudoRandom(Grp(ri))));
UnprofileLineByLine();
ProfileLineByLine("FDPM-dim-87-gf3-alt-membershiptests-10.gz");
List([1..10], i -> SLPforElement(riAlt, PseudoRandom(Grp(riAlt))));
UnprofileLineByLine();
LoadPackage("profiling");
OutputAnnotatedCodeCoverageFiles("FDPM-dim-87-gf3-sym-membershiptests-10.gz","FDPM-dim-87-gf3-sym-membershiptests-10");
OutputAnnotatedCodeCoverageFiles("FDPM-dim-87-gf3-alt-membershiptests-10.gz","FDPM-dim-87-gf3-alt-membershiptests-10");
