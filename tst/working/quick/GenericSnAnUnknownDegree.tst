#@local d, sets, SdOn2Sets, ri, success, x, slp, db
#
# HACK to insert the method
gap> AddMethod(FindHomDbPerm, FindHomMethodsGeneric.SnAnUnknownDegree, 58);;
gap> AddMethod(FindHomDbMatrix, FindHomMethodsGeneric.SnAnUnknownDegree, 1070);;
gap> AddMethod(FindHomDbProjective, FindHomMethodsGeneric.SnAnUnknownDegree, 1220);;

# For each entry (d, k) we construct Sym(d)/Alt(d) acting on k-sets.
# For each entry (d, k), we must have 2 * k ^ 2 > d,
# otherwise LargeBasePrimitive recognises the group instead of SnAnUnknownDegree.
gap> data := [[7, 2], [8, 3], [9, 3], [10, 3], [11, 3], [12, 3], [13, 3]];;

# TODO: make sure we really use everything
# SymmetricGroup action on k-sets
gap> SymOnKSets := function(d, k)
>     local sets;
>     sets := Combinations([1 .. d], k);;
>     return Action(SymmetricGroup(d), sets, OnSets);;
> end;;

#
# AlternatingGroup action on 2-sets
gap> AltOnKSets := function(d, k)
>     local sets;
>     sets := Combinations([1 .. d], k);;
>     return Action(AlternatingGroup(d), sets, OnSets);;
> end;;

#
gap> altGroups := List(data, entry -> AltOnKSets(entry[1], entry[2]));;
gap> symGroups := List(data, entry -> SymOnKSets(entry[1], entry[2]));;
gap> permMatGroup := function(G, q) return Group(List(
>     GeneratorsOfGroup(G),
>     x -> ImmutableMatrix(q, PermutationMat(x, NrMovedPoints(G), GF(q)))
> )); end;;
gap> altMatGroups := [
>     permMatGroup(AlternatingGroup(11), 7),
>     #permMatGroup(AlternatingGroup(5), 7^3),
> ];;
gap> nonAltOrSymGroups := [
>     DihedralGroup(IsPermGroup, 10),
>     #DihedralGroup(IsPcGroup, 10),
>     #DihedralGroup(IsPermGroup, 2000),
>     #DihedralGroup(IsPcGroup, 2000),
>     PSL(3, 5),
>     SL(3, 5),
>     Omega(-1, 4, 5),
>     Omega(-1, 4, 3),
>     Omega(+1, 4, 5),
>     Omega(+1, 4, 3),
>     Omega(+1, 8, 5),
>     Omega(+1, 8, 3),
>     Omega(0, 5, 5),
>     Omega(0, 5, 3),
> ];;

# Test
gap> for i in [1 .. Length(data)] do
>     RECOG.TestGroup(altGroups[i], false, Factorial(data[i, 1])/2, rec(), "SnAnUnknownDegree");
>     RECOG.TestGroup(symGroups[i], false, Factorial(data[i, 1]), rec(), "SnAnUnknownDegree");
> od;
gap> for i in [1 .. Length(altMatGroups)] do
>     RECOG.TestGroup(altMatGroups[i], false, Size(altMatGroups[i]));
> od;
gap> for i in [1 .. Length(altMatGroups)] do
>     RECOG.TestGroup(altMatGroups[i], true, Size(altMatGroups[i]));
> od;
gap> for i in [1 .. Length(nonAltOrSymGroups)] do
>     if FindHomMethodsGeneric.SnAnUnknownDegree(RecogNode(nonAltOrSymGroups[i]), nonAltOrSymGroups[i]) = Success then
>         Print("ERROR: Recognised group [", i, "] wrongly as Sn/An!\n");
>     fi;
> od;

# FindHomMethodsGeneric.SnAnUnknownDegree
# Sn
gap> for d in [11] do
> sets := Combinations([1 .. d], 2);;
> SdOn2Sets := Action(SymmetricGroup(d), sets, OnSets);;
> ri := RecogNode(SdOn2Sets);;
> success := FindHomMethodsGeneric.SnAnUnknownDegree(ri, SdOn2Sets);
> if not success or not Size(ri) = Factorial(d) then
>   Print("wrong result! degree ", d, "\n");
> fi;
> od;

# An
gap> for d in [11] do
> sets := Combinations([1 .. d], 2);;
> SdOn2Sets := Action(AlternatingGroup(d), sets, OnSets);;
> ri := RecogNode(SdOn2Sets);;
> success := FindHomMethodsGeneric.SnAnUnknownDegree(ri, SdOn2Sets);
> if not success or not Size(ri) = Factorial(d)/2 then
>   Print("wrong result! degree ", d, "\n");
> fi;
> od;

# Check Slp function
gap> ri := RecogNode(SdOn2Sets);;
gap> FindHomMethodsGeneric.SnAnUnknownDegree(ri, SdOn2Sets);
true
gap> x := PseudoRandom(Grp(ri));;
gap> slp := SLPforElement(ri, x);;
gap> x = ResultOfStraightLineProgram(slp, NiceGens(ri));
true

#
# Remove Hacky injection of our method
gap> for db in [FindHomDbPerm, FindHomDbMatrix, FindHomDbProjective] do
>       Remove(db,
>              PositionProperty(db, x -> Stamp(x.method) = "SnAnUnknownDegree"));;
> od;
