#
# HACK to insert the method
gap> AddMethod(FindHomDbPerm, FindHomMethodsGeneric.SnAnSmallUnknownDegree, 58);;
gap> AddMethod(FindHomDbPerm, FindHomMethodsGeneric.SnAnUnknownDegree, 57);;

# For each entry (d, k) we construct Sym(d)/Alt(d) acting on k-sets.
# For each entry (d, k), we must have 2 * k ^ 2 > d,
# otherwise LargeBasePrimitive recognises the group instead of SnAnUnknownDegree.
gap> dataPerm := [[7, 2], [8, 3], [9, 3], [10, 3], [11, 3], [12, 3], [13, 3]];;

#
# PermGroup action on k-sets
gap> PermOnKSets := function(G, k)
>     local sets;
>     sets := Combinations([1 .. NrMovedPoints(G)], k);;
>     return Action(G, sets, OnSets);;
> end;;
gap> AltOnKSets := function(d, k)
>     return PermOnKSets(AlternatingGroup(d), k);
> end;;
gap> SymOnKSets := function(d, k)
>     return PermOnKSets(SymmetricGroup(d), k);
> end;;

#
gap> altPermGroups := List(dataPerm, entry -> AltOnKSets(entry[1], entry[2]));;
gap> symPermGroups := List(dataPerm, entry -> SymOnKSets(entry[1], entry[2]));;

#
gap> dataMat := [[7, 3], [8, 5], [11, 7]];;

#
# Permutation Matrix Group
gap> PermMatGroup := function(G, q) return Group(List(
>     GeneratorsOfGroup(G),
>     x -> ImmutableMatrix(q, PermutationMat(x, NrMovedPoints(G), GF(q)))
> )); end;;
gap> AltMatGroup := function(n, q) return PermMatGroup(AlternatingGroup(n), q);
> end;;
gap> SymMatGroup := function(n, q) return PermMatGroup(SymmetricGroup(n), q);
> end;;

#
gap> altMatGroups := List(dataMat, entry -> AltMatGroup(entry[1], entry[2]));;
gap> symMatGroups := List(dataMat, entry -> SymMatGroup(entry[1], entry[2]));;

#
gap> nonAltOrSymGroups := [
>     PSL(3, 5),
>     SL(3, 5),
> ];;

# Test
gap> for i in [1 .. Length(dataPerm)] do
>     RECOG.TestGroup(altPermGroups[i], false, Factorial(dataPerm[i, 1])/2, rec());
>     RECOG.TestGroup(symPermGroups[i], false, Factorial(dataPerm[i, 1]), rec());
> od;
gap> for i in [1 .. Length(dataMat)] do
>     RECOG.TestGroup(altMatGroups[i], false, Factorial(dataMat[i, 1])/2, rec());
>     RECOG.TestGroup(symMatGroups[i], false, Factorial(dataMat[i, 1]), rec());
> od;
gap> for i in [1 .. Length(nonAltOrSymGroups)] do
>     ri := RecogNode(nonAltOrSymGroups[i]);
>     if FindHomMethodsGeneric.SnAnUnknownDegree(ri, nonAltOrSymGroups[i]) = Success then
>         Print("ERROR: Recognised group [", i, "] wrongly as Sn/An!\n");
>     fi;
> od;

#
# Remove Hacky injection of our method
gap> for db in [FindHomDbPerm] do
>       Remove(db,
>              PositionProperty(db, x -> Stamp(x.method) = "SnAnSmallUnknownDegree"));;
>       Remove(db,
>              PositionProperty(db, x -> Stamp(x.method) = "SnAnUnknownDegree"));;
> od;
