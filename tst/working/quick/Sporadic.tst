# test recognition of sporadic groups
# TODO: right now, we only test the first representation stored in AtlasRep;
# ideally, we should test more
gap> TestSporadic := function(name)
>     local g, ri;
>     g := AtlasGenerators(name,1).generators;
>     g := Group(g);
>     ri := EmptyRecognitionInfoRecord(rec(),g,IsMatrixGroup(g));
>     return FindHomMethodsProjective.NameSporadic(ri, g : DEBUGRECOGSPORADICS);
> end;;

#
gap> data := [rec(name := "M23"), rec(name := "Suz"), rec(name := "Fi23")];;
gap> for d in data do
> name := d.name;
> Print(name, "\n");
> TestSporadic(name);
> od;
M23
Suz
Fi23
