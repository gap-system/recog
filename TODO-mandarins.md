## Make clear where things can be improved
- comments and how to reproduce

## TODO
Wenn z.b. in einem Blatt ein SLP berechnet wurde, heißt das in einem inneren
Knoten `node` nicht, dass der input auch element von Grp(node) ist.
Insbesondere müssen wir immer das SLP für ein Mandarin auswerten und checken,
dass der Mandarin rausgekommen ist?

FDPM test:
  Soll ich mal ein profile anlegen wo ich constructive membership test für An
  und Sn vergleiche?
  Ergebnis: ist einfach langsam

There is a regression in bugfix.tst. Clean up and then check again.

    ########> Diff in /home/sergio/projects/pkg/recog/tst/working/slow/bugfix.\
    tst:25
    # Input is:
    for i in [1..50] do
        ri := RECOG.TestGroup(GL(8,27), false, Size(GL(8,27)));
    od;
    # Expected output:
    # But found:
    Immediate verification: found extra kernel element(s)!
    Error, no method found! For debugging hints type ?Recovery from NoMethodFound
    Error, no 1st choice method found for `Length' on 1 arguments
    The 1st argument is 'fail' which might point to an earlier problem

    ########

- also use gens of input group as mandarins

- make ImmVer + send 100 elements
  would this be faster? If so, do a hybrid approach? Namely only work with 10
  or 20 mandarins during recognition, but with 100 once the tree is finished.

- set mandarin info msgs to level 2
- revisit 1c19d12 fine tune imprimitive
- test whether we can make the standard arguments RECOG_FindKernelFastNormalClosureStandardArgumentValues for findgensNmeth smaller and
  get away with it since we use mandarins.

Could it be that immediate verification doesn't do anything once mandarins are
enabled? See logs/\*.logs. With master immediate verification prints "found
extra kernel element".
ImmVer does something when encountering trivial kernels? Double check this and
see if performance deteriorates if we disable that.

gap> SetInfoLevel(InfoRecog, 1);
gap> TestMatDiagonal := function(F, n)
>     local gens, l, i, m, j, g, ri;
>     gens := [];
>     l := ShallowCopy(Elements(F));
>     RemoveSet(l,Zero(F));
>     for i in [1..5] do
>         m := IdentityMat(7,F);
>         for j in [1..7] do
>             m[j,j] := Random(l);
>         od;
>         Add(gens,m);
>     od;
>     g := GroupWithGenerators(gens);
>     return RecogniseGroup(g);
> end;;
gap> while true do TestMatDiagonal(GF(9), 2);; od;

^ there is a call which takes forever when I let it run

Super slow due to crisis:
- MatDiagonal.tst
Slow due to crisis:
- bugfix

## Option to enable/disable mandarins
set num_mands to 0

## Docs:
Differences to magma/CompositionTree:
- We add levels and small/big crises.
- They during a crisis, the generators of the chopped off is doubled.
  Then, they claim that nrGens of a kernel is always at least nrGens of the
  parent assures that all descendants of the new kernel also have a big
  generatings set.
  We also do the former. Instead of doing the latter, 
  

## Kernel-safe methods, deterministicKernelCreation
Let methods say, that they create safe kernels if the current node is safe.
Try this e.g. with "ThrowAwayFixedPoints"


## Performance

Something is weird with the current profiling system. Membership-checking takes
forever for some groups. But profiling shows that the extra time is spent in
the SLP functions. Here we can find difference between membership testing and
mandarins.

    gap-master tst/testall-120-inTests-10-mandarins.g
    gap-master tst/testall-30-inTests-100-mandarins.g


Test performance by manually reducing the arguments for findkernelmeth of
BalTreeForBlocks and Imprimitive? Or maybe even of the whole
`RECOG_Find..StandardArguments`?
- Setting BAL_CONST to 0.1 and running recognition of the wreath product 
      g := WreathProduct(SymmetricGroup(5),SymmetricGroup(32));
  triggers lvl 3 crises and works fine. Time for recognition is roughly 5s with
  no extreme outliers.
  BUT See how this behaves if I only reduce the "conjugations"
  argument for findgensNmeth

When crises are raised very often, that may be a hint, that the kernel
generating size is too small. To an extent, it should be fine to rely on the
mandarins to catch that.

- ce1f513 master
  total    591680 ms (34347 ms GC) and 57.3GB allocated
- 61adc09 but without handling crises and erroring out instead
  total    982249 ms (78561 ms GC) and 88.7GB allocated
- b7c0cf0 Mandarins with SLPs but without checking equality
  total   1043838 ms (84736 ms GC) and 89.6GB allocated
- faf71d4 Mandarins with SLPs
  total   3370850 ms (505873 ms GC) and 153GB allocated
- 65539bf Mandarins without SLPs
  total   2866155 ms (365469 ms GC) and 188GB allocated

## Performance improvements

According to a few profiles I made a lot of time is spent in the GAP library
functions in lib/straight.gi:
- RewriteStraightLineProgram 	
- ResultOfLineOfStraightLineProgram 	
- IntermediateResultsOfSLPWithoutOverwriteInner 
Also, the SLPs seem to use up a lot of storage. That should be reduced by
implementing an SLP data-type on the kernel level.
