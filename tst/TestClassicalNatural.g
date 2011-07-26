# Classical natural:
# Usage: ReadPackage("recog","tst/TstClassicalNatural.g");
LoadPackage("recog");
#for q in [2,3,4,5,7,8,9,11,13,16,17,25,81,256] do
for q in [16,17,25,81,256] do
  for d in Set([2,3,4,5,6,7,8,9,10,17,18,19,20,29,30,q-1,q,q+1]) do
    if (q > 25 and d >= Maximum(q,10)) or d<=1 then continue; fi;
    if (q = 8 and d = 5) then continue; fi;
    if (q = 2 and d = 7) then continue; fi;
    if (q = 13 and d = 5) then continue; fi;
    if q > 7 and d = 5 then continue; fi;

    h := GL(d,q);
    gens := List([1..10],x->PseudoRandom(h));
    g := GroupWithGenerators(gens);
    Print("Testing GL(",d,",",q,") in its natural representation...\n");
    ri := RECOG.TestGroup(g,false,Size(h));
    r := ri;
    if not(IsLeaf(ri)) then r := RIFac(ri); fi;
    stamp := r!.fhmethsel.successmethod;
    if stamp="ProjDeterminant" then
        r := RIKer(r);
        stamp := r!.fhmethsel.successmethod;
    fi;
    Print("Stamp: ",stamp,"\n\n");
  od;
od;
# Problems:
#  GL(5,8)
#  GL(5,13)
#  GL(2,7) or GL(7,2)?
