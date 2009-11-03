#############################################################################
##
##  almostsimple.gi        
##                                recog package                   
##                                                        Max Neunhoeffer
##                                                            Ákos Seress
##
##  Copyright 2006-2009 by the authors.
##  This file is free software, see license information at the end.
##
##  Code to recognise (simple) groups by their two largest element orders.
##  At least recognise the "natural" characteristic.
##
#############################################################################

RECOG.ParseNumber := function( number, d, default )
  if IsInt(number) then 
      return number; 
  fi;
  if IsString(number) then
      if number = "logd" then return LogInt(d,2); fi;
      if number[Length(number)] = 'd' then
          return d * Int(number{[1..Length(number)-1]});
      fi;
  fi;
  return default;
end;

RECOG.MakeStabChainHint := function( chain, stdgens )
  local b,bb,choice,dims,f,gens,grpnum,grps,i,j,lens,llens,m,name,names,nams,nrs,o,orblens,pts,r,size,slps;
  f := FieldOfMatrixList(stdgens);
  name := chain[1].name;
  size := chain[1].order;
  slps := [];
  names := [];
  dims := [];
  orblens := [];
  pts := [];
  gens := stdgens;
  repeat
      Print("Working on ",name,"\n");
      grps := [];
      nams := [];
      nrs := [];
      for i in [1..Length(chain)] do
          r := chain[i];
          if IsBound(r.parent) and r.parent = name then
              Add(grps,ResultOfStraightLineProgram(r.generators,gens));
              Add(nams,r.name);
              Add(nrs,i);
          fi;
      od;
      if Length(grps) = 0 then break; fi;
      Print("Considering subgroups: ",nams,"\n");
      bb := [];
      llens := [];
      grpnum := [];
      for i in [1..Length(grps)] do
          # will be left by break in case of success
          Print("  Considering ",nams[i],"\n");
          m := GModuleByMats(grps[i],f);
          if not MTX.IsIrreducible(m) then
              b := List(MTX.BasesMinimalSubmodules(m),MutableCopyMat);
              Sort(b,function(a,b) return Length(a) < Length(b); end );
              Print("    Dimensions: ",List(b,Length),"\n");
              lens := [];
              for j in [1..Length(b)] do
                  TriangulizeMat(b[j]);
                  if Length(b[j]) = 1 then
                      o := Orb(gens,b[j][1],OnLines,rec( report := 10000,
                             treehashsize := 1000, storenumbers := true ));
                  else
                      o := Orb(gens,b[j],OnSubspacesByCanonicalBasis,
                         rec( report := 10000, treehashsize := 1000, 
                              storenumbers := true ));
                  fi;
                  Enumerate(o);
                  Print("    Found orbit of length ",Length(o),"\n");
                  lens[j] := Length(o);
              od;
              Append(bb,b);
              Append(llens,lens);
              Append(grpnum,ListWithIdenticalEntries(Length(b),i));
          else
              Print("    Restriction is irreducible!\n");
          fi;
      od;
      choice := 1;
      Print("Dimensions: ",List(bb,Length),"\n");
      Print("Orbit lengths: ",llens,"\n");
      Error("now decide which orbit to take, set choice");
      if choice > 0 then
          i := grpnum[choice];
          Add(names,nams[i]);
          Add(dims,Length(bb[choice]));
          name := nams[i];
          gens := grps[i];
          size := size / llens[choice];
          Add(orblens,llens[choice]);
          Add(slps,chain[nrs[i]].generators);
          Add(pts,bb[choice]);
      fi;
  until size = 1 or choice = 0;
  return rec( slps := slps, names := names, dims := dims, orblens := orblens,
              pts := pts );
end;

InstallGlobalFunction( DoHintedStabChain, function(ri,G,hint)
    local S,b,bra,c,cf,elm,finder,fu,gm,homs,m,max,maxes,maxgens,opt,s,stdgens;
    finder := AtlasProgram(hint.name,"find");
    if finder = fail then
        Info(InfoRecog,1,"Expected BBox finder for stdgens of ",hint.name,
             " not availabe!");
        Info(InfoRecog,1,"Check your AtlasRep installation!");
        return fail;
    fi;
    gm := Group(ri!.gensHmem);
    gm!.pseudorandomfunc := [rec( 
       func := function(ri) return RandomElm(ri,"StdGens",true).el; end,
       args := [ri])];
    Info(InfoRecog,2,"Finding standard generators with bbox program...");
    stdgens := RunBBoxProgram(finder.program,gm,ri!.gensHmem,
                              rec( orderfunction := RECOG.ProjectiveOrder ) );
    if stdgens = fail or stdgens = "timeout" then
        Info(InfoRecog,2,"Stdgens finder did not succeed for ",hint.name);
        return fail;
    fi;
    stdgens := stdgens.gens;
    Setslptostd(ri,SLPOfElms(stdgens));
    Setstdgens(ri,StripMemory(stdgens));
    if IsBound(hint.usemax) then
        if IsBound(hint.brauercharelm) then
            elm := ResultOfStraightLineProgram(hint.brauercharelm,stdgens);
            bra := BrauerCharacterValue(elm!.el);
            maxes := hint.usemax{Filtered([1..Length(hint.usemax)],
                                          i->hint.brauercharvals[i] = bra)};
        else
            maxes := hint.usemax;
        fi;
        for max in maxes do
            s := AtlasProgram(hint.name,max);
            if s = fail then
                Info(InfoRecog,1,"Expected maximal subgroup slp of ",hint.name,
                     " not available!");
                Info(InfoRecog,1,"Check your AtlasRep installation!");
                return fail;
            fi;
            maxgens := ResultOfStraightLineProgram(s.program,
                                                   StripMemory(stdgens));
            m := GModuleByMats(maxgens,ri!.field);
            if MTX.IsIrreducible(m) then
                Info(InfoRecog,2,"Found irreducible submodule!");
                continue;
            fi;
            cf := List(MTX.CollectedFactors(m),x->x[1]);
            Sort(cf,function(a,b) return a.dimension < b.dimension; end);
            for c in cf do
                homs := MTX.Homomorphisms(c,m);
                if Length(homs) > 0 then
                    ConvertToMatrixRep(homs[1],ri!.field);
                    b := MutableCopyMat(homs[1]);
                    break;
                fi;
                # Some must be in the socle, so this terminates with break!
            od;
            TriangulizeMat(b);
            fu := function() return RandomElm(ri,"StabChain",true).el; end;
            opt := rec( Projective := true, RandomElmFunc := fu );
            if Length(b) = 1 then
                opt.Cand := rec( points := [b[1]], ops := [OnLines] );
            else
                opt.Cand := rec( points := [b], 
                                 ops := [OnSubspacesByCanonicalBasis] );
            fi;
            gm := GroupWithGenerators(stdgens);
            opt.Size := hint.size;
            Info(InfoRecog,2,"Computing hinted stabilizer chain for ",
                 hint.name," ...");
            S := StabilizerChain(gm,opt);
            # Verify correctness by sifting original gens:
            # ...
            ri!.stabilizerchain := S;
            Setslptonice(ri,SLPOfElms(StrongGenerators(S)));
            SetSize(ri,hint.size);
            ForgetMemory(S);
            Unbind(S!.opt.RandomElmFunc);
            Setslpforelement(ri,SLPforElementFuncsProjective.StabilizerChain);
            SetFilterObj(ri,IsLeaf);
            ri!.comment := Concatenation("_",hint.name);
            return true;
        od;
    fi;
    Info( InfoRecog, 2, "Got stab chain hint, not yet implemented!" );
    return fail;
  end );

InstallGlobalFunction( DoHintedLowIndex, function(ri,G,hint)
  local bas,d,fld,gens,hm,hom,i,numberrandgens,orb,orblenlimit,s,
        tries,triesinner,triesinnerlimit,trieslimit,x,y;

  Info(InfoRecog,2,"Got hint for group, trying LowIndex...");

  fld := ri!.field;
  d := ri!.dimension;
  if IsBound(hint.elordersstart) then
      repeat
          x := PseudoRandom(G);
      until Order(x) in hint.elordersstart;
      x := [x];
  else
      x := [];
  fi;

  tries := 0;
  numberrandgens := RECOG.ParseNumber(hint.numberrandgens,d,2);
  triesinnerlimit := RECOG.ParseNumber(hint.triesforgens,d,"1d");
  trieslimit := RECOG.ParseNumber(hint.tries,d,10);
  orblenlimit := RECOG.ParseNumber(hint.orblenlimit,d,"4d");
  Info(InfoRecog,3,"Using numberrandgens=",numberrandgens,
       " triesinnerlimit=",triesinnerlimit," trieslimit=",trieslimit,
       " orblenlimit=",orblenlimit);
  
  repeat
      gens := ShallowCopy(x);
      triesinner := 0;
      if numberrandgens = Length(gens) then   # we have to make the hm module
          hm := GModuleByMats(gens,fld);
          if MTX.IsIrreducible(hm) then
              tries := tries + 1;
              continue;
          fi;
      else
          while Length(gens) < numberrandgens and 
                triesinner < triesinnerlimit do
              y := PseudoRandom(G);
              Add(gens,y);
              triesinner := triesinner + 1;
              hm := GModuleByMats(gens,fld);
              if MTX.IsIrreducible(hm) then
                  Unbind(gens[Length(gens)]);
              fi;
          od;
      fi;
      if Length(gens) = numberrandgens then
          # We hope to have the maximal subgroup!
          bas := [MTX.ProperSubmoduleBasis(hm)];
          s := bas[1];
          while s <> fail do
              hm := MTX.InducedActionSubmodule(hm,s);
              s := MTX.ProperSubmoduleBasis(hm);
              Add(bas,s);
          od;
          Unbind(bas[Length(bas)]);
          s := bas[Length(bas)];
          for i in [Length(bas)-1,Length(bas)-2..1] do
              s := s * bas[i];
          od;
          # Now s is the basis of a minimal submodule, permute that:
          s := MutableCopyMat(s);
          TriangulizeMat(s);
          # FIXME: this will be unnecessary:
          ConvertToMatrixRep(s);
          Info(InfoRecog,2,"Found invariant subspace of dimension ",
               Length(s),", enumerating orbit...");
          if not IsBound(hint.subspacedims) or 
             Length(s) in hint.subspacedims then
              #orb := RECOG.OrbitSubspaceWithLimit(G,s,orblenlimit);
              orb := Orb(G,s,OnSubspacesByCanonicalBasis,
                         rec(storenumbers := true, 
                             hashlen := NextPrimeInt(2*orblenlimit)));
              Enumerate(orb,orblenlimit);
              if IsClosed(orb) then
                  hom := OrbActionHomomorphism(G,orb);
                  if Length(s) * Length(orb) = d then
                      # A block system!
                      forkernel(ri).t := Concatenation(orb);
                      forkernel(ri).blocksize := Length(s);
                      Add(forkernel(ri).hints,
                  rec(method:=FindHomMethodsProjective.DoBaseChangeForBlocks, 
                            rank := 2000, stamp := "DoBaseChangeForBlocks"),1);
                      Setimmediateverification(ri,true);
                      findgensNmeth(ri).args[1] := Length(orb)+3;
                      findgensNmeth(ri).args[2] := 5;
                      Info(InfoRecog,2,"Found block system with ",
                           Length(orb)," blocks.");
                  else
                      Info(InfoRecog,2,"Found orbit of length ",
                           Length(orb)," - not a block system.");
                  fi;
                  Sethomom(ri,hom);
                  Setmethodsforfactor(ri,FindHomDbPerm);
                  return true;
              fi;
          else
              Info(InfoRecog,2,"Subspace dimension not as expected, ",
                   "not enumerating orbit.");
          fi;
      fi;
      tries := tries + 1;
  until tries > trieslimit;
  return fail;
end );
  
# We start a database of hints, whenever we discover a certain group, we
# can ask this database what to do:

RECOG.AlmostSimpleHints := rec();

InstallGlobalFunction( InstallAlmostSimpleHint,
  function( name, type, re )
    if not(IsBound(RECOG.AlmostSimpleHints.(name))) then
        RECOG.AlmostSimpleHints.(name) := [];
    fi;
    re.type := type;
    Add( RECOG.AlmostSimpleHints.(name),re );
  end );

RECOG.ProduceTrivialStabChainHint := function(name,reps,maxes)
  local bad,f,g,gens,hint,list,m,o,prevdim,prevfield,r,range,res,ri,
        size,success,t,values,x;
  PrintTo(Concatenation("NEWHINTS.",name),"# Hints for ",name,":\n");
  prevdim := fail;
  prevfield := fail;
  for r in reps do
      Print("\nDoing representation #",r,"\n");
      gens := AtlasGenerators(name,r);
      g := Group(gens.generators);
      f := gens.ring;
      values := [];
      success := false;
      size := Size(CharacterTable(name));
      for m in [1..Length(maxes)] do
          Print("Doing maximal subgroup #",m,"\n");
          hint := rec( name := name, size := size, usemax := [m] );
          ri := EmptyRecognitionInfoRecord(rec(),g,true);
          t := Runtime();
          res := DoHintedStabChain(ri,g,hint);
          t := Runtime() - t;
          if res = true then
              o := ri!.stabilizerchain!.orb;
              x := o[1];
              if IsMatrix(x) then
                  Add(values,[Length(x)*QuoInt(Length(o)+99,100),Length(o)]);
              else
                  Add(values,[QuoInt(Length(o)+99,100),Length(o)]);
              fi;
              Print("value=",values[Length(values)]," time=",t," orblen=",
                    Length(o)," subspace=");
              ViewObj(x);
              Print("\n");
              success := true;
          else
              Add(values,[infinity,infinity]);
              Print("failure\n");
          fi;
      od;
      if success then
          if Size(f) = prevfield and Length(gens.generators[1]) = prevdim then
              AppendTo(Concatenation("NEWHINTS.",name),
                       ">>>SAME FIELD AND DIM\n");
          fi;
          list := ShallowCopy(maxes);
          SortParallel(values,list);
          bad := First([1..Length(values)],i->values[i][1] = infinity);
          if bad = fail or bad > 3 then
              if Length(values) > 3 then
                  range := [1..3];
              else
                  range := [1..Length(values)];
              fi;
          else
              range := [1..bad-1];
          fi;
          AppendTo(Concatenation("NEWHINTS.",name),
                "InstallAlmostSimpleHint( \"",name,"\", \"StabChainHint\",\n",
                "  rec( name := \"",name,"\", fields := [",
                Size(f),"], dimensions := [",Length(gens.generators[1]),
                "], \n       usemax := ",list{range},
                ", \n       size := ", size, 
                ", atlasrepnrs := [",r,"], \n       values := ",
                values{range},"\n  ));\n");
      fi;
      prevfield := Size(f);
      prevdim := Length(gens.generators[1]);
  od;
end;

RECOG.DistinguishAtlasReps := function(name,rep1,rep2)
  local br1,br2,classes,gens1,gens2,guck1,guck2,l,lens,slps;
  classes := AtlasProgram(name,"cyclic").program;
  gens1 := GeneratorsWithMemory(AtlasGenerators(name,rep1).generators);
  gens2 := AtlasGenerators(name,rep2).generators;
  guck1 := ResultOfStraightLineProgram(classes,gens1);
  guck2 := ResultOfStraightLineProgram(classes,gens2);
  br1 := List(guck1,x->BrauerCharacterValue(x!.el));
  br2 := List(guck2,BrauerCharacterValue);
  l := Filtered([1..Length(br1)],i->br1[i]<>br2[i]);
  slps := List(guck1,SLPOfElm);
  lens := List(l,x->Length(LinesOfStraightLineProgram(slps[x])));
  SortParallel(lens,l);
  Print("brauercharelm := ",slps[l[1]],", brauercharvals := ",
        [br1[l[1]],br2[l[1]]],",\n");
end;


# Hints for M11:
InstallAlmostSimpleHint( "M11", "StabChainHint",
  rec( name := "M11", fields := [2], dimensions := [10], 
       usemax := [ 1, 3, 4 ], 
       size := 7920, atlasrepnrs := [6], 
       values := [ [ 1, 11 ], [ 1, 55 ], [ 1, 66 ] ]
  ));
InstallAlmostSimpleHint( "M11", "StabChainHint",
  rec( name := "M11", fields := [2], dimensions := [32], 
       usemax := [ 4, 5, 3 ], 
       size := 7920, atlasrepnrs := [7], 
       values := [ [ 4, 66 ], [ 4, 165 ], [ 8, 55 ] ]
  ));
InstallAlmostSimpleHint( "M11", "StabChainHint",
  rec( name := "M11", fields := [2], dimensions := [44], 
       usemax := [ 3, 4, 5 ], 
       size := 7920, atlasrepnrs := [8], 
       values := [ [ 1, 55 ], [ 1, 66 ], [ 2, 165 ] ]
  ));
InstallAlmostSimpleHint( "M11", "StabChainHint",
  rec( name := "M11", fields := [3], dimensions := [5], 
       usemax := [ 3, 1, 4 ], 
       size := 7920, atlasrepnrs := [9,10], 
  ));
InstallAlmostSimpleHint( "M11", "StabChainHint",
  rec( name := "M11", fields := [3], dimensions := [10], 
       usemax := [ 3 ], 
       size := 7920, atlasrepnrs := [11,12,13], 
  ));
InstallAlmostSimpleHint( "M11", "StabChainHint",
  rec( name := "M11", fields := [3], dimensions := [24], 
       usemax := [ 3, 5, 1 ], 
       size := 7920, atlasrepnrs := [14], 
       values := [ [ 2, 55 ], [ 2, 165 ], [ 4, 11 ] ]
  ));
InstallAlmostSimpleHint( "M11", "StabChainHint",
  rec( name := "M11", fields := [3], dimensions := [45], 
       usemax := [ 3, 5, 4 ], 
       size := 7920, atlasrepnrs := [15], 
       values := [ [ 1, 55 ], [ 2, 165 ], [ 4, 66 ] ]
  ));
InstallAlmostSimpleHint( "M11", "StabChainHint",
  rec( name := "M11", fields := [4], dimensions := [16], 
       usemax := [ 4, 5, 2 ], 
       size := 7920, atlasrepnrs := [16,17], 
       values := [ [ 4, 66 ], [ 4, 165 ], [ 5, 12 ] ]
  ));
InstallAlmostSimpleHint( "M11", "StabChainHint",
  rec( name := "M11", fields := [5], dimensions := [10], 
       usemax := [ 1, 3, 4 ], 
       size := 7920, atlasrepnrs := [18], 
       values := [ [ 1, 11 ], [ 1, 55 ], [ 1, 66 ] ]
  ));
InstallAlmostSimpleHint( "M11", "StabChainHint",
  rec( name := "M11", fields := [5], dimensions := [11], 
       usemax := [ 1, 2, 3 ], 
       size := 7920, atlasrepnrs := [19], 
       values := [ [ 1, 11 ], [ 1, 12 ], [ 1, 55 ] ]
  ));
InstallAlmostSimpleHint( "M11", "StabChainHint",
  rec( name := "M11", fields := [5], dimensions := [16], 
       usemax := [ 4, 5, 2 ], 
       size := 7920, atlasrepnrs := [20,21], 
       values := [ [ 3, 66 ], [ 4, 165 ], [ 5, 12 ] ]
  ));
InstallAlmostSimpleHint( "M11", "StabChainHint",
  rec( name := "M11", fields := [5], dimensions := [20], 
       usemax := [ 5, 4, 3 ], 
       size := 7920, atlasrepnrs := [22], 
       values := [ [ 2, 165 ], [ 3, 66 ], [ 4, 55 ] ]
  ));
InstallAlmostSimpleHint( "M11", "StabChainHint",
  rec( name := "M11", fields := [5], dimensions := [45], 
       usemax := [ 3, 5, 4 ], 
       size := 7920, atlasrepnrs := [23], 
       values := [ [ 1, 55 ], [ 2, 165 ], [ 3, 66 ] ]
  ));
InstallAlmostSimpleHint( "M11", "StabChainHint",
  rec( name := "M11", fields := [5], dimensions := [55], 
       usemax := [ 3, 4, 5 ], 
       size := 7920, atlasrepnrs := [24], 
       values := [ [ 1, 55 ], [ 1, 66 ], [ 2, 165 ] ]
  ));
InstallAlmostSimpleHint( "M11", "StabChainHint",
  rec( name := "M11", fields := [11], dimensions := [9], 
       usemax := [ 3, 4, 5 ], 
       size := 7920, atlasrepnrs := [25], 
       values := [ [ 1, 55 ], [ 4, 66 ], [ 4, 165 ] ]
  ));
InstallAlmostSimpleHint( "M11", "StabChainHint",
  rec( name := "M11", fields := [11], dimensions := [10], 
       usemax := [ 3, 5 ], 
       size := 7920, atlasrepnrs := [26,27], 
  ));
InstallAlmostSimpleHint( "M11", "StabChainHint",
  rec( name := "M11", fields := [11], dimensions := [11], 
       usemax := [ 1, 2, 3 ], 
       size := 7920, atlasrepnrs := [28], 
       values := [ [ 1, 11 ], [ 1, 12 ], [ 1, 55 ] ]
  ));
InstallAlmostSimpleHint( "M11", "StabChainHint",
  rec( name := "M11", fields := [11], dimensions := [16], 
       usemax := [ 5, 2, 4 ], 
       size := 7920, atlasrepnrs := [29], 
       values := [ [ 4, 165 ], [ 5, 12 ], [ 5, 66 ] ]
  ));
InstallAlmostSimpleHint( "M11", "StabChainHint",
  rec( name := "M11", fields := [11], dimensions := [44], 
       usemax := [ 3, 4, 5 ], 
       size := 7920, atlasrepnrs := [30], 
       values := [ [ 1, 55 ], [ 1, 66 ], [ 2, 165 ] ]
  ));
InstallAlmostSimpleHint( "M11", "StabChainHint",
  rec( name := "M11", fields := [11], dimensions := [55], 
       usemax := [ 3, 4, 5 ], 
       size := 7920, atlasrepnrs := [31], 
       values := [ [ 1, 55 ], [ 1, 66 ], [ 2, 165 ] ]
  ));
InstallAlmostSimpleHint( "M11", "StabChainHint",
  rec( name := "M11", fields := [25], dimensions := [10], 
       usemax := [ 3, 5, 4 ], 
       size := 7920, atlasrepnrs := [32,33], 
       values := [ [ 2, 55 ], [ 2, 165 ], [ 3, 66 ] ]
  ));

# Hints for M12:
InstallAlmostSimpleHint( "M12", "StabChainHint",
  rec( name := "M12", fields := [2], dimensions := [10], 
       usemax := [ 3, 4, 8 ], 
       size := 95040, atlasrepnrs := [5], 
       values := [ [ 1, 66 ], [ 1, 66 ], [ 4, 396 ] ]
  ));
InstallAlmostSimpleHint( "M12", "StabChainHint",
  rec( name := "M12", fields := [2], dimensions := [44], 
       usemax := [ 6, 7, 8 ], 
       size := 95040, atlasrepnrs := [6], 
       values := [ [ 3, 220 ], [ 3, 220 ], [ 4, 396 ] ]
  ));
InstallAlmostSimpleHint( "M12", "StabChainHint",
  rec( name := "M12", fields := [2], dimensions := [144], 
       usemax := [ 8, 9, 10 ], 
       size := 95040, atlasrepnrs := [7], 
       values := [ [ 4, 396 ], [ 5, 495 ], [ 5, 495 ] ]
  ));
InstallAlmostSimpleHint( "M12", "StabChainHint",
  rec( name := "M12", fields := [3], dimensions := [10], 
       usemax := [ 3, 4, 6 ], 
       size := 95040, atlasrepnrs := [8], 
       values := [ [ 1, 66 ], [ 1, 66 ], [ 3, 220 ] ]
  ));
InstallAlmostSimpleHint( "M12", "StabChainHint",
  rec( name := "M12", fields := [3], dimensions := [15], 
       usemax := [ 3, 2, 9 ], 
       size := 95040, atlasrepnrs := [9], 
       values := [ [ 1, 66 ], [ 5, 12 ], [ 5, 495 ] ]
  ));
InstallAlmostSimpleHint( "M12", "StabChainHint",
  rec( name := "M12", fields := [3], dimensions := [34], 
       usemax := [ 8, 1, 2 ], 
       size := 95040, atlasrepnrs := [10], 
       values := [ [ 4, 396 ], [ 5, 12 ], [ 5, 12 ] ]
  ));
InstallAlmostSimpleHint( "M12", "StabChainHint",
  rec( name := "M12", fields := [3], dimensions := [45], 
       usemax := [ 5, 10 ], 
       size := 95040, atlasrepnrs := [11,12], 
       brauercharelm := StraightLineProgram( [ [ 1, 1, 2, 1 ], [ 3, 1, 2, 1 ], 
         [ 3, 1, 4, 1 ], [ 3, 1, 5, 1 ], [ 3, 1, 6, 1 ], [ 7, 1, 4, 1 ] ], 2 ), 
       brauercharvals := [ 0, 2 ],
  ));
InstallAlmostSimpleHint( "M12", "StabChainHint",
  rec( name := "M12", fields := [3], dimensions := [54], 
       usemax := [ 3, 4, 6 ], 
       size := 95040, atlasrepnrs := [13], 
       values := [ [ 1, 66 ], [ 1, 66 ], [ 3, 220 ] ]
  ));
InstallAlmostSimpleHint( "M12", "StabChainHint",
  rec( name := "M12", fields := [3], dimensions := [99], 
       usemax := [ 6, 7, 8 ], 
       size := 95040, atlasrepnrs := [14], 
       values := [ [ 3, 220 ], [ 3, 220 ], [ 4, 396 ] ]
  ));
InstallAlmostSimpleHint( "M12", "StabChainHint",
  rec( name := "M12", fields := [4], dimensions := [16], 
       usemax := [ 5, 8, 10 ], 
       size := 95040, atlasrepnrs := [15,16], 
       values := [ [ 2, 144 ], [ 4, 396 ], [ 5, 495 ] ]
  ));
InstallAlmostSimpleHint( "M12", "StabChainHint",
  rec( name := "M12", fields := [5], dimensions := [11], 
       usemax := [ 1, 2, 3 ], 
       size := 95040, atlasrepnrs := [17], 
       values := [ [ 1, 12 ], [ 1, 12 ], [ 1, 66 ] ]
  ));
InstallAlmostSimpleHint( "M12", "StabChainHint",
  rec( name := "M12", fields := [5], dimensions := [16], 
       usemax := [ 5, 8, 10 ], 
       size := 95040, atlasrepnrs := [18], 
       values := [ [ 2, 144 ], [ 4, 396 ], [ 5, 495 ] ]
  ));
InstallAlmostSimpleHint( "M12", "StabChainHint",
  rec( name := "M12", fields := [5], dimensions := [45], 
       usemax := [ 5, 6, 7 ], 
       size := 95040, atlasrepnrs := [19], 
       values := [ [ 2, 144 ], [ 3, 220 ], [ 3, 220 ] ]
  ));
InstallAlmostSimpleHint( "M12", "StabChainHint",
  rec( name := "M12", fields := [5], dimensions := [55], 
       usemax := [ 3, 4 ], 
       size := 95040, atlasrepnrs := [20,21], 
       values := [ [ 1, 66 ], [ 1, 66 ] ]
  ));
InstallAlmostSimpleHint( "M12", "StabChainHint",
  rec( name := "M12", fields := [5], dimensions := [66], 
       usemax := [ 3, 4, 5 ], 
       size := 95040, atlasrepnrs := [22], 
       values := [ [ 1, 66 ], [ 1, 66 ], [ 2, 144 ] ]
  ));
InstallAlmostSimpleHint( "M12", "StabChainHint",
  rec( name := "M12", fields := [5], dimensions := [78], 
       usemax := [ 6, 7, 3 ], 
       size := 95040, atlasrepnrs := [23], 
       values := [ [ 6, 220 ], [ 6, 220 ], [ 8, 66 ] ]
  ));
InstallAlmostSimpleHint( "M12", "StabChainHint",
  rec( name := "M12", fields := [5], dimensions := [98], 
       usemax := [ 8, 10, 3 ], 
       size := 95040, atlasrepnrs := [24], 
       values := [ [ 4, 396 ], [ 5, 495 ], [ 8, 66 ] ]
  ));
InstallAlmostSimpleHint( "M12", "StabChainHint",
  rec( name := "M12", fields := [5], dimensions := [120], 
       usemax := [ 6, 7, 9 ], 
       size := 95040, atlasrepnrs := [25], 
       values := [ [ 3, 220 ], [ 3, 220 ], [ 5, 495 ] ]
  ));
InstallAlmostSimpleHint( "M12", "StabChainHint",
  rec( name := "M12", fields := [11], dimensions := [11], 
       usemax := [ 2, 3, 4 ], 
       size := 95040, atlasrepnrs := [26], 
       values := [ [ 1, 12 ], [ 1, 66 ], [ 1, 66 ] ]
  ));
InstallAlmostSimpleHint( "M12", "StabChainHint",
  rec( name := "M12", fields := [11], dimensions := [16], 
       usemax := [ 5, 8, 10 ], 
       size := 95040, atlasrepnrs := [27], 
       values := [ [ 2, 144 ], [ 4, 396 ], [ 5, 495 ] ]
  ));
InstallAlmostSimpleHint( "M12", "StabChainHint",
  rec( name := "M12", fields := [11], dimensions := [29], 
       usemax := [ 6, 7, 9 ], 
       size := 95040, atlasrepnrs := [28], 
       values := [ [ 3, 220 ], [ 3, 220 ], [ 5, 495 ] ]
  ));
InstallAlmostSimpleHint( "M12", "StabChainHint",
  rec( name := "M12", fields := [11], dimensions := [53], 
       usemax := [ 8, 9, 10 ], 
       size := 95040, atlasrepnrs := [29], 
       values := [ [ 4, 396 ], [ 5, 495 ], [ 5, 495 ] ]
  ));
InstallAlmostSimpleHint( "M12", "StabChainHint",
  rec( name := "M12", fields := [11], dimensions := [55], 
       usemax := [ 3, 4, 6 ], 
       size := 95040, atlasrepnrs := [30,31], 
       values := [ [ 1, 66 ], [ 1, 66 ], [ 3, 220 ] ]
  ));
InstallAlmostSimpleHint( "M12", "StabChainHint",
  rec( name := "M12", fields := [11], dimensions := [66], 
       usemax := [ 3, 4, 5 ], 
       size := 95040, atlasrepnrs := [32], 
       values := [ [ 1, 66 ], [ 1, 66 ], [ 2, 144 ] ]
  ));
InstallAlmostSimpleHint( "M12", "StabChainHint",
  rec( name := "M12", fields := [11], dimensions := [91], 
       usemax := [ 9, 5, 6 ], 
       size := 95040, atlasrepnrs := [33], 
       values := [ [ 5, 495 ], [ 6, 144 ], [ 6, 220 ] ]
  ));
InstallAlmostSimpleHint( "M12", "StabChainHint",
  rec( name := "M12", fields := [11], dimensions := [99], 
       usemax := [ 6, 7, 8 ], 
       size := 95040, atlasrepnrs := [34], 
       values := [ [ 3, 220 ], [ 3, 220 ], [ 4, 396 ] ]
  ));
InstallAlmostSimpleHint( "M12", "StabChainHint",
  rec( name := "M12", fields := [11], dimensions := [176], 
       usemax := [ 8, 10, 5 ], 
       size := 95040, atlasrepnrs := [35], 
       values := [ [ 4, 396 ], [ 5, 495 ], [ 6, 144 ] ]
  ));

# Hints for M22:
InstallAlmostSimpleHint( "M22", "StabChainHint",
  rec( name := "M22", fields := [2], dimensions := [10], 
       usemax := [ 2 ], 
       size := 443520, atlasrepnrs := [13,14], 
       values := [ [ 1, 77 ], [ 4, 330 ], [ 7, 616 ] ]
  ));
InstallAlmostSimpleHint( "M22", "StabChainHint",
  rec( name := "M22", fields := [2], dimensions := [34], 
       usemax := [ 5, 2, 1 ], 
       size := 443520, atlasrepnrs := [15], 
       values := [ [ 3, 231 ], [ 4, 77 ], [ 9, 22 ] ]
  ));
InstallAlmostSimpleHint( "M22", "StabChainHint",
  rec( name := "M22", fields := [2], dimensions := [98], 
       usemax := [ 2, 6, 3 ], 
       size := 443520, atlasrepnrs := [16], 
       values := [ [ 4, 77 ], [ 4, 330 ], [ 8, 176 ] ]
  ));
InstallAlmostSimpleHint( "M22", "StabChainHint",
  rec( name := "M22", fields := [3], dimensions := [21], 
       usemax := [ 1, 2, 3 ], 
       size := 443520, atlasrepnrs := [17], 
       values := [ [ 1, 22 ], [ 1, 77 ], [ 2, 176 ] ]
  ));
InstallAlmostSimpleHint( "M22", "StabChainHint",
  rec( name := "M22", fields := [3], dimensions := [49], 
       usemax := [ 2, 5 ], 
       size := 443520, atlasrepnrs := [18,19], 
  ));
InstallAlmostSimpleHint( "M22", "StabChainHint",
  rec( name := "M22", fields := [3], dimensions := [55], 
       usemax := [ 2, 5, 6 ], 
       size := 443520, atlasrepnrs := [20], 
       values := [ [ 1, 77 ], [ 3, 231 ], [ 4, 330 ] ]
  ));
InstallAlmostSimpleHint( "M22", "StabChainHint",
  rec( name := "M22", fields := [3], dimensions := [99], 
       usemax := [ 6, 7, 2 ], 
       size := 443520, atlasrepnrs := [21], 
       values := [ [ 4, 330 ], [ 7, 616 ], [ 9, 77 ] ]
  ));
InstallAlmostSimpleHint( "M22", "StabChainHint",
  rec( name := "M22", fields := [3], dimensions := [210], 
       usemax := [ 5, 2, 7 ], 
       size := 443520, atlasrepnrs := [22], 
       values := [ [ 3, 231 ], [ 4, 77 ], [ 7, 616 ] ]
  ));
InstallAlmostSimpleHint( "M22", "StabChainHint",
  rec( name := "M22", fields := [3], dimensions := [231], 
       usemax := [ 2, 1, 5 ], 
       size := 443520, atlasrepnrs := [23], 
       values := [ [ 6, 77 ], [ 15, 22 ], [ 18, 231 ] ]
  ));
InstallAlmostSimpleHint( "M22", "StabChainHint",
  rec( name := "M22", fields := [4], dimensions := [70], 
       usemax := [ 1, 2, 5 ], 
       size := 443520, atlasrepnrs := [24,25], 
       values := [ [ 8, 22 ], [ 8, 77 ], [ 12, 231 ] ]
  ));
InstallAlmostSimpleHint( "M22", "StabChainHint",
  rec( name := "M22", fields := [5], dimensions := [21], 
       usemax := [ 1, 2, 3 ], 
       size := 443520, atlasrepnrs := [26], 
       values := [ [ 1, 22 ], [ 1, 77 ], [ 2, 176 ] ]
  ));
InstallAlmostSimpleHint( "M22", "StabChainHint",
  rec( name := "M22", fields := [5], dimensions := [55], 
       usemax := [ 2, 5, 6 ], 
       size := 443520, atlasrepnrs := [27], 
       values := [ [ 1, 77 ], [ 3, 231 ], [ 4, 330 ] ]
  ));
InstallAlmostSimpleHint( "M22", "StabChainHint",
  rec( name := "M22", fields := [5], dimensions := [98], 
       usemax := [ 7, 2, 5 ], 
       size := 443520, atlasrepnrs := [28], 
       values := [ [ 7, 616 ], [ 8, 77 ], [ 9, 231 ] ]
  ));
InstallAlmostSimpleHint( "M22", "StabChainHint",
  rec( name := "M22", fields := [5], dimensions := [133], 
       usemax := [ 2, 8, 5 ], 
       size := 443520, atlasrepnrs := [29], 
       values := [ [ 5, 77 ], [ 7, 672 ], [ 9, 231 ] ]
  ));
InstallAlmostSimpleHint( "M22", "StabChainHint",
  rec( name := "M22", fields := [5], dimensions := [210], 
       usemax := [ 5, 2, 7 ], 
       size := 443520, atlasrepnrs := [30], 
       values := [ [ 3, 231 ], [ 5, 77 ], [ 7, 616 ] ]
  ));
InstallAlmostSimpleHint( "M22", "StabChainHint",
  rec( name := "M22", fields := [5], dimensions := [280], 
       usemax := [ 5, 2, 3 ], 
       size := 443520, atlasrepnrs := [31], 
       values := [ [ 9, 231 ], [ 10, 77 ], [ 16, 176 ] ]
  ));
InstallAlmostSimpleHint( "M22", "StabChainHint",
  rec( name := "M22", fields := [5], dimensions := [385], 
       usemax := [ 7, 2, 5 ], 
       size := 443520, atlasrepnrs := [32], 
       values := [ [ 7, 616 ], [ 8, 77 ], [ 9, 231 ] ]
  ));
InstallAlmostSimpleHint( "M22", "StabChainHint",
  rec( name := "M22", fields := [7], dimensions := [21], 
       usemax := [ 1, 2, 3 ], 
       size := 443520, atlasrepnrs := [33], 
       values := [ [ 1, 22 ], [ 1, 77 ], [ 2, 176 ] ]
  ));
InstallAlmostSimpleHint( "M22", "StabChainHint",
  rec( name := "M22", fields := [7], dimensions := [45], 
       usemax := [ 6, 3, 4 ], 
       size := 443520, atlasrepnrs := [34], 
       values := [ [ 12, 330 ], [ 20, 176 ], [ 20, 176 ] ]
  ));
InstallAlmostSimpleHint( "M22", "StabChainHint",
  rec( name := "M22", fields := [7], dimensions := [54], 
       usemax := [ 6, 7, 2 ], 
       size := 443520, atlasrepnrs := [35], 
       values := [ [ 4, 330 ], [ 7, 616 ], [ 9, 77 ] ]
  ));
InstallAlmostSimpleHint( "M22", "StabChainHint",
  rec( name := "M22", fields := [7], dimensions := [154], 
       usemax := [ 3, 4, 5 ], 
       size := 443520, atlasrepnrs := [36], 
       values := [ [ 2, 176 ], [ 2, 176 ], [ 3, 231 ] ]
  ));
InstallAlmostSimpleHint( "M22", "StabChainHint",
  rec( name := "M22", fields := [7], dimensions := [210], 
       usemax := [ 5, 2, 7 ], 
       size := 443520, atlasrepnrs := [37], 
       values := [ [ 3, 231 ], [ 5, 77 ], [ 7, 616 ] ]
  ));
InstallAlmostSimpleHint( "M22", "StabChainHint",
  rec( name := "M22", fields := [7], dimensions := [231], 
       usemax := [ 2, 7, 8 ], 
       size := 443520, atlasrepnrs := [38], 
       values := [ [ 5, 77 ], [ 7, 616 ], [ 7, 672 ] ]
  ));
InstallAlmostSimpleHint( "M22", "StabChainHint",
  rec( name := "M22", fields := [7], dimensions := [385], 
       usemax := [ 7, 2, 3 ], 
       size := 443520, atlasrepnrs := [39], 
       values := [ [ 7, 616 ], [ 9, 77 ], [ 10, 176 ] ]
  ));
InstallAlmostSimpleHint( "M22", "StabChainHint",
  rec( name := "M22", fields := [9], dimensions := [45], 
       usemax := [ 6, 3, 4 ], 
       size := 443520, atlasrepnrs := [40], 
       values := [ [ 12, 330 ], [ 20, 176 ], [ 20, 176 ] ]
  ));
InstallAlmostSimpleHint( "M22", "StabChainHint",
  rec( name := "M22", fields := [11], dimensions := [20], 
       usemax := [ 5, 2, 7 ], 
       size := 443520, atlasrepnrs := [41], 
       values := [ [ 3, 231 ], [ 5, 77 ], [ 7, 616 ] ]
  ));
InstallAlmostSimpleHint( "M22", "StabChainHint",
  rec( name := "M22", fields := [11], dimensions := [45], 
       usemax := [ 6, 3, 4 ], 
       size := 443520, atlasrepnrs := [42,43], 
       values := [ [ 12, 330 ], [ 20, 176 ], [ 20, 176 ] ]
  ));
InstallAlmostSimpleHint( "M22", "StabChainHint",
  rec( name := "M22", fields := [11], dimensions := [55], 
       usemax := [ 2, 5, 6 ], 
       size := 443520, atlasrepnrs := [44], 
       values := [ [ 1, 77 ], [ 3, 231 ], [ 4, 330 ] ]
  ));
InstallAlmostSimpleHint( "M22", "StabChainHint",
  rec( name := "M22", fields := [11], dimensions := [99], 
       usemax := [ 6, 7, 2 ], 
       size := 443520, atlasrepnrs := [45], 
       values := [ [ 4, 330 ], [ 7, 616 ], [ 9, 77 ] ]
  ));
InstallAlmostSimpleHint( "M22", "StabChainHint",
  rec( name := "M22", fields := [11], dimensions := [154], 
       usemax := [ 3, 4, 5 ], 
       size := 443520, atlasrepnrs := [46], 
       values := [ [ 2, 176 ], [ 2, 176 ], [ 3, 231 ] ]
  ));
InstallAlmostSimpleHint( "M22", "StabChainHint",
  rec( name := "M22", fields := [11], dimensions := [190], 
       usemax := [ 2, 5, 3 ], 
       size := 443520, atlasrepnrs := [47], 
       values := [ [ 10, 77 ], [ 12, 231 ], [ 20, 176 ] ]
  ));
InstallAlmostSimpleHint( "M22", "StabChainHint",
  rec( name := "M22", fields := [11], dimensions := [231], 
       usemax := [ 2, 7, 8 ], 
       size := 443520, atlasrepnrs := [48], 
       values := [ [ 5, 77 ], [ 7, 616 ], [ 7, 672 ] ]
  ));
InstallAlmostSimpleHint( "M22", "StabChainHint",
  rec( name := "M22", fields := [11], dimensions := [385], 
       usemax := [ 7, 2, 3 ], 
       size := 443520, atlasrepnrs := [49], 
       values := [ [ 7, 616 ], [ 8, 77 ], [ 12, 176 ] ]
  ));
InstallAlmostSimpleHint( "M22", "StabChainHint",
  rec( name := "M22", fields := [25], dimensions := [45], 
       usemax := [ 6, 3, 4 ], 
       size := 443520, atlasrepnrs := [50], 
       values := [ [ 12, 330 ], [ 20, 176 ], [ 20, 176 ] ]
  ));
InstallAlmostSimpleHint( "M22", "StabChainHint",
  rec( name := "M22", fields := [49], dimensions := [280], 
       usemax := [ 2, 5, 6 ], 
       size := 443520, atlasrepnrs := [51,52], 
       values := [ [ 10, 77 ], [ 12, 231 ], [ 12, 330 ] ]
  ));

# Hints for M23:
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [2], dimensions := [11], 
       usemax := [ 3 ], 
       size := 10200960, atlasrepnrs := [8,9], 
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [2], dimensions := [44], 
       usemax := [ 6 ], 
       size := 10200960, atlasrepnrs := [10,11], 
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [2], dimensions := [120], 
       usemax := [ 1, 3, 4 ], 
       size := 10200960, atlasrepnrs := [12], 
       values := [ [ 10, 23 ], [ 18, 253 ], [ 24, 506 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [2], dimensions := [220], 
       usemax := [ 2 ], 
       size := 10200960, atlasrepnrs := [13,14], 
       values := [ [ 27, 253 ], [ 34, 23 ], [ 36, 1771 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [2], dimensions := [252], 
       usemax := [ 3, 6, 4 ], 
       size := 10200960, atlasrepnrs := [15], 
       values := [ [ 12, 253 ], [ 18, 1771 ], [ 24, 506 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [3], dimensions := [22], 
       usemax := [ 1, 2, 3 ], 
       size := 10200960, atlasrepnrs := [16], 
       values := [ [ 1, 23 ], [ 3, 253 ], [ 3, 253 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [3], dimensions := [104], 
       usemax := [ 3 ], 
       size := 10200960, atlasrepnrs := [17,18], 
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [3], dimensions := [231], 
       usemax := [ 2, 3, 6 ], 
       size := 10200960, atlasrepnrs := [19], 
       values := [ [ 3, 253 ], [ 18, 253 ], [ 18, 1771 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [3], dimensions := [253], 
       usemax := [ 4, 6, 3 ], 
       size := 10200960, atlasrepnrs := [20], 
       values := [ [ 6, 506 ], [ 18, 1771 ], [ 39, 253 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [3], dimensions := [770], 
       usemax := [ 6, 2, 3 ], 
       size := 10200960, atlasrepnrs := [21], 
       values := [ [ 18, 1771 ], [ 45, 253 ], [ 45, 253 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [4], dimensions := [896], 
       usemax := [ 2, 3, 1 ], 
       size := 10200960, atlasrepnrs := [22,23], 
       values := [ [ 48, 253 ], [ 60, 253 ], [ 70, 23 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [5], dimensions := [22], 
       usemax := [ 1, 2, 3 ], 
       size := 10200960, atlasrepnrs := [24], 
       values := [ [ 1, 23 ], [ 3, 253 ], [ 3, 253 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [5], dimensions := [230], 
       usemax := [ 2, 3, 4 ], 
       size := 10200960, atlasrepnrs := [25], 
       values := [ [ 3, 253 ], [ 3, 253 ], [ 6, 506 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [5], dimensions := [231], 
       usemax := [ 3, 6 ], 
       size := 10200960, atlasrepnrs := [26,27], 
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [5], dimensions := [896], 
       usemax := [ 3, 6, 4 ], 
       size := 10200960, atlasrepnrs := [28], 
       values := [ [ 39, 253 ], [ 54, 1771 ], [ 78, 506 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [7], dimensions := [22], 
       usemax := [ 1, 2, 3 ], 
       size := 10200960, atlasrepnrs := [29], 
       values := [ [ 1, 23 ], [ 3, 253 ], [ 3, 253 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [7], dimensions := [45], 
       usemax := [ 7 ], 
       size := 10200960, atlasrepnrs := [30], 
       values := [ [ 404, 40320 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [7], dimensions := [208], 
       usemax := [ 4, 6, 3 ], 
       size := 10200960, atlasrepnrs := [31], 
       values := [ [ 6, 506 ], [ 18, 1771 ], [ 42, 253 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [7], dimensions := [231], 
       usemax := [ 2, 3, 6 ], 
       size := 10200960, atlasrepnrs := [32], 
       values := [ [ 3, 253 ], [ 15, 253 ], [ 18, 1771 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [7], dimensions := [990], 
       usemax := [ 3, 1, 6 ], 
       size := 10200960, atlasrepnrs := [33], 
       values := [ [ 30, 253 ], [ 45, 23 ], [ 72, 1771 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [9], dimensions := [45], 
       usemax := [ 7 ], 
       size := 10200960, atlasrepnrs := [35], 
       values := [ [ 404, 40320 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [9], dimensions := [990], 
       usemax := [ 3, 1, 2 ], 
       size := 10200960, atlasrepnrs := [37], 
       values := [ [ 30, 253 ], [ 45, 23 ], [ 45, 253 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [11], dimensions := [22], 
       usemax := [ 1, 2, 3 ], 
       size := 10200960, atlasrepnrs := [38], 
       values := [ [ 1, 23 ], [ 3, 253 ], [ 3, 253 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [11], dimensions := [45], 
       usemax := [ 5, 7 ], 
       size := 10200960, atlasrepnrs := [39], 
       values := [ [ 208, 1288 ], [ 404, 40320 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [11], dimensions := [229], 
       usemax := [ 5, 3, 6 ], 
       size := 10200960, atlasrepnrs := [40], 
       values := [ [ 13, 1288 ], [ 18, 253 ], [ 18, 1771 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [11], dimensions := [231], 
       usemax := [ 2, 3, 6 ], 
       size := 10200960, atlasrepnrs := [41], 
       values := [ [ 3, 253 ], [ 18, 253 ], [ 18, 1771 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [11], dimensions := [253], 
       usemax := [ 4, 6, 3 ], 
       size := 10200960, atlasrepnrs := [42], 
       values := [ [ 6, 506 ], [ 18, 1771 ], [ 42, 253 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [11], dimensions := [806], 
       usemax := [ 3, 6, 2 ], 
       size := 10200960, atlasrepnrs := [43], 
       values := [ [ 63, 253 ], [ 90, 1771 ], [ 105, 253 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [11], dimensions := [990], 
       usemax := [ 3, 1, 6 ], 
       size := 10200960, atlasrepnrs := [44], 
       values := [ [ 30, 253 ], [ 45, 23 ], [ 72, 1771 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [23], dimensions := [21], 
       usemax := [ 2, 3, 6 ], 
       size := 10200960, atlasrepnrs := [45], 
       values := [ [ 3, 253 ], [ 18, 253 ], [ 36, 1771 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [23], dimensions := [45], 
       usemax := [ 7 ], 
       size := 10200960, atlasrepnrs := [47], 
       values := [ [ 404, 40320 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [23], dimensions := [210], 
       usemax := [ 6, 3, 2 ], 
       size := 10200960, atlasrepnrs := [48], 
       values := [ [ 18, 1771 ], [ 45, 253 ], [ 60, 253 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [23], dimensions := [230], 
       usemax := [ 2, 3, 4 ], 
       size := 10200960, atlasrepnrs := [49], 
       values := [ [ 3, 253 ], [ 3, 253 ], [ 6, 506 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [23], dimensions := [231], 
       usemax := [ 3, 6, 2 ], 
       size := 10200960, atlasrepnrs := [50], 
       values := [ [ 63, 253 ], [ 90, 1771 ], [ 105, 253 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [23], dimensions := [253], 
       usemax := [ 4, 6, 3 ], 
       size := 10200960, atlasrepnrs := [51], 
       values := [ [ 6, 506 ], [ 18, 1771 ], [ 42, 253 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [23], dimensions := [280], 
       usemax := [ 3, 6, 4 ], 
       size := 10200960, atlasrepnrs := [52], 
       values := [ [ 30, 253 ], [ 72, 1771 ], [ 126, 506 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [23], dimensions := [665], 
       usemax := [ 6, 2, 3 ], 
       size := 10200960, atlasrepnrs := [53], 
       values := [ [ 90, 1771 ], [ 105, 253 ], [ 105, 253 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [25], dimensions := [45], 
       usemax := [ 7 ], 
       size := 10200960, atlasrepnrs := [54], 
       values := [ [ 404, 40320 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [25], dimensions := [770], 
       usemax := [ 6, 3, 2 ], 
       size := 10200960, atlasrepnrs := [55], 
       values := [ [ 18, 1771 ], [ 30, 253 ], [ 60, 253 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [25], dimensions := [990], 
       usemax := [ 3, 1, 6 ], 
       size := 10200960, atlasrepnrs := [56], 
       values := [ [ 30, 253 ], [ 45, 23 ], [ 54, 1771 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [49], dimensions := [231], 
       usemax := [ 3, 6, 2 ], 
       size := 10200960, atlasrepnrs := [57,58], 
       values := [ [ 63, 253 ], [ 90, 1771 ], [ 105, 253 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [49], dimensions := [770], 
       usemax := [ 6, 3, 2 ], 
       size := 10200960, atlasrepnrs := [59,60], 
       values := [ [ 18, 1771 ], [ 30, 253 ], [ 57, 253 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [49], dimensions := [896], 
       usemax := [ 3, 6, 2 ], 
       size := 10200960, atlasrepnrs := [61,62], 
       values := [ [ 63, 253 ], [ 90, 1771 ], [ 105, 253 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [121], dimensions := [231], 
       usemax := [ 3, 6, 2 ], 
       size := 10200960, atlasrepnrs := [63,64], 
       values := [ [ 63, 253 ], [ 90, 1771 ], [ 105, 253 ] ]
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", fields := [121], dimensions := [770], 
       usemax := [ 6, 3, 2 ], 
       size := 10200960, atlasrepnrs := [65,66], 
       values := [ [ 18, 1771 ], [ 30, 253 ], [ 60, 253 ] ]
  ));

# Hints for M24:
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [2], dimensions := [11], 
       usemax := [ 2 ], 
       size := 244823040, atlasrepnrs := [8,9], 
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [2], dimensions := [44], 
       usemax := [ 5 ], 
       size := 244823040, atlasrepnrs := [10,11], 
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [2], dimensions := [120], 
       usemax := [ 2, 3, 5 ], 
       size := 244823040, atlasrepnrs := [12], 
       values := [ [ 30, 276 ], [ 48, 759 ], [ 72, 1771 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [2], dimensions := [220], 
       usemax := [ 5 ], 
       size := 244823040, atlasrepnrs := [13,14], 
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [2], dimensions := [252], 
       usemax := [ 5, 3, 7 ], 
       size := 244823040, atlasrepnrs := [15], 
       values := [ [ 18, 1771 ], [ 32, 759 ], [ 114, 3795 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [2], dimensions := [320], 
       usemax := [ 1 ], 
       size := 244823040, atlasrepnrs := [16,17], 
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [2], dimensions := [1242], 
       usemax := [ 3, 5, 7 ], 
       size := 244823040, atlasrepnrs := [18], 
       values := [ [ 32, 759 ], [ 108, 1771 ], [ 114, 3795 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [2], dimensions := [1792], 
       usemax := [ 5, 3, 7 ], 
       size := 244823040, atlasrepnrs := [19], 
       values := [ [ 108, 1771 ], [ 160, 759 ], [ 228, 3795 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [3], dimensions := [22], 
       usemax := [ 2, 4, 6 ], 
       size := 244823040, atlasrepnrs := [20], 
       values := [ [ 3, 276 ], [ 13, 1288 ], [ 21, 2024 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [3], dimensions := [231], 
       usemax := [ 6, 2, 5 ], 
       size := 244823040, atlasrepnrs := [21], 
       values := [ [ 21, 2024 ], [ 63, 276 ], [ 108, 1771 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [3], dimensions := [252], 
       usemax := [ 2, 3, 4 ], 
       size := 244823040, atlasrepnrs := [22], 
       values := [ [ 3, 276 ], [ 8, 759 ], [ 13, 1288 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [3], dimensions := [483], 
       usemax := [ 3, 5, 6 ], 
       size := 244823040, atlasrepnrs := [23], 
       values := [ [ 8, 759 ], [ 18, 1771 ], [ 21, 2024 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [3], dimensions := [770], 
       usemax := [ 5, 7, 3 ], 
       size := 244823040, atlasrepnrs := [24,25], 
       values := [ [ 72, 1771 ], [ 266, 3795 ], [ 280, 759 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [5], dimensions := [23], 
       usemax := [ 1, 2, 3 ], 
       size := 244823040, atlasrepnrs := [26], 
       values := [ [ 1, 24 ], [ 3, 276 ], [ 8, 759 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [5], dimensions := [231], 
       usemax := [ 5, 3, 2 ], 
       size := 244823040, atlasrepnrs := [27], 
       values := [ [ 108, 1771 ], [ 168, 759 ], [ 294, 276 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [5], dimensions := [252], 
       usemax := [ 2, 3, 4 ], 
       size := 244823040, atlasrepnrs := [28], 
       values := [ [ 3, 276 ], [ 8, 759 ], [ 13, 1288 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [5], dimensions := [253], 
       usemax := [ 2, 6, 1 ], 
       size := 244823040, atlasrepnrs := [29], 
       values := [ [ 3, 276 ], [ 21, 2024 ], [ 22, 24 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [7], dimensions := [23], 
       usemax := [ 1, 2, 3 ], 
       size := 244823040, atlasrepnrs := [30], 
       values := [ [ 1, 24 ], [ 3, 276 ], [ 8, 759 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [7], dimensions := [45], 
       usemax := [ 7 ], 
       size := 244823040, atlasrepnrs := [31], 
       values := [ [ 114, 3795 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [7], dimensions := [252], 
       usemax := [ 2, 3, 4 ], 
       size := 244823040, atlasrepnrs := [32], 
       values := [ [ 3, 276 ], [ 8, 759 ], [ 13, 1288 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [7], dimensions := [253], 
       usemax := [ 2, 6, 1 ], 
       size := 244823040, atlasrepnrs := [33], 
       values := [ [ 3, 276 ], [ 21, 2024 ], [ 22, 24 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [7], dimensions := [483], 
       usemax := [ 3, 5, 6 ], 
       size := 244823040, atlasrepnrs := [34], 
       values := [ [ 8, 759 ], [ 18, 1771 ], [ 21, 2024 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [7], dimensions := [990], 
       usemax := [ 7, 2, 3 ], 
       size := 244823040, atlasrepnrs := [35], 
       values := [ [ 114, 3795 ], [ 135, 276 ], [ 360, 759 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [9], dimensions := [45], 
       usemax := [ 7 ], 
       size := 244823040, atlasrepnrs := [36,37], 
       values := [ [ 114, 3795 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [9], dimensions := [990], 
       usemax := [ 7, 2, 3 ], 
       size := 244823040, atlasrepnrs := [38], 
       values := [ [ 114, 3795 ], [ 135, 276 ], [ 360, 759 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [11], dimensions := [23], 
       usemax := [ 1, 2, 3 ], 
       size := 244823040, atlasrepnrs := [39], 
       values := [ [ 1, 24 ], [ 3, 276 ], [ 8, 759 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [11], dimensions := [45], 
       usemax := [ 7, 4 ], 
       size := 244823040, atlasrepnrs := [40], 
       values := [ [ 114, 3795 ], [ 208, 1288 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [11], dimensions := [229], 
       usemax := [ 4, 5, 7 ], 
       size := 244823040, atlasrepnrs := [41], 
       values := [ [ 13, 1288 ], [ 18, 1771 ], [ 38, 3795 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [11], dimensions := [253], 
       usemax := [ 2, 6, 1 ], 
       size := 244823040, atlasrepnrs := [42], 
       values := [ [ 3, 276 ], [ 21, 2024 ], [ 22, 24 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [11], dimensions := [482], 
       usemax := [ 2, 7, 5 ], 
       size := 244823040, atlasrepnrs := [43], 
       values := [ [ 60, 276 ], [ 76, 3795 ], [ 90, 1771 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [11], dimensions := [806], 
       usemax := [ 5, 4, 7 ], 
       size := 244823040, atlasrepnrs := [44], 
       values := [ [ 90, 1771 ], [ 208, 1288 ], [ 228, 3795 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [11], dimensions := [990], 
       usemax := [ 7, 2, 3 ], 
       size := 244823040, atlasrepnrs := [45], 
       values := [ [ 114, 3795 ], [ 135, 276 ], [ 360, 759 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [23], dimensions := [23], 
       usemax := [ 1, 2, 3 ], 
       size := 244823040, atlasrepnrs := [46], 
       values := [ [ 1, 24 ], [ 3, 276 ], [ 8, 759 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [23], dimensions := [45], 
       usemax := [ 7 ], 
       size := 244823040, atlasrepnrs := [47], 
       values := [ [ 114, 3795 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [23], dimensions := [231], 
       usemax := [ 5, 3, 4 ], 
       size := 244823040, atlasrepnrs := [48], 
       values := [ [ 108, 1771 ], [ 168, 759 ], [ 715, 1288 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [23], dimensions := [251], 
       usemax := [ 1, 6, 3 ], 
       size := 244823040, atlasrepnrs := [49], 
       values := [ [ 21, 24 ], [ 42, 2024 ], [ 56, 759 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [23], dimensions := [253], 
       usemax := [ 2, 1, 6 ], 
       size := 244823040, atlasrepnrs := [50], 
       values := [ [ 3, 276 ], [ 21, 24 ], [ 21, 2024 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [23], dimensions := [483], 
       usemax := [ 3, 5, 6 ], 
       size := 244823040, atlasrepnrs := [51], 
       values := [ [ 8, 759 ], [ 18, 1771 ], [ 21, 2024 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [23], dimensions := [770], 
       usemax := [ 5, 1, 3 ], 
       size := 244823040, atlasrepnrs := [52], 
       values := [ [ 90, 1771 ], [ 280, 24 ], [ 280, 759 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [23], dimensions := [990], 
       usemax := [ 7, 2, 3 ], 
       size := 244823040, atlasrepnrs := [53], 
       values := [ [ 114, 3795 ], [ 135, 276 ], [ 360, 759 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [25], dimensions := [45], 
       usemax := [ 7 ], 
       size := 244823040, atlasrepnrs := [54,55], 
       values := [ [ 114, 3795 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [25], dimensions := [770], 
       usemax := [ 5, 3, 6 ], 
       size := 244823040, atlasrepnrs := [56], 
       values := [ [ 90, 1771 ], [ 280, 759 ], [ 420, 2024 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [25], dimensions := [990], 
       usemax := [ 7, 2, 3 ], 
       size := 244823040, atlasrepnrs := [57], 
       values := [ [ 114, 3795 ], [ 135, 276 ], [ 360, 759 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [49], dimensions := [231], 
       usemax := [ 5, 3, 4 ], 
       size := 244823040, atlasrepnrs := [58], 
       values := [ [ 108, 1771 ], [ 168, 759 ], [ 715, 1288 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [49], dimensions := [770], 
       usemax := [ 5, 3, 6 ], 
       size := 244823040, atlasrepnrs := [59], 
       values := [ [ 90, 1771 ], [ 280, 759 ], [ 399, 2024 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [121], dimensions := [231], 
       usemax := [ 5, 3, 4 ], 
       size := 244823040, atlasrepnrs := [60], 
       values := [ [ 108, 1771 ], [ 168, 759 ], [ 715, 1288 ] ]
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", fields := [121], dimensions := [770], 
       usemax := [ 5, 3, 6 ], 
       size := 244823040, atlasrepnrs := [61], 
       values := [ [ 90, 1771 ], [ 280, 759 ], [ 420, 2024 ] ]
  ));

# Hints for HS:
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [2], dimensions := [20], 
       usemax := [ 1, 4, 6 ], 
       size := 44352000, atlasrepnrs := [9], 
       values := [ [ 10, 100 ], [ 11, 1100 ], [ 39, 3850 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [2], dimensions := [56], 
       usemax := [ 1, 6, 8 ], 
       size := 44352000, atlasrepnrs := [10], 
       values := [ [ 10, 100 ], [ 39, 3850 ], [ 56, 5600 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [2], dimensions := [132], 
       usemax := [ 5, 1, 2 ], 
       size := 44352000, atlasrepnrs := [11], 
       values := [ [ 11, 1100 ], [ 34, 100 ], [ 56, 176 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [2], dimensions := [518], 
       usemax := [ 1, 5, 7 ], 
       size := 44352000, atlasrepnrs := [12], 
       values := [ [ 34, 100 ], [ 88, 1100 ], [ 126, 4125 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [2], dimensions := [1000], 
       usemax := [ 1, 5, 7 ], 
       size := 44352000, atlasrepnrs := [13], 
       values := [ [ 34, 100 ], [ 66, 1100 ], [ 126, 4125 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [3], dimensions := [22], 
       usemax := [ 1, 2, 3 ], 
       size := 44352000, atlasrepnrs := [14], 
       values := [ [ 1, 100 ], [ 2, 176 ], [ 2, 176 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [3], dimensions := [49], 
       usemax := [ 3, 2, 5 ], 
       size := 44352000, atlasrepnrs := [15,16], 
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [3], dimensions := [77], 
       usemax := [ 1, 4, 5 ], 
       size := 44352000, atlasrepnrs := [17], 
       values := [ [ 1, 100 ], [ 11, 1100 ], [ 11, 1100 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [3], dimensions := [154], 
       usemax := [ 5 ], 
       size := 44352000, atlasrepnrs := [18,19,20], 
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [3], dimensions := [231], 
       usemax := [ 4, 1, 6 ], 
       size := 44352000, atlasrepnrs := [21], 
       values := [ [ 11, 1100 ], [ 21, 100 ], [ 39, 3850 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [3], dimensions := [321], 
       usemax := [ 2, 3, 1 ], 
       size := 44352000, atlasrepnrs := [22], 
       values := [ [ 40, 176 ], [ 40, 176 ], [ 90, 100 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [3], dimensions := [693], 
       usemax := [ 5, 6, 2 ], 
       size := 44352000, atlasrepnrs := [23], 
       values := [ [ 11, 1100 ], [ 39, 3850 ], [ 42, 176 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [3], dimensions := [748], 
       usemax := [ 6, 1, 2 ], 
       size := 44352000, atlasrepnrs := [24], 
       values := [ [ 39, 3850 ], [ 55, 100 ], [ 56, 176 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [3], dimensions := [770], 
       usemax := [ 2, 3, 6 ], 
       size := 44352000, atlasrepnrs := [25], 
       values := [ [ 40, 176 ], [ 40, 176 ], [ 156, 3850 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [3], dimensions := [825], 
       usemax := [ 4, 1, 6 ], 
       size := 44352000, atlasrepnrs := [26], 
       values := [ [ 11, 1100 ], [ 21, 100 ], [ 39, 3850 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [4], dimensions := [896], 
       usemax := [ 1, 7, 5 ], 
       size := 44352000, atlasrepnrs := [27,28], 
       values := [ [ 70, 100 ], [ 126, 4125 ], [ 154, 1100 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [5], dimensions := [21], 
       usemax := [ 2, 3, 4 ], 
       size := 44352000, atlasrepnrs := [29], 
       values := [ [ 2, 176 ], [ 2, 176 ], [ 11, 1100 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [5], dimensions := [55], 
       usemax := [ 5, 2, 3 ], 
       size := 44352000, atlasrepnrs := [30], 
       values := [ [ 11, 1100 ], [ 38, 176 ], [ 38, 176 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [5], dimensions := [98], 
       usemax := [ 2, 3, 5 ], 
       size := 44352000, atlasrepnrs := [31], 
       values := [ [ 16, 176 ], [ 16, 176 ], [ 143, 1100 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [5], dimensions := [133], 
       usemax := [ 2, 3, 8 ], 
       size := 44352000, atlasrepnrs := [32,33], 
       values := [ [ 16, 176 ], [ 38, 176 ], [ 56, 5600 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [5], dimensions := [175], 
       usemax := [ 2, 3, 4 ], 
       size := 44352000, atlasrepnrs := [34], 
       values := [ [ 2, 176 ], [ 2, 176 ], [ 11, 1100 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [5], dimensions := [210], 
       usemax := [ 2, 3, 10 ], 
       size := 44352000, atlasrepnrs := [35], 
       values := [ [ 38, 176 ], [ 38, 176 ], [ 58, 5775 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [5], dimensions := [280], 
       usemax := [ 3, 2, 5 ], 
       size := 44352000, atlasrepnrs := [36], 
       values := [ [ 16, 176 ], [ 126, 176 ], [ 231, 1100 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [5], dimensions := [518], 
       usemax := [ 2, 3, 10 ], 
       size := 44352000, atlasrepnrs := [37], 
       values := [ [ 38, 176 ], [ 38, 176 ], [ 58, 5775 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [5], dimensions := [650], 
       usemax := [ 2, 3, 6 ], 
       size := 44352000, atlasrepnrs := [38], 
       values := [ [ 38, 176 ], [ 38, 176 ], [ 39, 3850 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [7], dimensions := [22], 
       usemax := [ 1, 2, 3 ], 
       size := 44352000, atlasrepnrs := [39], 
       values := [ [ 1, 100 ], [ 2, 176 ], [ 2, 176 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [7], dimensions := [77], 
       usemax := [ 1, 4, 5 ], 
       size := 44352000, atlasrepnrs := [40], 
       values := [ [ 1, 100 ], [ 11, 1100 ], [ 11, 1100 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [7], dimensions := [154], 
       usemax := [ 5 ], 
       size := 44352000, atlasrepnrs := [41,42,43], 
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [7], dimensions := [175], 
       usemax := [ 2, 3, 4 ], 
       size := 44352000, atlasrepnrs := [44], 
       values := [ [ 2, 176 ], [ 2, 176 ], [ 11, 1100 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [7], dimensions := [231], 
       usemax := [ 4, 1, 6 ], 
       size := 44352000, atlasrepnrs := [45], 
       values := [ [ 11, 1100 ], [ 21, 100 ], [ 39, 3850 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [7], dimensions := [605], 
       usemax := [ 2, 3, 1 ], 
       size := 44352000, atlasrepnrs := [46], 
       values := [ [ 40, 176 ], [ 40, 176 ], [ 45, 100 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [7], dimensions := [693], 
       usemax := [ 5, 6, 2 ], 
       size := 44352000, atlasrepnrs := [47], 
       values := [ [ 11, 1100 ], [ 39, 3850 ], [ 42, 176 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [7], dimensions := [770], 
       usemax := [ 2 ], 
       size := 44352000, atlasrepnrs := [48,49,50], 
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [7], dimensions := [803], 
       usemax := [ 7, 1, 10 ], 
       size := 44352000, atlasrepnrs := [51], 
       values := [ [ 42, 4125 ], [ 54, 100 ], [ 58, 5775 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [11], dimensions := [22], 
       usemax := [ 1, 2, 3 ], 
       size := 44352000, atlasrepnrs := [52], 
       values := [ [ 1, 100 ], [ 2, 176 ], [ 2, 176 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [11], dimensions := [77], 
       usemax := [ 1, 4, 5 ], 
       size := 44352000, atlasrepnrs := [53], 
       values := [ [ 1, 100 ], [ 11, 1100 ], [ 11, 1100 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [11], dimensions := [154], 
       usemax := [ 5 ], 
       size := 44352000, atlasrepnrs := [54,55,56], 
       values := [ [ 11, 1100 ], [ 39, 3850 ], [ 42, 4125 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [11], dimensions := [174], 
       usemax := [ 1, 2, 3 ], 
       size := 44352000, atlasrepnrs := [57], 
       values := [ [ 20, 100 ], [ 42, 176 ], [ 42, 176 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [11], dimensions := [231], 
       usemax := [ 4, 1, 6 ], 
       size := 44352000, atlasrepnrs := [58], 
       values := [ [ 11, 1100 ], [ 20, 100 ], [ 39, 3850 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [11], dimensions := [693], 
       usemax := [ 5, 6, 2 ], 
       size := 44352000, atlasrepnrs := [59], 
       values := [ [ 11, 1100 ], [ 39, 3850 ], [ 42, 176 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [11], dimensions := [770], 
       usemax := [ 4, 5, 1 ], 
       size := 44352000, atlasrepnrs := [60], 
       values := [ [ 11, 1100 ], [ 11, 1100 ], [ 20, 100 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [11], dimensions := [825], 
       usemax := [ 4, 1, 6 ], 
       size := 44352000, atlasrepnrs := [61], 
       values := [ [ 11, 1100 ], [ 20, 100 ], [ 39, 3850 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [11], dimensions := [854], 
       usemax := [ 1, 7, 5 ], 
       size := 44352000, atlasrepnrs := [62], 
       values := [ [ 45, 100 ], [ 126, 4125 ], [ 154, 1100 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [11], dimensions := [896], 
       usemax := [ 1, 6, 2 ], 
       size := 44352000, atlasrepnrs := [63], 
       values := [ [ 45, 100 ], [ 195, 3850 ], [ 210, 176 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [49], dimensions := [896], 
       usemax := [ 6, 5, 2 ], 
       size := 44352000, atlasrepnrs := [64,65], 
       values := [ [ 195, 3850 ], [ 209, 1100 ], [ 210, 176 ] ]
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", fields := [121], dimensions := [770], 
       usemax := [ 2, 3, 1 ], 
       size := 44352000, atlasrepnrs := [66,67], 
       values := [ [ 40, 176 ], [ 40, 176 ], [ 190, 100 ] ]
  ));

# Hints for J1:
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [2], dimensions := [20], 
       usemax := [ 2, 3, 4 ], 
       size := 175560, atlasrepnrs := [8], 
       values := [ [ 11, 1045 ], [ 15, 1463 ], [ 16, 1540 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [2], dimensions := [76], 
       usemax := [ 3, 2 ], 
       size := 175560, atlasrepnrs := [9,10], 
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [2], dimensions := [112], 
       usemax := [ 1, 2, 3 ], 
       size := 175560, atlasrepnrs := [11,12], 
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [2], dimensions := [360], 
       usemax := [ 2, 3, 4 ], 
       size := 175560, atlasrepnrs := [13], 
       values := [ [ 11, 1045 ], [ 15, 1463 ], [ 16, 1540 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [3], dimensions := [76], 
       usemax := [ 1, 3 ], 
       size := 175560, atlasrepnrs := [14,15], 
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [3], dimensions := [112], 
       usemax := [ 1, 2, 3 ], 
       size := 175560, atlasrepnrs := [16], 
       values := [ [ 3, 266 ], [ 11, 1045 ], [ 15, 1463 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [3], dimensions := [133], 
       usemax := [ 2, 1, 3 ], 
       size := 175560, atlasrepnrs := [17], 
       values := [ [ 11, 1045 ], [ 15, 266 ], [ 15, 1463 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [3], dimensions := [154], 
       usemax := [ 2, 1, 3 ], 
       size := 175560, atlasrepnrs := [18], 
       values := [ [ 11, 1045 ], [ 15, 266 ], [ 15, 1463 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [3], dimensions := [360], 
       usemax := [ 2, 1, 3 ], 
       size := 175560, atlasrepnrs := [19], 
       values := [ [ 11, 1045 ], [ 15, 266 ], [ 15, 1463 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [4], dimensions := [56], 
       usemax := [ 1, 2, 3 ], 
       size := 175560, atlasrepnrs := [20,21,22,23], 
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [5], dimensions := [56], 
       usemax := [ 1, 2, 3 ], 
       size := 175560, atlasrepnrs := [24], 
       values := [ [ 3, 266 ], [ 11, 1045 ], [ 15, 1463 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [5], dimensions := [76], 
       usemax := [ 3 ], 
       size := 175560, atlasrepnrs := [25,26], 
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [5], dimensions := [77], 
       usemax := [ 1, 3, 4 ], 
       size := 175560, atlasrepnrs := [27], 
       values := [ [ 3, 266 ], [ 15, 1463 ], [ 16, 1540 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [5], dimensions := [133], 
       usemax := [ 1, 3, 4 ], 
       size := 175560, atlasrepnrs := [28], 
       values := [ [ 15, 266 ], [ 15, 1463 ], [ 16, 1540 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [5], dimensions := [360], 
       usemax := [ 2, 1, 3 ], 
       size := 175560, atlasrepnrs := [29], 
       values := [ [ 11, 1045 ], [ 15, 266 ], [ 15, 1463 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [7], dimensions := [31], 
       usemax := [ 2, 3, 4 ], 
       size := 175560, atlasrepnrs := [30], 
       values := [ [ 11, 1045 ], [ 15, 1463 ], [ 16, 1540 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [7], dimensions := [45], 
       usemax := [ 2, 4, 5 ], 
       size := 175560, atlasrepnrs := [31], 
       values := [ [ 11, 1045 ], [ 16, 1540 ], [ 16, 1596 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [7], dimensions := [75], 
       usemax := [ 2, 3, 4 ], 
       size := 175560, atlasrepnrs := [32], 
       values := [ [ 11, 1045 ], [ 15, 1463 ], [ 16, 1540 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [7], dimensions := [77], 
       usemax := [ 1, 2, 3 ], 
       size := 175560, atlasrepnrs := [33], 
       values := [ [ 3, 266 ], [ 11, 1045 ], [ 15, 1463 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [7], dimensions := [89], 
       usemax := [ 2, 3, 4 ], 
       size := 175560, atlasrepnrs := [34], 
       values := [ [ 11, 1045 ], [ 15, 1463 ], [ 16, 1540 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [7], dimensions := [112], 
       usemax := [ 1, 2, 3 ], 
       size := 175560, atlasrepnrs := [35], 
       values := [ [ 3, 266 ], [ 11, 1045 ], [ 15, 1463 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [7], dimensions := [120], 
       usemax := [ 2, 3, 4 ], 
       size := 175560, atlasrepnrs := [36], 
       values := [ [ 11, 1045 ], [ 15, 1463 ], [ 16, 1540 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [7], dimensions := [133], 
       usemax := [ 2, 3, 4 ], 
       size := 175560, atlasrepnrs := [37], 
       values := [ [ 11, 1045 ], [ 15, 1463 ], [ 16, 1540 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [7], dimensions := [154], 
       usemax := [ 2, 3, 4 ], 
       size := 175560, atlasrepnrs := [38], 
       values := [ [ 11, 1045 ], [ 15, 1463 ], [ 16, 1540 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [7], dimensions := [266], 
       usemax := [ 2, 3, 4 ], 
       size := 175560, atlasrepnrs := [39], 
       values := [ [ 11, 1045 ], [ 15, 1463 ], [ 16, 1540 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [8], dimensions := [120], 
       usemax := [ 2, 3, 4 ], 
       size := 175560, atlasrepnrs := [40,41,42], 
       values := [ [ 11, 1045 ], [ 15, 1463 ], [ 16, 1540 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [9], dimensions := [56], 
       usemax := [ 1, 2, 3 ], 
       size := 175560, atlasrepnrs := [43,44], 
       values := [ [ 3, 266 ], [ 11, 1045 ], [ 15, 1463 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [9], dimensions := [77], 
       usemax := [ 2, 1, 3 ], 
       size := 175560, atlasrepnrs := [45,46], 
       values := [ [ 11, 1045 ], [ 15, 266 ], [ 15, 1463 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [11], dimensions := [7], 
       usemax := [ 4, 5, 6 ], 
       size := 175560, atlasrepnrs := [47], 
       values := [ [ 16, 1540 ], [ 16, 1596 ], [ 30, 2926 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [11], dimensions := [14], 
       usemax := [ 1, 5, 6 ], 
       size := 175560, atlasrepnrs := [48], 
       values := [ [ 9, 266 ], [ 16, 1596 ], [ 30, 2926 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [11], dimensions := [27], 
       usemax := [ 1, 3, 4 ], 
       size := 175560, atlasrepnrs := [49], 
       values := [ [ 15, 266 ], [ 15, 1463 ], [ 16, 1540 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [11], dimensions := [49], 
       usemax := [ 1, 2, 3 ], 
       size := 175560, atlasrepnrs := [50], 
       values := [ [ 3, 266 ], [ 11, 1045 ], [ 15, 1463 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [11], dimensions := [56], 
       usemax := [ 1, 2, 3 ], 
       size := 175560, atlasrepnrs := [51], 
       values := [ [ 3, 266 ], [ 11, 1045 ], [ 15, 1463 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [11], dimensions := [64], 
       usemax := [ 1, 5, 2 ], 
       size := 175560, atlasrepnrs := [52], 
       values := [ [ 15, 266 ], [ 16, 1596 ], [ 22, 1045 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [11], dimensions := [69], 
       usemax := [ 1, 3, 4 ], 
       size := 175560, atlasrepnrs := [53], 
       values := [ [ 9, 266 ], [ 15, 1463 ], [ 16, 1540 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [11], dimensions := [77], 
       usemax := [ 3 ], 
       size := 175560, atlasrepnrs := [54,55,56], 
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [11], dimensions := [106], 
       usemax := [ 2, 1, 3 ], 
       size := 175560, atlasrepnrs := [57], 
       values := [ [ 11, 1045 ], [ 15, 266 ], [ 15, 1463 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [11], dimensions := [119], 
       usemax := [ 1, 3, 4 ], 
       size := 175560, atlasrepnrs := [58], 
       values := [ [ 9, 266 ], [ 15, 1463 ], [ 16, 1540 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [11], dimensions := [209], 
       usemax := [ 1, 2, 3 ], 
       size := 175560, atlasrepnrs := [59], 
       values := [ [ 9, 266 ], [ 11, 1045 ], [ 15, 1463 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [19], dimensions := [22], 
       usemax := [ 2, 4, 1 ], 
       size := 175560, atlasrepnrs := [60], 
       values := [ [ 11, 1045 ], [ 16, 1540 ], [ 30, 266 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [19], dimensions := [34], 
       usemax := [ 1, 3, 4 ], 
       size := 175560, atlasrepnrs := [61], 
       values := [ [ 3, 266 ], [ 15, 1463 ], [ 16, 1540 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [19], dimensions := [43], 
       usemax := [ 2, 3, 4 ], 
       size := 175560, atlasrepnrs := [62], 
       values := [ [ 11, 1045 ], [ 15, 1463 ], [ 16, 1540 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [19], dimensions := [55], 
       usemax := [ 3, 4, 5 ], 
       size := 175560, atlasrepnrs := [63], 
       values := [ [ 15, 1463 ], [ 16, 1540 ], [ 16, 1596 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [19], dimensions := [76], 
       usemax := [ 1, 3 ], 
       size := 175560, atlasrepnrs := [64,65], 
       brauercharelm := StraightLineProgram( [ [ 1, 1, 2, 1 ], [ 3, 1, 2, 1 ], 
         [ 3, 1, 4, 1 ], [ 3, 1, 5, 1 ], [ 6, 1, 4, 1 ], [ 5, 1, 7, 1 ] ], 2 ), 
       brauercharvals := [ -1, 1 ],
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [19], dimensions := [77], 
       usemax := [ 2, 3, 4 ], 
       size := 175560, atlasrepnrs := [66], 
       values := [ [ 11, 1045 ], [ 15, 1463 ], [ 16, 1540 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [19], dimensions := [133], 
       usemax := [ 2, 3, 4 ], 
       size := 175560, atlasrepnrs := [67,68,69], 
       values := [ [ 11, 1045 ], [ 15, 1463 ], [ 16, 1540 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [19], dimensions := [209], 
       usemax := [ 2, 3, 4 ], 
       size := 175560, atlasrepnrs := [70], 
       values := [ [ 11, 1045 ], [ 15, 1463 ], [ 16, 1540 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [27], dimensions := [120], 
       usemax := [ 2, 1, 3 ], 
       size := 175560, atlasrepnrs := [71,72,73], 
       values := [ [ 11, 1045 ], [ 15, 266 ], [ 15, 1463 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [49], dimensions := [56], 
       usemax := [ 1, 2, 3 ], 
       size := 175560, atlasrepnrs := [74,75], 
       values := [ [ 3, 266 ], [ 11, 1045 ], [ 15, 1463 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [49], dimensions := [77], 
       usemax := [ 2, 3, 4 ], 
       size := 175560, atlasrepnrs := [76,77], 
       values := [ [ 11, 1045 ], [ 15, 1463 ], [ 16, 1540 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [49], dimensions := [133], 
       usemax := [ 2, 1, 3 ], 
       size := 175560, atlasrepnrs := [78,79], 
       values := [ [ 11, 1045 ], [ 15, 266 ], [ 15, 1463 ] ]
  ));
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", fields := [125], dimensions := [120], 
       usemax := [ 2, 1, 3 ], 
       size := 175560, atlasrepnrs := [80,81,82], 
       values := [ [ 11, 1045 ], [ 15, 266 ], [ 15, 1463 ] ]
  ));

# Hints for J2:
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", fields := [2], dimensions := [36], 
       usemax := [ 1, 3, 4 ], 
       size := 604800, atlasrepnrs := [8], 
       values := [ [ 1, 100 ], [ 4, 315 ], [ 6, 525 ] ]
  ));
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", fields := [2], dimensions := [84], 
       usemax := [ 1, 5, 3 ], 
       size := 604800, atlasrepnrs := [9], 
       values := [ [ 6, 100 ], [ 9, 840 ], [ 16, 315 ] ]
  ));
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", fields := [2], dimensions := [160], 
       usemax := [ 3, 4, 5 ], 
       size := 604800, atlasrepnrs := [10], 
       values := [ [ 4, 315 ], [ 6, 525 ], [ 9, 840 ] ]
  ));
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", fields := [3], dimensions := [36], 
       usemax := [ 1, 3, 4 ], 
       size := 604800, atlasrepnrs := [11], 
       values := [ [ 1, 100 ], [ 4, 315 ], [ 6, 525 ] ]
  ));
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", fields := [3], dimensions := [63], 
       usemax := [ 1, 2, 4 ], 
       size := 604800, atlasrepnrs := [12], 
       values := [ [ 1, 100 ], [ 3, 280 ], [ 6, 525 ] ]
  ));
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", fields := [3], dimensions := [90], 
       usemax := [ 2, 3, 4 ], 
       size := 604800, atlasrepnrs := [13], 
       values := [ [ 3, 280 ], [ 4, 315 ], [ 6, 525 ] ]
  ));
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", fields := [3], dimensions := [133], 
       usemax := [ 4, 1, 5 ], 
       size := 604800, atlasrepnrs := [14], 
       values := [ [ 6, 525 ], [ 7, 100 ], [ 9, 840 ] ]
  ));
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", fields := [3], dimensions := [225], 
       usemax := [ 4, 1, 5 ], 
       size := 604800, atlasrepnrs := [15], 
       values := [ [ 6, 525 ], [ 7, 100 ], [ 9, 840 ] ]
  ));
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", fields := [4], dimensions := [6], 
       usemax := [ 4, 3, 5 ], 
       size := 604800, atlasrepnrs := [16], 
       values := [ [ 6, 525 ], [ 8, 315 ], [ 9, 840 ] ]
  ));
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", fields := [4], dimensions := [14], 
       usemax := [ 3, 5, 6 ], 
       size := 604800, atlasrepnrs := [17], 
       values := [ [ 4, 315 ], [ 9, 840 ], [ 11, 1008 ] ]
  ));
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", fields := [4], dimensions := [64], 
       usemax := [ 3, 5, 4 ], 
       size := 604800, atlasrepnrs := [18], 
       values := [ [ 8, 315 ], [ 9, 840 ], [ 12, 525 ] ]
  ));
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", fields := [5], dimensions := [14], 
       usemax := [ 3, 6, 4 ], 
       size := 604800, atlasrepnrs := [19], 
       values := [ [ 4, 315 ], [ 11, 1008 ], [ 12, 525 ] ]
  ));
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", fields := [5], dimensions := [21], 
       usemax := [ 2, 6, 3 ], 
       size := 604800, atlasrepnrs := [20], 
       values := [ [ 3, 280 ], [ 11, 1008 ], [ 12, 315 ] ]
  ));
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", fields := [5], dimensions := [41], 
       usemax := [ 2, 1, 5 ], 
       size := 604800, atlasrepnrs := [21], 
       values := [ [ 3, 280 ], [ 7, 100 ], [ 9, 840 ] ]
  ));
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", fields := [5], dimensions := [70], 
       usemax := [ 4, 6, 1 ], 
       size := 604800, atlasrepnrs := [22], 
       values := [ [ 6, 525 ], [ 11, 1008 ], [ 14, 100 ] ]
  ));
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", fields := [5], dimensions := [85], 
       usemax := [ 6, 5, 7 ], 
       size := 604800, atlasrepnrs := [23], 
       values := [ [ 11, 1008 ], [ 18, 840 ], [ 18, 1800 ] ]
  ));
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", fields := [5], dimensions := [90], 
       usemax := [ 2, 3, 4 ], 
       size := 604800, atlasrepnrs := [24], 
       values := [ [ 3, 280 ], [ 4, 315 ], [ 6, 525 ] ]
  ));
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", fields := [5], dimensions := [175], 
       usemax := [ 2, 4, 1 ], 
       size := 604800, atlasrepnrs := [25], 
       values := [ [ 3, 280 ], [ 6, 525 ], [ 7, 100 ] ]
  ));
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", fields := [5], dimensions := [189], 
       usemax := [ 6, 3, 2 ], 
       size := 604800, atlasrepnrs := [26], 
       values := [ [ 11, 1008 ], [ 12, 315 ], [ 18, 280 ] ]
  ));
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", fields := [5], dimensions := [225], 
       usemax := [ 4, 1, 5 ], 
       size := 604800, atlasrepnrs := [27], 
       values := [ [ 6, 525 ], [ 7, 100 ], [ 9, 840 ] ]
  ));
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", fields := [5], dimensions := [300], 
       usemax := [ 1, 4, 2 ], 
       size := 604800, atlasrepnrs := [28], 
       values := [ [ 6, 100 ], [ 12, 525 ], [ 18, 280 ] ]
  ));
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", fields := [7], dimensions := [36], 
       usemax := [ 1, 3, 4 ], 
       size := 604800, atlasrepnrs := [29], 
       values := [ [ 1, 100 ], [ 4, 315 ], [ 6, 525 ] ]
  ));
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", fields := [7], dimensions := [63], 
       usemax := [ 1, 2, 4 ], 
       size := 604800, atlasrepnrs := [30], 
       values := [ [ 1, 100 ], [ 3, 280 ], [ 6, 525 ] ]
  ));
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", fields := [7], dimensions := [89], 
       usemax := [ 5, 6, 4 ], 
       size := 604800, atlasrepnrs := [31], 
       values := [ [ 9, 840 ], [ 11, 1008 ], [ 12, 525 ] ]
  ));
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", fields := [7], dimensions := [101], 
       usemax := [ 1, 4, 3 ], 
       size := 604800, atlasrepnrs := [32], 
       values := [ [ 6, 100 ], [ 6, 525 ], [ 20, 315 ] ]
  ));
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", fields := [7], dimensions := [124], 
       usemax := [ 4, 5, 6 ], 
       size := 604800, atlasrepnrs := [33], 
       values := [ [ 6, 525 ], [ 9, 840 ], [ 11, 1008 ] ]
  ));
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", fields := [7], dimensions := [126], 
       usemax := [ 2, 4, 5 ], 
       size := 604800, atlasrepnrs := [34], 
       values := [ [ 3, 280 ], [ 6, 525 ], [ 9, 840 ] ]
  ));
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", fields := [7], dimensions := [175], 
       usemax := [ 2, 4, 1 ], 
       size := 604800, atlasrepnrs := [35], 
       values := [ [ 3, 280 ], [ 6, 525 ], [ 7, 100 ] ]
  ));
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", fields := [7], dimensions := [199], 
       usemax := [ 1, 4, 3 ], 
       size := 604800, atlasrepnrs := [36], 
       values := [ [ 6, 100 ], [ 12, 525 ], [ 20, 315 ] ]
  ));
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", fields := [7], dimensions := [336], 
       usemax := [ 4, 5, 1 ], 
       size := 604800, atlasrepnrs := [37], 
       values := [ [ 6, 525 ], [ 9, 840 ], [ 14, 100 ] ]
  ));
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", fields := [9], dimensions := [13], 
       usemax := [ 1, 4, 2 ], 
       size := 604800, atlasrepnrs := [38], 
       values := [ [ 3, 100 ], [ 6, 525 ], [ 9, 280 ] ]
  ));
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", fields := [9], dimensions := [21], 
       usemax := [ 2, 1, 6 ], 
       size := 604800, atlasrepnrs := [39], 
       values := [ [ 3, 280 ], [ 6, 100 ], [ 11, 1008 ] ]
  ));
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", fields := [9], dimensions := [57], 
       usemax := [ 1, 2, 6 ], 
       size := 604800, atlasrepnrs := [40], 
       values := [ [ 3, 100 ], [ 9, 280 ], [ 11, 1008 ] ]
  ));
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", fields := [9], dimensions := [189], 
       usemax := [ 2, 6, 3 ], 
       size := 604800, atlasrepnrs := [41], 
       values := [ [ 9, 280 ], [ 11, 1008 ], [ 12, 315 ] ]
  ));
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", fields := [49], dimensions := [14], 
       usemax := [ 3, 6, 4 ], 
       size := 604800, atlasrepnrs := [42], 
       values := [ [ 4, 315 ], [ 11, 1008 ], [ 12, 525 ] ]
  ));
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", fields := [49], dimensions := [21], 
       usemax := [ 2, 6, 3 ], 
       size := 604800, atlasrepnrs := [43], 
       values := [ [ 3, 280 ], [ 11, 1008 ], [ 12, 315 ] ]
  ));
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", fields := [49], dimensions := [70], 
       usemax := [ 4, 6, 1 ], 
       size := 604800, atlasrepnrs := [44], 
       values := [ [ 6, 525 ], [ 11, 1008 ], [ 14, 100 ] ]
  ));
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", fields := [49], dimensions := [189], 
       usemax := [ 6, 3, 2 ], 
       size := 604800, atlasrepnrs := [45], 
       values := [ [ 11, 1008 ], [ 12, 315 ], [ 18, 280 ] ]
  ));
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", fields := [49], dimensions := [224], 
       usemax := [ 6, 3, 4 ], 
       size := 604800, atlasrepnrs := [46], 
       values := [ [ 11, 1008 ], [ 12, 315 ], [ 12, 525 ] ]
  ));

# Hints for Fi23:
InstallAlmostSimpleHint( "Fi23", "StabChainHint",
  rec( name := "Fi23", fields := [2], dimensions := [782],
       usemax := [ 1 ],
       size := 4089470473293004800, atlasrepnrs := [4],
  ));
InstallAlmostSimpleHint( "Fi23", "StabChainHint",
  rec( name := "Fi23", fields := [2], dimensions := [1494],
       usemax := [ 1 ],
       size := 4089470473293004800, atlasrepnrs := [5],
  ));
InstallAlmostSimpleHint( "Fi23", "StabChainHint",
  rec( name := "Fi23", fields := [3], dimensions := [253],
       usemax := [ 1 ],
       size := 4089470473293004800, atlasrepnrs := [6],
  ));
InstallAlmostSimpleHint( "Fi23", "StabChainHint",
  rec( name := "Fi23", fields := [3], dimensions := [528],
       usemax := [ 1 ],
       size := 4089470473293004800, atlasrepnrs := [7],
  ));
InstallAlmostSimpleHint( "Fi23", "StabChainHint",
  rec( name := "Fi23", fields := [5], dimensions := [782],
       usemax := [ 1 ],
       size := 4089470473293004800, atlasrepnrs := [8],
  ));
InstallAlmostSimpleHint( "Fi23", "StabChainHint",
  rec( name := "Fi23", fields := [7], dimensions := [782],
       usemax := [ 1 ],
       size := 4089470473293004800, atlasrepnrs := [9],
  ));
InstallAlmostSimpleHint( "Fi23", "StabChainHint",
  rec( name := "Fi23", fields := [11], dimensions := [782],
       usemax := [ 1 ],
       size := 4089470473293004800, atlasrepnrs := [10],
  ));
InstallAlmostSimpleHint( "Fi23", "StabChainHint",
  rec( name := "Fi23", fields := [13], dimensions := [782],
       usemax := [ 1 ],
       size := 4089470473293004800, atlasrepnrs := [11],
  ));
InstallAlmostSimpleHint( "Fi23", "StabChainHint",
  rec( name := "Fi23", fields := [17], dimensions := [782],
       usemax := [ 1 ],
       size := 4089470473293004800, atlasrepnrs := [12],
  ));
InstallAlmostSimpleHint( "Fi23", "StabChainHint",
  rec( name := "Fi23", fields := [23], dimensions := [782],
       usemax := [ 1 ],
       size := 4089470473293004800, atlasrepnrs := [13],
  ));

InstallAlmostSimpleHint( "HS", "LowIndexHint",
  rec( characteristics := [2], dimensiondivs := [20,56,132,518,896,1000,1408],
       elordersstart := [11], numberrandgens := 2, tries := 10,
       triesforgens := 300,
       subspacedims := [1,10,34,70], orblenlimit := 100 ) );
InstallAlmostSimpleHint( "HS", "LowIndexHint",
  rec( characteristics := [3], dimensiondivs := [22,77,154],  # more?
       elordersstart := [11], numberrandgens := 2, tries := 10,
       triesforgens := 300,
       subspacedims := [1,21,45,49,55,99], orblenlimit := 100 ) );

# Generic hints:
InstallAlmostSimpleHint( "J1", "StabChainHint",
  rec( name := "J1", usemax := [ 1, 2, 3, 4, 5, 6, 7 ],
       size := 175560,
  ));
InstallAlmostSimpleHint( "M11", "StabChainHint",
  rec( name := "M11", usemax := [ 1, 2, 3, 4, 5 ],
       size := 7920,
  ));
InstallAlmostSimpleHint( "M12", "StabChainHint",
  rec( name := "M12", usemax := [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11 ],
       size := 95040,
  ));
InstallAlmostSimpleHint( "J3", "StabChainHint",
  rec( name := "J3", usemax := [ 1, 2, 3, 4, 5, 6, 7, 8, 9 ],
       size := 50232960,
  ));
InstallAlmostSimpleHint( "M23", "StabChainHint",
  rec( name := "M23", usemax := [ 1, 2, 3, 4, 5, 6, 7 ],
       size := 10200960,
  ));
InstallAlmostSimpleHint( "M22", "StabChainHint",
  rec( name := "M22", usemax := [ 1, 2, 3, 4, 5, 6, 7, 8 ],
       size := 443520,
  ));
InstallAlmostSimpleHint( "J2", "StabChainHint",
  rec( name := "J2", usemax := [ 1, 2, 3, 4, 5, 6, 7, 8, 9 ],
       size := 604800,
  ));
InstallAlmostSimpleHint( "He", "StabChainHint",
  rec( name := "He", usemax := [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11 ],
       size := 4030387200,
  ));
InstallAlmostSimpleHint( "Ru", "StabChainHint",
  rec( name := "Ru", usemax := [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 
  14, 15 ],
       size := 145926144000,
  ));
InstallAlmostSimpleHint( "HS", "StabChainHint",
  rec( name := "HS", usemax := [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12 ],
       size := 44352000,
  ));
InstallAlmostSimpleHint( "M24", "StabChainHint",
  rec( name := "M24", usemax := [ 1, 2, 3, 4, 5, 6, 7, 8, 9 ],
       size := 244823040,
  ));
InstallAlmostSimpleHint( "ON", "StabChainHint",
  rec( name := "ON", usemax := [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13 ],
       size := 460815505920,
  ));
InstallAlmostSimpleHint( "McL", "StabChainHint",
  rec( name := "McL", usemax := [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12 ],
       size := 898128000,
  ));
InstallAlmostSimpleHint( "Co3", "StabChainHint",
  rec( name := "Co3", usemax := [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 
  14 ],
       size := 495766656000,
  ));
InstallAlmostSimpleHint( "Co2", "StabChainHint",
  rec( name := "Co2", usemax := [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11 ],
       size := 42305421312000,
  ));
InstallAlmostSimpleHint( "Suz", "StabChainHint",
  rec( name := "Suz", usemax := [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 
  14, 15, 16, 17 ],
       size := 448345497600,
  ));
InstallAlmostSimpleHint( "Fi22", "StabChainHint",
  rec( name := "Fi22", usemax := [ 1,2,3,4,5,6,7,8,9,10,11,12,13,14 ],
       size := 64561751654400,
  ));
InstallAlmostSimpleHint( "Co1", "StabChainHint",
  rec( name := "Co1", usemax := [ 1, 2, 3, 4, 5, 6 ],
       size := 4157776806543360000,
  ));
InstallAlmostSimpleHint( "Fi23", "StabChainHint",
  rec( name := "Fi23", usemax := [ 1, 2, 3, 4, 5, 6, 9, 10, 13, 14 ],
       size := 4089470473293004800,
  ));
InstallAlmostSimpleHint( "M12.2", "StabChainHint",
  rec( name := "M12.2", usemax := [ 2, 3, 4, 5, 6, 7, 8, 9 ],
       size := 190080,
  ));
InstallAlmostSimpleHint( "M22.2", "StabChainHint",
  rec( name := "M22.2", usemax := [ 1, 2, 3, 4, 5, 6, 7 ],
       size := 887040,
  ));
InstallAlmostSimpleHint( "HS.2", "StabChainHint",
  rec( name := "HS.2", usemax := [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 ],
       size := 88704000,
  ));
InstallAlmostSimpleHint( "J2.2", "StabChainHint",
  rec( name := "J2.2", usemax := [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 ],
       size := 1209600,
  ));
InstallAlmostSimpleHint( "McL.2", "StabChainHint",
  rec( name := "McL.2", usemax := [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 ],
       size := 1796256000,
  ));
InstallAlmostSimpleHint( "Suz.2", "StabChainHint",
  rec( name := "Suz.2", usemax := [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 
  13, 14, 15, 16 ],
       size := 896690995200,
  ));
InstallAlmostSimpleHint( "He.2", "StabChainHint",
  rec( name := "He.2", usemax := [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12 ],
       size := 8060774400,
  ));
InstallAlmostSimpleHint( "Fi22.2", "StabChainHint",
  rec( name := "Fi22.2", usemax := [ 1, 2, 13 ],
       size := 129123503308800,
  ));
InstallAlmostSimpleHint( "ON.2", "StabChainHint",
  rec( name := "ON.2", usemax := [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 ],
       size := 921631011840,
  ));
InstallAlmostSimpleHint( "J3.2", "StabChainHint",
  rec( name := "J3.2", usemax := [ 1, 2, 3, 4, 5, 6, 7, 8, 9 ],
       size := 100465920,
  ));
InstallAlmostSimpleHint( "2F4(2)'", "StabChainHint",
  rec( name := "2F4(2)'", usemax := [ 1, 2, 3, 4, 5, 6, 7, 8 ],
       size := 17971200,
  ));
InstallAlmostSimpleHint( "2F4(2)'.2", "StabChainHint",
  rec( name := "2F4(2)'.2", usemax := [ 1 ],  # not more avaiable as of now!
       size := 35942400,
  ));
# No hints there for Fi24' since we do not have the maximal subgroups!
InstallAlmostSimpleHint( "Fi24'.2", "StabChainHint",
  rec( name := "Fi24'.2", usemax := [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 
  13, 14, 15, 16, 17, 18, 19, 20, 21 ],
       size := 2510411418381323442585600,
  ));
InstallAlmostSimpleHint( "HN", "StabChainHint",
  rec( name := "HN", usemax := [ 1,2,3,4,5,6,7,10,11,12,14 ],
       size := 273030912000000,
  ));
InstallAlmostSimpleHint( "HN.2", "StabChainHint",
  rec( name := "HN", usemax := [ 1..13 ],
       size := 546061824000000,
  ));
InstallAlmostSimpleHint( "J4", "StabChainHint",
  rec( name := "J4", usemax := [ 1..13 ],
       size := 86775571046077562880,
  ));
InstallAlmostSimpleHint( "Ly", "StabChainHint",
  rec( name := "Ly", usemax := [ 1..9 ],
       size := 51765179004000000,
  ));
InstallAlmostSimpleHint( "Th", "StabChainHint",
  rec( name := "Th", usemax := [ 1..16 ],
       size := 90745943887872000,
  ));
# No hints for B and M since we won't see them!

# This is for the released AtlasRep package:
if not(IsBound(AGR_TablesOfContents)) then
    AGR_TablesOfContents := fail;
    AGR_InfoForName := fail;
fi;
RECOG.PrintGenericStabChainHint := function ( n )
    local S,g,gens,nn,toc,tocs;
    tocs := AGR_TablesOfContents( "all" );
    nn := AGR_InfoForName( n )[2];
    toc := tocs[1].(nn);
    gens := AtlasGenerators( n, 1 ).generators;
    g := Group( gens );
    S := StabilizerChain( g );
    Print( "InstallAlmostSimpleHint( \"", n, "\", \"StabChainHint\",\n" );
    Print( "  rec( name := \"", n, "\", usemax := " );
    Print( Set( List( toc.maxes, x->x[2] ) ) );
    Print( ",\n       size := ", Size( S ), ",\n  ));\n" );
end;

# dimensions optionally
# subspacedims there or not
# elordersstart unbound ==> start with empty generator list
# if numberrandgens = "logd" then it will use LogInt(d,2)
# if triesforgens = "Xd" then it will use X * d (X a number as a string)
# if orblenlimit = "Xd" then it will use X * d (X a number as a string)
# L2 hint with doing the decision on the fly
#   depending on the ppd-Properties of L2(p)
# This means:
#   rec( numberrandgens := "logd", tries := 10, triesforgens := "1d",
#        orblenlimit := "4d" )
# is the standard low index.

InstallAlmostSimpleHint( "L2(31)", "LowIndexHint",
  rec( characteristics := [31], dimensions := [1,2,3],
       elordersstart := [31], numberrandgens := 2, tries := 1,
       triesforgens := 100, orblenlimit := 32 ) );

InstallGlobalFunction( LookupHintForSimple, 
  function(ri,G,name)
    local dim,f,hi,j,p,q;
    Info(InfoRecog,2,"Looking up hints for ",name,"...");
    if IsBound(RECOG.AlmostSimpleHints.(name)) then
        j := 1;
        hi := RECOG.AlmostSimpleHints.(name);
        f := ri!.field;
        p := Characteristic(f);
        q := Size(f);
        dim := ri!.dimension;
        while j <= Length(hi) do
            if (not(IsBound(hi[j].characteristics)) or 
                p in hi[j].characteristics) and 
               (not(IsBound(hi[j].fields)) or
                q in hi[j].fields) and
               (not(IsBound(hi[j].dimensiondivs)) or 
                ForAny(hi[j].dimensiondivs,d->dim mod d = 0)) and
               (not(IsBound(hi[j].dimensions)) or
                dim in hi[j].dimensions) then
                # This hint is applicable!
                if hi[j].type = "LowIndexHint" then
                    return DoHintedLowIndex(ri,G,hi[j]);
                elif hi[j].type = "StabChainHint" then
                    return DoHintedStabChain(ri,G,hi[j]);
                # Put other hint types here!
                fi;
            fi;
            j := j + 1;
        od;
    fi;
    Info(InfoRecog,2,"No hint worked, giving up.");
    return fail;
  end );

RECOG.grouplist:=
[[3,2,["l",2,5]],[4,3,["l",2,7]],[5,3,["l",2,4]],
[5,3,["l",2,5]],[5,3,["s",4,2]],[5,4,["l",2,9]],
[5,4,["s",4,3]],[6,5,["l",2,11]],[6,5,["s",4,3]],
[7,2,["2G2",3]],[7,3,["2G2",3]],[7,3,["G2",2]],
[7,3,["l",3,2]],[7,4,["G2",2]],[7,4,["l",2,7]],
[7,4,["l",3,2]],[7,5,["l",3,4]],[7,6,["G2",2]],
[7,6,["l",2,13]],[8,7,["G2",2]],[8,7,["u",3,3]],
[8,7,["u",3,5]],[8,7,["u",4,3]],[9,5,["s",4,3]],
[9,5,["u",4,2]],[9,6,["s",4,3]],[9,6,["u",4,2]],
[9,7,["2G2",3]],[9,7,["l",2,8]],[9,8,["l",2,17]],
[9,8,["u",4,3]],[10,8,["u",3,5]],[10,9,["l",2,19]],
[11,6,["l",2,11]],[12,5,["s",4,3]],[12,6,["s",4,3]],
[12,7,["G2",2]],[12,8,["G2",2]],[12,8,["u",3,3]],
[12,8,["u",4,3]],[12,9,["s",4,3]],[12,9,["u",4,2]],
[12,9,["u",4,3]],[12,11,["l",2,23]],[13,5,["2F4",2]],
[13,6,["2F4",2]],[13,7,["2B2",8]],[13,7,["l",2,13]],
[13,8,["l",3,3]],[13,8,["G2",3]],[13,8,["2F4",2]],
[13,9,["G2",3]],[13,10,["2F4",2]],[13,12,["2F4",2]],
[13,12,["G2",3]],[13,12,["l",2,25]],[13,12,["s",4,5]],
[14,13,["l",2,27]],[15,7,["l",4,2]],[15,9,["o+",8,2]],
[15,9,["s",6,2]],[15,10,["o+",8,2]],[15,10,["s",6,2]],
[15,11,["u",5,2]],[15,11,["u",6,2]],[15,12,["o+",8,2]],
[15,12,["s",6,2]],[15,12,["u",5,2]],[15,12,["u",6,2]],
[15,13,["s",4,5]],[15,13,["u",3,4]],[15,14,["l",2,29]],
[16,13,["2F4",2]],[16,15,["l",2,31]],[17,9,["l",2,17]],
[17,15,["l",2,16]],[17,15,["s",4,4]],[18,15,["u",5,2]],
[18,15,["u",6,2]],[19,10,["l",2,19]],[19,16,["l",3,7]],
[19,18,["l",2,37]],[20,13,["l",4,3]],[20,13,["s",4,5]],
[20,14,["o",7,3]],[20,14,["o+",8,3]],[20,14,["s",6,3]],
[20,15,["o",7,3]],[20,15,["o+",8,3]],[20,15,["s",4,5]],
[20,15,["s",6,3]],[20,18,["o",7,3]],[20,18,["o+",8,3]],
[20,18,["s",6,3]],[21,13,["3D4",2]],[21,14,["3D4",2]],
[21,15,["G2",4]],[21,17,["F4",2]],[21,17,["o-",8,2]],
[21,17,["s",8,2]],[21,18,["3D4",2]],[21,18,["F4",2]],
[21,18,["s",8,2]],[21,19,["u",3,8]],[21,20,["F4",2]],
[21,20,["l",2,41]],[21,20,["s",8,2]],[22,21,["l",2,43]],
[23,12,["l",2,23]],[24,20,["s",6,3]],[24,21,["F4",2]],
[24,21,["s",8,2]],[24,23,["l",2,47]],[25,24,["l",2,49]],
[25,24,["s",4,7]],[27,26,["l",2,53]],[28,21,["3D4",2]],
[28,21,["F4",2]],[28,24,["F4",2]],[28,25,["s",4,7]],
[29,15,["l",2,29]],[30,13,["s",4,5]],[30,15,["s",4,5]],
[30,20,["s",4,5]],[30,20,["s",6,3]],[30,21,["F4",2]],
[30,21,["o-",8,2]],[30,21,["s",8,2]],[30,24,["F4",2]],
[30,24,["s",6,3]],[30,24,["s",8,2]],[30,28,["F4",2]],
[30,29,["l",2,59]],[31,16,["l",2,31]],[31,21,["l",5,2]],
[31,24,["l",3,5]],[31,24,["G2",5]],[31,25,["G2",5]],
[31,30,["G2",5]],[31,30,["l",2,61]],[33,31,["l",2,32]],
[34,33,["l",2,67]],[35,33,["2E6",2]],[35,33,["o-",10,2]],
[36,20,["s",6,3]],[36,24,["s",6,3]],[36,30,["s",6,3]],
[36,35,["l",2,71]],[37,19,["l",2,37]],[37,26,["2G2",27]],
[37,36,["l",2,73]],[39,31,["l",4,5]],[40,37,["u",3,11]],
[40,39,["l",2,79]],[41,21,["l",2,41]],[41,31,["2B2",32]],
[41,40,["l",2,81]],[41,40,["s",4,9]],[42,25,["s",4,7]],
[42,28,["s",4,7]],[42,41,["l",2,83]],[43,22,["l",2,43]],
[44,40,["u",3,11]],[45,44,["l",2,89]],[47,24,["l",2,47]],
[48,43,["u",3,7]],[49,48,["l",2,97]],[51,45,["o+",10,2]],
[51,45,["s",10,2]],[51,50,["l",2,101]],[52,41,["o",9,3]],
[52,41,["o-",8,3]],[52,41,["s",8,3]],[52,42,["o",9,3]],
[52,42,["s",8,3]],[52,45,["o",9,3]],[52,45,["s",8,3]],
[52,51,["l",2,103]],[53,27,["l",2,53]],
[54,53,["l",2,107]],[55,54,["l",2,109]],
[56,25,["s",4,7]],[56,28,["s",4,7]],[56,42,["s",4,7]],
[56,48,["u",3,7]],[57,48,["G2",7]],[57,49,["G2",7]],
[57,56,["G2",7]],[57,56,["l",2,113]],[59,30,["l",2,59]],
[60,51,["o+",10,2]],[60,51,["s",10,2]],[60,52,["o",9,3]],
[60,52,["o-",8,3]],[60,52,["s",8,3]],[61,31,["l",2,61]],
[61,56,["l",3,13]],[61,60,["l",2,121]],
[61,60,["s",4,11]],[63,31,["l",6,2]],[63,45,["u",7,2]],
[63,52,["u",4,5]],[63,60,["u",4,5]],[63,60,["u",7,2]],
[63,62,["l",2,125]],[64,63,["l",2,127]],
[65,51,["u",4,4]],[65,51,["u",5,4]],[65,63,["l",2,64]],
[65,63,["s",4,8]],[66,61,["s",4,11]],[66,63,["u",7,2]],
[66,65,["l",2,131]],[67,34,["l",2,67]],
[69,68,["l",2,137]],[70,69,["l",2,139]],
[71,36,["l",2,71]],[72,52,["s",8,3]],[72,60,["s",8,3]],
[73,37,["l",2,73]],[73,63,["l",3,8]],[73,63,["G2",8]],
[75,74,["l",2,149]],[76,75,["l",2,151]],
[78,52,["s",8,3]],[78,60,["s",8,3]],[78,63,["o",7,5]],
[78,63,["s",6,5]],[78,65,["o",7,5]],[78,65,["s",6,5]],
[78,72,["s",8,3]],[79,40,["l",2,79]],[79,78,["l",2,157]],
[80,61,["u",5,3]],[80,65,["o-",10,3]],[80,73,["u",3,9]],
[82,81,["l",2,163]],[83,42,["l",2,83]],[84,52,["s",8,3]],
[84,60,["s",8,3]],[84,72,["s",8,3]],[84,78,["s",8,3]],
[84,80,["o-",10,3]],[84,80,["u",5,3]],
[84,83,["l",2,167]],[85,63,["l",4,4]],[85,65,["s",6,4]],
[85,84,["l",2,169]],[85,84,["s",4,13]],[86,75,["u",4,7]],
[86,84,["u",4,7]],[87,86,["l",2,173]],[89,45,["l",2,89]],
[90,52,["s",8,3]],[90,60,["s",8,3]],[90,72,["s",8,3]],
[90,78,["s",8,3]],[90,84,["s",8,3]],[90,89,["l",2,179]],
[91,80,["l",3,9]],[91,80,["G2",9]],[91,85,["l",3,16]],
[91,85,["s",4,13]],[91,90,["l",2,181]],
[93,65,["o-",12,2]],[93,84,["o-",12,2]],[93,91,["E6",2]],
[96,91,["u",3,17]],[96,95,["l",2,191]],
[97,49,["l",2,97]],[97,96,["l",2,193]],
[99,98,["l",2,197]],[100,99,["l",2,199]],
[101,51,["l",2,101]],[102,93,["o-",12,2]],
[102,96,["u",3,17]],[103,52,["l",2,103]],
[104,73,["3D4",3]],[104,78,["3D4",3]],[104,82,["F4",3]],
[104,84,["3D4",3]],[104,84,["F4",3]],[104,90,["F4",3]],
[105,85,["o+",12,2]],[105,93,["s",12,2]],
[105,102,["s",12,2]],[106,105,["l",2,211]],
[107,54,["l",2,107]],[109,55,["l",2,109]],
[109,91,["2F4",8]],[110,61,["s",4,11]],
[110,66,["s",4,11]],[112,111,["l",2,223]],
[113,57,["l",2,113]],[114,113,["l",2,227]],
[115,114,["l",2,229]],[117,116,["l",2,233]],
[120,78,["s",6,5]],[120,104,["F4",3]],
[120,105,["s",12,2]],[120,119,["l",2,239]],
[121,104,["l",5,3]],[121,120,["l",2,241]],
[122,91,["u",6,3]],[122,120,["u",6,3]],
[122,121,["l",2,243]],[126,93,["E6",2]],
[126,125,["l",2,251]],[127,64,["l",2,127]],
[127,105,["l",7,2]],[127,120,["l",3,19]],
[129,99,["u",8,2]],[129,99,["u",9,2]],
[129,126,["u",8,2]],[129,126,["u",9,2]],
[129,127,["l",2,128]],[129,128,["l",2,257]],
[130,78,["s",6,5]],[130,120,["s",6,5]],
[131,66,["l",2,131]],[132,61,["s",4,11]],
[132,66,["s",4,11]],[132,110,["s",4,11]],
[132,129,["u",8,2]],[132,129,["u",9,2]],
[132,131,["l",2,263]],[133,120,["l",3,11]],
[133,120,["G2",11]],[133,121,["G2",11]],
[133,132,["G2",11]],[135,134,["l",2,269]],
[136,135,["l",2,271]],[137,69,["l",2,137]],
[139,70,["l",2,139]],[139,138,["l",2,277]],
[141,140,["l",2,281]],[142,141,["l",2,283]],
[145,127,["2B2",128]],[145,144,["l",2,289]],
[145,144,["s",4,17]],[147,146,["l",2,293]],
[149,75,["l",2,149]],[151,76,["l",2,151]],
[153,145,["s",4,17]],[154,153,["l",2,307]],
[156,78,["o+",8,5]],[156,85,["s",4,13]],
[156,91,["s",4,13]],[156,155,["l",2,311]],
[157,79,["l",2,157]],[157,156,["l",2,313]],
[159,158,["l",2,317]],[163,82,["l",2,163]],
[164,140,["o+",10,3]],[164,140,["o",11,3]],
[164,140,["s",10,3]],[164,156,["o+",10,3]],
[164,156,["o",11,3]],[164,156,["s",10,3]],
[166,165,["l",2,331]],[167,84,["l",2,167]],
[168,157,["u",3,13]],[169,168,["l",2,337]],
[172,171,["l",2,343]],[173,87,["l",2,173]],
[174,173,["l",2,347]],[175,174,["l",2,349]],
[176,169,["u",3,23]],[177,176,["l",2,353]],
[179,90,["l",2,179]],[180,164,["o",11,3]],
[180,164,["s",10,3]],[180,179,["l",2,359]],
[181,91,["l",2,181]],[181,180,["l",2,361]],
[181,180,["s",4,19]],[182,85,["s",4,13]],
[182,91,["s",4,13]],[182,121,["l",6,3]],
[182,156,["s",4,13]],[182,168,["u",3,13]],
[183,168,["G2",13]],[183,169,["G2",13]],[183,182,["G2",13]],
[184,176,["u",3,23]],[184,183,["l",2,367]],
[187,186,["l",2,373]],[190,181,["s",4,19]],
[190,189,["l",2,379]],[191,96,["l",2,191]],
[192,191,["l",2,383]],[193,97,["l",2,193]],
[195,165,["o+",14,2]],[195,186,["o+",14,2]],
[195,194,["l",2,389]],[197,99,["l",2,197]],
[199,100,["l",2,199]],[199,198,["l",2,397]],
[200,171,["l",4,7]],[200,172,["o",7,7]],
[200,172,["s",6,7]],[200,175,["o",7,7]],
[200,175,["s",6,7]],[201,200,["l",2,401]],
[204,195,["o+",14,2]],[205,182,["l",4,9]],
[205,204,["l",2,409]],[210,209,["l",2,419]],
[211,106,["l",2,211]],[211,210,["l",2,421]],
[216,215,["l",2,431]],[217,208,["l",3,25]],
[217,216,["l",2,433]],[220,219,["l",2,439]],
[222,221,["l",2,443]],[223,112,["l",2,223]],
[225,224,["l",2,449]],[227,114,["l",2,227]],
[229,115,["l",2,229]],[229,228,["l",2,457]],
[231,230,["l",2,461]],[232,231,["l",2,463]],
[233,117,["l",2,233]],[234,164,["s",10,3]],
[234,180,["s",10,3]],[234,233,["l",2,467]],
[239,120,["l",2,239]],[240,164,["s",10,3]],
[240,180,["s",10,3]],[240,234,["s",10,3]],
[240,239,["l",2,479]],[241,121,["l",2,241]],
[244,243,["l",2,487]],[246,164,["s",10,3]],
[246,180,["s",10,3]],[246,234,["s",10,3]],
[246,240,["s",10,3]],[246,245,["l",2,491]],
[250,249,["l",2,499]],[251,126,["l",2,251]],
[252,164,["s",10,3]],[252,180,["s",10,3]],
[252,234,["s",10,3]],[252,240,["s",10,3]],
[252,246,["s",10,3]],[252,251,["l",2,503]],
[255,85,["o+",8,4]],[255,155,["o-",14,2]],
[255,195,["s",14,2]],[255,204,["s",14,2]],
[255,210,["o-",14,2]],[255,210,["s",14,2]],
[255,217,["E7",2]],[255,217,["l",8,2]],
[255,241,["u",3,16]],[255,252,["E7",2]],
[255,254,["l",2,509]],[257,129,["l",2,257]],
[257,255,["l",2,256]],[257,255,["s",4,16]],
[260,205,["o+",12,3]],[261,260,["l",2,521]],
[262,261,["l",2,523]],[263,132,["l",2,263]],
[265,264,["l",2,529]],[265,264,["s",4,23]],
[269,135,["l",2,269]],[271,136,["l",2,271]],
[271,242,["2G2",243]],[271,270,["l",2,541]],
[272,145,["s",4,17]],[272,153,["s",4,17]],
[273,255,["G2",16]],[274,273,["l",2,547]],
[276,265,["s",4,23]],[277,139,["l",2,277]],
[279,278,["l",2,557]],[280,271,["u",3,29]],
[281,141,["l",2,281]],[282,281,["l",2,563]],
[283,142,["l",2,283]],[285,284,["l",2,569]],
[286,285,["l",2,571]],[289,288,["l",2,577]],
[290,280,["u",3,29]],[293,147,["l",2,293]],
[294,293,["l",2,587]],[297,296,["l",2,593]],
[300,299,["l",2,599]],[301,300,["l",2,601]],
[304,303,["l",2,607]],[306,145,["s",4,17]],
[306,153,["s",4,17]],[306,272,["s",4,17]],
[307,154,["l",2,307]],[307,288,["l",3,17]],
[307,288,["G2",17]],[307,289,["G2",17]],
[307,306,["G2",17]],[307,306,["l",2,613]],
[309,308,["l",2,617]],[310,309,["l",2,619]],
[311,156,["l",2,311]],[313,157,["l",2,313]],
[313,312,["l",2,625]],[313,312,["s",4,25]],
[315,241,["3D4",4]],[315,257,["F4",4]],
[315,257,["o-",8,4]],[315,257,["s",8,4]],
[316,315,["l",2,631]],[317,159,["l",2,317]],
[321,320,["l",2,641]],[322,321,["l",2,643]],
[324,323,["l",2,647]],[327,326,["l",2,653]],
[330,329,["l",2,659]],[331,166,["l",2,331]],
[331,320,["l",3,31]],[331,330,["l",2,661]],
[333,305,["u",4,11]],[333,330,["u",4,11]],
[336,200,["s",6,7]],[337,169,["l",2,337]],
[337,336,["l",2,673]],[339,338,["l",2,677]],
[341,315,["l",5,4]],[341,331,["u",3,32]],
[342,181,["s",4,19]],[342,190,["s",4,19]],
[342,341,["l",2,683]],[346,345,["l",2,691]],
[347,174,["l",2,347]],[349,175,["l",2,349]],
[350,200,["s",6,7]],[350,336,["s",6,7]],
[351,350,["l",2,701]],[353,177,["l",2,353]],
[355,354,["l",2,709]],[359,180,["l",2,359]],
[360,343,["u",3,19]],[360,359,["l",2,719]],
[364,363,["l",2,727]],[365,328,["u",4,9]],
[365,364,["l",2,729]],[365,364,["s",4,27]],
[367,184,["l",2,367]],[367,366,["l",2,733]],
[370,369,["l",2,739]],[372,313,["o",9,5]],
[372,313,["o-",8,5]],[372,313,["s",8,5]],
[372,315,["o",9,5]],[372,315,["s",8,5]],
[372,371,["l",2,743]],[373,187,["l",2,373]],
[376,375,["l",2,751]],[379,190,["l",2,379]],
[379,378,["l",2,757]],[380,181,["s",4,19]],
[380,190,["s",4,19]],[380,342,["s",4,19]],
[380,360,["u",3,19]],[381,315,["o-",16,2]],
[381,360,["G2",19]],[381,361,["G2",19]],
[381,372,["o-",16,2]],[381,380,["G2",19]],
[381,380,["l",2,761]],[383,192,["l",2,383]],
[385,384,["l",2,769]],[387,386,["l",2,773]],
[389,195,["l",2,389]],[390,372,["o",9,5]],
[390,372,["o-",8,5]],[390,372,["s",8,5]],
[390,381,["o-",16,2]],[394,393,["l",2,787]],
[397,199,["l",2,397]],[399,398,["l",2,797]],
[401,201,["l",2,401]],[405,404,["l",2,809]],
[406,405,["l",2,811]],[409,205,["l",2,409]],
[410,365,["o",7,9]],[410,365,["s",6,9]],
[411,410,["l",2,821]],[412,411,["l",2,823]],
[414,413,["l",2,827]],[415,414,["l",2,829]],
[419,210,["l",2,419]],[420,419,["l",2,839]],
[421,211,["l",2,421]],[421,420,["l",2,841]],
[421,420,["s",4,29]],[427,426,["l",2,853]],
[429,428,["l",2,857]],[430,429,["l",2,859]],
[431,216,["l",2,431]],[432,431,["l",2,863]],
[433,217,["l",2,433]],[435,421,["s",4,29]],
[439,220,["l",2,439]],[439,438,["l",2,877]],
[441,440,["l",2,881]],[442,441,["l",2,883]],
[443,222,["l",2,443]],[444,443,["l",2,887]],
[449,225,["l",2,449]],[454,453,["l",2,907]],
[455,341,["l",6,4]],[456,455,["l",2,911]],
[457,229,["l",2,457]],[460,459,["l",2,919]],
[461,231,["l",2,461]],[463,232,["l",2,463]],
[465,357,["o+",16,2]],[465,381,["s",16,2]],
[465,390,["s",16,2]],[465,408,["s",16,2]],
[465,420,["o+",16,2]],[465,420,["s",16,2]],
[465,464,["l",2,929]],[467,234,["l",2,467]],
[469,456,["l",3,37]],[469,468,["l",2,937]],
[471,470,["l",2,941]],[474,473,["l",2,947]],
[477,476,["l",2,953]],[479,240,["l",2,479]],
[481,480,["l",2,961]],[481,480,["s",4,31]],
[484,365,["o-",12,3]],[484,410,["o",13,3]],
[484,410,["s",12,3]],[484,420,["o",13,3]],
[484,420,["s",12,3]],[484,468,["o",13,3]],
[484,468,["s",12,3]],[484,483,["l",2,967]],
[486,485,["l",2,971]],[487,244,["l",2,487]],
[489,488,["l",2,977]],[491,246,["l",2,491]],
[492,484,["o",13,3]],[492,484,["o-",12,3]],
[492,484,["s",12,3]],[492,491,["l",2,983]],
[496,481,["s",4,31]],[496,495,["l",2,991]],
[499,250,["l",2,499]],[499,498,["l",2,997]],
[503,252,["l",2,503]],[505,504,["l",2,1009]],
[506,265,["s",4,23]],[506,276,["s",4,23]],
[507,506,["l",2,1013]],[509,255,["l",2,509]],
[510,465,["o+",16,2]],[510,465,["s",16,2]],
[510,509,["l",2,1019]],[511,465,["l",9,2]],
[511,510,["l",2,1021]],[513,387,["u",10,2]],
[513,455,["u",4,8]],[513,510,["u",10,2]],
[513,511,["l",2,512]],[516,513,["u",10,2]],
[516,515,["l",2,1031]],[517,516,["l",2,1033]],
[520,519,["l",2,1039]],[521,261,["l",2,521]],
[523,262,["l",2,523]],[525,524,["l",2,1049]],
[526,525,["l",2,1051]],[531,530,["l",2,1061]],
[532,531,["l",2,1063]],[535,534,["l",2,1069]],
[541,271,["l",2,541]],[544,543,["l",2,1087]],
[545,511,["2B2",512]],[546,545,["l",2,1091]],
[547,274,["l",2,547]],[547,546,["l",2,1093]],
[549,548,["l",2,1097]],[552,265,["s",4,23]],
[552,276,["s",4,23]],[552,506,["s",4,23]],
[552,551,["l",2,1103]],[553,528,["l",3,23]],
[553,528,["G2",23]],[553,529,["G2",23]],
[553,552,["G2",23]],[555,554,["l",2,1109]],
[557,279,["l",2,557]],[559,558,["l",2,1117]],
[560,547,["u",3,41]],[562,561,["l",2,1123]],
[563,282,["l",2,563]],[565,564,["l",2,1129]],
[569,285,["l",2,569]],[571,286,["l",2,571]],
[574,560,["u",3,41]],[576,575,["l",2,1151]],
[577,289,["l",2,577]],[577,576,["l",2,1153]],
[582,581,["l",2,1163]],[585,511,["l",4,8]],
[585,513,["s",6,8]],[586,585,["l",2,1171]],
[587,294,["l",2,587]],[591,590,["l",2,1181]],
[593,297,["l",2,593]],[594,593,["l",2,1187]],
[595,549,["l",4,13]],[597,596,["l",2,1193]],
[599,300,["l",2,599]],[600,300,["o+",8,7]],
[601,301,["l",2,601]],[601,600,["l",2,1201]],
[607,304,["l",2,607]],[607,606,["l",2,1213]],
[609,608,["l",2,1217]],[612,611,["l",2,1223]],
[613,307,["l",2,613]],[615,614,["l",2,1229]],
[616,615,["l",2,1231]],[617,309,["l",2,617]],
[619,310,["l",2,619]],[619,618,["l",2,1237]],
[620,372,["s",8,5]],[620,390,["s",8,5]],
[624,521,["u",5,5]],[624,521,["u",6,5]],
[624,601,["u",3,25]],[625,624,["l",2,1249]],
[630,372,["s",8,5]],[630,390,["s",8,5]],
[630,620,["s",8,5]],[630,624,["u",5,5]],
[630,624,["u",6,5]],[630,629,["l",2,1259]],
[631,316,["l",2,631]],[631,616,["l",3,43]],
[639,638,["l",2,1277]],[640,639,["l",2,1279]],
[641,321,["l",2,641]],[642,641,["l",2,1283]],
[643,322,["l",2,643]],[645,644,["l",2,1289]],
[646,645,["l",2,1291]],[647,324,["l",2,647]],
[649,648,["l",2,1297]],[651,511,["E8",2]],
[651,624,["G2",25]],[651,650,["l",2,1301]],
[652,651,["l",2,1303]],[653,327,["l",2,653]],
[654,653,["l",2,1307]],[659,330,["l",2,659]],
[660,659,["l",2,1319]],[661,331,["l",2,661]],
[661,660,["l",2,1321]],[664,663,["l",2,1327]],
[666,665,["l",2,1331]],[673,337,["l",2,673]],
[677,339,["l",2,677]],[681,680,["l",2,1361]],
[683,342,["l",2,683]],[684,683,["l",2,1367]],
[685,684,["l",2,1369]],[685,684,["s",4,37]],
[687,686,["l",2,1373]],[691,346,["l",2,691]],
[691,690,["l",2,1381]],[700,699,["l",2,1399]],
[701,351,["l",2,701]],[703,685,["s",4,37]],
[705,704,["l",2,1409]],[709,355,["l",2,709]],
[712,711,["l",2,1423]],[714,713,["l",2,1427]],
[715,714,["l",2,1429]],[717,716,["l",2,1433]],
[719,360,["l",2,719]],[720,484,["s",12,3]],
[720,492,["s",12,3]],[720,719,["l",2,1439]],
[724,723,["l",2,1447]],[726,484,["s",12,3]],
[726,492,["s",12,3]],[726,720,["s",12,3]],
[726,725,["l",2,1451]],[727,364,["l",2,727]],
[727,726,["l",2,1453]],[728,560,["u",7,3]],
[728,560,["u",8,3]],[728,703,["u",3,27]],
[730,729,["l",2,1459]],[732,484,["s",12,3]],
[732,492,["s",12,3]],[732,665,["l",4,11]],
[732,666,["o",7,11]],[732,666,["s",6,11]],
[732,671,["o",7,11]],[732,671,["s",6,11]],
[732,720,["s",12,3]],[732,726,["s",12,3]],
[732,728,["u",7,3]],[732,728,["u",8,3]],
[733,367,["l",2,733]],[736,721,["u",3,47]],
[736,735,["l",2,1471]],[738,484,["s",12,3]],
[738,492,["s",12,3]],[738,720,["s",12,3]],
[738,726,["s",12,3]],[738,732,["s",12,3]],
[739,370,["l",2,739]],[741,740,["l",2,1481]],
[742,741,["l",2,1483]],[743,372,["l",2,743]],
[744,601,["3D4",5]],[744,620,["3D4",5]],[744,626,["F4",5]],
[744,630,["3D4",5]],[744,630,["F4",5]],
[744,743,["l",2,1487]],[745,744,["l",2,1489]],
[747,746,["l",2,1493]],[750,749,["l",2,1499]],
[751,376,["l",2,751]],[752,736,["u",3,47]],
[756,755,["l",2,1511]],[757,379,["l",2,757]],
[757,728,["l",3,27]],[757,728,["G2",27]],
[761,381,["l",2,761]],[762,761,["l",2,1523]],
[765,651,["o-",18,2]],[765,714,["o-",18,2]],
[766,765,["l",2,1531]],[769,385,["l",2,769]],
[771,645,["o+",18,2]],[771,762,["o+",18,2]],
[771,765,["s",18,2]],[772,771,["l",2,1543]],
[773,387,["l",2,773]],[775,774,["l",2,1549]],
[777,776,["l",2,1553]],[780,744,["F4",5]],
[780,771,["o+",18,2]],[780,771,["s",18,2]],
[780,779,["l",2,1559]],[781,744,["l",5,5]],
[784,783,["l",2,1567]],[786,785,["l",2,1571]],
[787,394,["l",2,787]],[790,789,["l",2,1579]],
[792,791,["l",2,1583]],[797,399,["l",2,797]],
[799,798,["l",2,1597]],[801,800,["l",2,1601]],
[804,803,["l",2,1607]],[805,804,["l",2,1609]],
[807,806,["l",2,1613]],[809,405,["l",2,809]],
[810,809,["l",2,1619]],[811,406,["l",2,811]],
[811,810,["l",2,1621]],[812,421,["s",4,29]],
[812,435,["s",4,29]],[814,813,["l",2,1627]],
[817,800,["l",3,49]],[819,818,["l",2,1637]],
[820,728,["o-",14,3]],[820,732,["o-",14,3]],
[820,780,["o-",14,3]],[821,411,["l",2,821]],
[823,412,["l",2,823]],[827,414,["l",2,827]],
[829,415,["l",2,829]],[829,828,["l",2,1657]],
[832,831,["l",2,1663]],[834,833,["l",2,1667]],
[835,834,["l",2,1669]],[839,420,["l",2,839]],
[840,771,["s",18,2]],[840,780,["s",18,2]],
[841,840,["l",2,1681]],[841,840,["s",4,41]],
[847,846,["l",2,1693]],[849,848,["l",2,1697]],
[850,849,["l",2,1699]],[853,427,["l",2,853]],
[855,854,["l",2,1709]],[857,429,["l",2,857]],
[859,430,["l",2,859]],[861,841,["s",4,41]],
[861,860,["l",2,1721]],[862,861,["l",2,1723]],
[863,432,["l",2,863]],[867,866,["l",2,1733]],
[870,421,["s",4,29]],[870,435,["s",4,29]],
[870,812,["s",4,29]],[871,840,["l",3,29]],
[871,840,["G2",29]],[871,841,["G2",29]],
[871,870,["G2",29]],[871,870,["l",2,1741]],
[874,873,["l",2,1747]],[877,439,["l",2,877]],
[877,876,["l",2,1753]],[880,879,["l",2,1759]],
[881,441,["l",2,881]],[883,442,["l",2,883]],
[887,444,["l",2,887]],[889,888,["l",2,1777]],
[892,891,["l",2,1783]],[894,893,["l",2,1787]],
[895,894,["l",2,1789]],[901,900,["l",2,1801]],
[906,905,["l",2,1811]],[907,454,["l",2,907]],
[911,456,["l",2,911]],[912,911,["l",2,1823]],
[916,915,["l",2,1831]],[919,460,["l",2,919]],
[924,923,["l",2,1847]],[925,924,["l",2,1849]],
[925,924,["s",4,43]],[929,465,["l",2,929]],
[930,481,["s",4,31]],[930,496,["s",4,31]],
[930,765,["o-",18,2]],[930,771,["s",18,2]],
[930,780,["s",18,2]],[930,840,["s",18,2]],
[931,930,["l",2,1861]],[934,933,["l",2,1867]],
[936,919,["u",3,53]],[936,935,["l",2,1871]],
[937,469,["l",2,937]],[937,936,["l",2,1873]],
[939,819,["o+",10,5]],[939,930,["o+",10,5]],
[939,938,["l",2,1877]],[940,939,["l",2,1879]],
[941,471,["l",2,941]],[945,944,["l",2,1889]],
[946,925,["s",4,43]],[947,474,["l",2,947]],
[951,950,["l",2,1901]],[953,477,["l",2,953]],
[954,936,["u",3,53]],[954,953,["l",2,1907]],
[957,956,["l",2,1913]],[960,931,["u",3,31]],
[966,965,["l",2,1931]],[967,484,["l",2,967]],
[967,966,["l",2,1933]],[968,949,["E6",3]],
[971,486,["l",2,971]],[975,974,["l",2,1949]],
[976,975,["l",2,1951]],[977,489,["l",2,977]],
[983,492,["l",2,983]],[987,986,["l",2,1973]],
[990,989,["l",2,1979]],[991,496,["l",2,991]],
[992,481,["s",4,31]],[992,496,["s",4,31]],
[992,930,["s",4,31]],[992,960,["u",3,31]],
[993,960,["G2",31]],[993,961,["G2",31]],[993,992,["G2",31]],
[994,993,["l",2,1987]],[997,499,["l",2,997]],
[997,996,["l",2,1993]],[999,998,["l",2,1997]],
[1000,999,["l",2,1999]],[1002,1001,["l",2,2003]],
[1006,1005,["l",2,2011]],[1009,505,["l",2,1009]],
[1009,1008,["l",2,2017]],[1013,507,["l",2,1013]],
[1014,1013,["l",2,2027]],[1015,1014,["l",2,2029]],
[1019,510,["l",2,1019]],[1020,765,["o-",18,2]],
[1020,771,["s",18,2]],[1020,780,["s",18,2]],
[1020,840,["s",18,2]],[1020,930,["o-",18,2]],
[1020,930,["s",18,2]],[1020,1019,["l",2,2039]],
[1021,511,["l",2,1021]],[1023,765,["u",11,2]],
[1023,765,["u",12,2]],[1023,774,["u",12,2]],
[1023,889,["l",10,2]],[1023,1020,["u",11,2]],
[1023,1020,["u",12,2]],[1025,819,["u",6,4]],
[1025,1023,["l",2,1024]],[1025,1023,["s",4,32]],
[1026,1023,["u",11,2]],[1026,1023,["u",12,2]],
[1027,1026,["l",2,2053]],[1031,516,["l",2,1031]],
[1032,1031,["l",2,2063]],[1033,517,["l",2,1033]],
[1035,1034,["l",2,2069]],[1039,520,["l",2,1039]],
[1040,728,["2E6",3]],[1040,732,["2E6",3]],
[1041,1040,["l",2,2081]],[1042,1041,["l",2,2083]],
[1044,1043,["l",2,2087]],[1045,1044,["l",2,2089]],
[1049,525,["l",2,1049]],[1050,1049,["l",2,2099]],
[1051,526,["l",2,1051]],[1056,1055,["l",2,2111]],
[1057,1023,["l",3,32]],[1057,1023,["G2",32]],
[1057,1056,["l",2,2113]],[1061,531,["l",2,1061]],
[1063,532,["l",2,1063]],[1065,1064,["l",2,2129]],
[1066,1065,["l",2,2131]],[1069,535,["l",2,1069]],
[1069,1068,["l",2,2137]],[1071,1025,["o-",10,4]],
[1071,1070,["l",2,2141]],[1072,1071,["l",2,2143]],
[1077,1076,["l",2,2153]],[1081,1080,["l",2,2161]],
[1087,544,["l",2,1087]],[1090,1089,["l",2,2179]],
[1091,546,["l",2,1091]],[1092,968,["E6",3]],
[1093,547,["l",2,1093]],[1093,1040,["l",7,3]],
[1094,1093,["l",2,2187]],[1097,549,["l",2,1097]],
[1099,1020,["u",4,13]],[1099,1092,["u",4,13]],
[1099,1098,["l",2,2197]],[1102,1101,["l",2,2203]],
[1103,552,["l",2,1103]],[1104,1103,["l",2,2207]],
[1105,1104,["l",2,2209]],[1105,1104,["s",4,47]],
[1107,1106,["l",2,2213]],[1109,555,["l",2,1109]],
[1111,1110,["l",2,2221]],[1117,559,["l",2,1117]],
[1119,1118,["l",2,2237]],[1120,1119,["l",2,2239]],
[1122,1121,["l",2,2243]],[1123,562,["l",2,1123]],
[1126,1125,["l",2,2251]],[1128,1105,["s",4,47]],
[1129,565,["l",2,1129]],[1134,1133,["l",2,2267]],
[1135,1134,["l",2,2269]],[1137,1136,["l",2,2273]],
[1141,1140,["l",2,2281]],[1144,1143,["l",2,2287]],
[1147,1146,["l",2,2293]],[1149,1148,["l",2,2297]],
[1151,576,["l",2,1151]],[1153,577,["l",2,1153]],
[1155,1154,["l",2,2309]],[1156,1155,["l",2,2311]],
[1160,1141,["u",3,59]],[1163,582,["l",2,1163]],
[1167,1166,["l",2,2333]],[1170,1169,["l",2,2339]],
[1171,586,["l",2,1171]],[1171,1170,["l",2,2341]],
[1174,1173,["l",2,2347]],[1176,1175,["l",2,2351]],
[1179,1178,["l",2,2357]],[1180,1160,["u",3,59]],
[1181,591,["l",2,1181]],[1186,1185,["l",2,2371]],
[1187,594,["l",2,1187]],[1189,1188,["l",2,2377]],
[1190,1099,["o",7,13]],[1190,1099,["s",6,13]],
[1190,1105,["o",7,13]],[1190,1105,["s",6,13]],
[1191,1190,["l",2,2381]],[1192,1191,["l",2,2383]],
[1193,597,["l",2,1193]],[1195,1194,["l",2,2389]],
[1197,1196,["l",2,2393]],[1200,1199,["l",2,2399]],
[1201,601,["l",2,1201]],[1201,1200,["l",2,2401]],
[1201,1200,["s",4,49]],[1206,1205,["l",2,2411]],
[1209,1208,["l",2,2417]],[1212,1211,["l",2,2423]],
[1213,607,["l",2,1213]],[1217,609,["l",2,1217]],
[1219,1218,["l",2,2437]],[1221,1220,["l",2,2441]],
[1223,612,["l",2,1223]],[1224,1223,["l",2,2447]],
[1229,615,["l",2,1229]],[1230,1229,["l",2,2459]],
[1231,616,["l",2,1231]],[1234,1233,["l",2,2467]],
[1237,619,["l",2,1237]],[1237,1236,["l",2,2473]],
[1239,1238,["l",2,2477]],[1249,625,["l",2,1249]],
[1252,1251,["l",2,2503]],[1259,630,["l",2,1259]],
[1261,1240,["l",3,61]],[1261,1260,["l",2,2521]],
[1266,1265,["l",2,2531]],[1270,1269,["l",2,2539]],
[1272,1271,["l",2,2543]],[1275,1274,["l",2,2549]],
[1276,1275,["l",2,2551]],[1277,639,["l",2,1277]],
[1279,640,["l",2,1279]],[1279,1278,["l",2,2557]],
[1283,642,["l",2,1283]],[1285,1105,["o+",10,4]],
[1285,1105,["s",10,4]],[1289,645,["l",2,1289]],
[1290,1289,["l",2,2579]],[1291,646,["l",2,1291]],
[1296,1295,["l",2,2591]],[1297,649,["l",2,1297]],
[1297,1296,["l",2,2593]],[1301,651,["l",2,1301]],
[1303,652,["l",2,1303]],[1305,1228,["l",4,17]],
[1305,1304,["l",2,2609]],[1307,654,["l",2,1307]],
[1309,1308,["l",2,2617]],[1311,1310,["l",2,2621]],
[1312,1181,["u",5,9]],[1317,1316,["l",2,2633]],
[1319,660,["l",2,1319]],[1320,732,["s",6,11]],
[1321,661,["l",2,1321]],[1321,1271,["2F4",32]],
[1324,1323,["l",2,2647]],[1327,664,["l",2,1327]],
[1329,1328,["l",2,2657]],[1330,1329,["l",2,2659]],
[1332,685,["s",4,37]],[1332,703,["s",4,37]],
[1332,1331,["l",2,2663]],[1336,1335,["l",2,2671]],
[1339,1338,["l",2,2677]],[1342,732,["s",6,11]],
[1342,1320,["s",6,11]],[1342,1341,["l",2,2683]],
[1344,1343,["l",2,2687]],[1345,1344,["l",2,2689]],
[1347,1346,["l",2,2693]],[1350,1349,["l",2,2699]],
[1354,1353,["l",2,2707]],[1356,1355,["l",2,2711]],
[1357,1356,["l",2,2713]],[1360,1359,["l",2,2719]],
[1361,681,["l",2,1361]],[1365,1364,["l",2,2729]],
[1366,1365,["l",2,2731]],[1367,684,["l",2,1367]],
[1368,1201,["o",9,7]],[1368,1201,["o-",8,7]],
[1368,1201,["s",8,7]],[1368,1204,["o",9,7]],
[1368,1204,["s",8,7]],[1368,1333,["u",3,37]],
[1371,1370,["l",2,2741]],[1373,687,["l",2,1373]],
[1375,1374,["l",2,2749]],[1377,1376,["l",2,2753]],
[1381,691,["l",2,1381]],[1384,1383,["l",2,2767]],
[1387,1365,["l",3,64]],[1389,1388,["l",2,2777]],
[1395,1394,["l",2,2789]],[1396,1395,["l",2,2791]],
[1399,700,["l",2,1399]],[1399,1398,["l",2,2797]],
[1400,1368,["o",9,7]],[1400,1368,["o-",8,7]],
[1400,1368,["s",8,7]],[1401,1400,["l",2,2801]],
[1402,1401,["l",2,2803]],[1405,1404,["l",2,2809]],
[1405,1404,["s",4,53]],[1406,685,["s",4,37]],
[1406,703,["s",4,37]],[1406,1332,["s",4,37]],
[1406,1368,["u",3,37]],[1407,1368,["G2",37]],
[1407,1369,["G2",37]],[1407,1406,["G2",37]],
[1409,705,["l",2,1409]],[1410,1409,["l",2,2819]],
[1417,1416,["l",2,2833]],[1419,1418,["l",2,2837]],
[1422,1421,["l",2,2843]],[1423,712,["l",2,1423]],
[1426,1425,["l",2,2851]],[1427,714,["l",2,1427]],
[1429,715,["l",2,1429]],[1429,1428,["l",2,2857]],
[1431,1405,["s",4,53]],[1431,1430,["l",2,2861]],
[1433,717,["l",2,1433]],[1439,720,["l",2,1439]],
[1440,1439,["l",2,2879]],[1444,1443,["l",2,2887]],
[1447,724,["l",2,1447]],[1449,1448,["l",2,2897]],
[1451,726,["l",2,1451]],[1452,1451,["l",2,2903]],
[1453,727,["l",2,1453]],[1455,1454,["l",2,2909]],
[1459,730,["l",2,1459]],[1459,1458,["l",2,2917]],
[1460,1220,["o+",14,3]],[1460,1220,["o",15,3]],
[1460,1220,["s",14,3]],[1460,1230,["o",15,3]],
[1460,1230,["s",14,3]],[1460,1260,["o",15,3]],
[1460,1260,["s",14,3]],[1460,1452,["o+",14,3]],
[1460,1452,["o",15,3]],[1460,1452,["s",14,3]],
[1464,1463,["l",2,2927]],[1470,1469,["l",2,2939]],
[1471,736,["l",2,1471]],[1476,1460,["o",15,3]],
[1476,1460,["s",14,3]],[1477,1476,["l",2,2953]],
[1479,1478,["l",2,2957]],[1481,741,["l",2,1481]],
[1482,1481,["l",2,2963]],[1483,742,["l",2,1483]],
[1485,1484,["l",2,2969]],[1486,1485,["l",2,2971]],
[1487,744,["l",2,1487]],[1489,745,["l",2,1489]],
[1493,747,["l",2,1493]],[1499,750,["l",2,1499]],
[1500,1499,["l",2,2999]],[1501,1500,["l",2,3001]],
[1506,1505,["l",2,3011]],[1510,1509,["l",2,3019]],
[1511,756,["l",2,1511]],[1512,1511,["l",2,3023]],
[1519,1496,["l",3,67]],[1519,1518,["l",2,3037]],
[1521,1520,["l",2,3041]],[1523,762,["l",2,1523]],
[1525,1524,["l",2,3049]],[1531,766,["l",2,1531]],
[1531,1530,["l",2,3061]],[1534,1533,["l",2,3067]],
[1540,1539,["l",2,3079]],[1542,1541,["l",2,3083]],
[1543,772,["l",2,1543]],[1545,1544,["l",2,3089]],
[1549,775,["l",2,1549]],[1553,777,["l",2,1553]],
[1555,1554,["l",2,3109]],[1559,780,["l",2,1559]],
[1560,1559,["l",2,3119]],[1561,1560,["l",2,3121]],
[1563,1562,["l",2,3125]],[1567,784,["l",2,1567]],
[1569,1568,["l",2,3137]],[1571,786,["l",2,1571]],
[1579,790,["l",2,1579]],[1582,1581,["l",2,3163]],
[1583,792,["l",2,1583]],[1584,1583,["l",2,3167]],
[1585,1584,["l",2,3169]],[1591,1590,["l",2,3181]],
[1594,1593,["l",2,3187]],[1596,1595,["l",2,3191]],
[1597,799,["l",2,1597]],[1601,801,["l",2,1601]],
[1602,1601,["l",2,3203]],[1605,1604,["l",2,3209]],
[1607,804,["l",2,1607]],[1609,805,["l",2,1609]],
[1609,1608,["l",2,3217]],[1611,1610,["l",2,3221]],
[1612,1563,["o-",10,5]],[1613,807,["l",2,1613]],
[1615,1614,["l",2,3229]],[1619,810,["l",2,1619]],
[1621,811,["l",2,1621]],[1626,1625,["l",2,3251]],
[1627,814,["l",2,1627]],[1627,1626,["l",2,3253]],
[1629,1628,["l",2,3257]],[1630,1629,["l",2,3259]],
[1636,1635,["l",2,3271]],[1637,819,["l",2,1637]],
[1640,820,["o+",8,9]],[1640,841,["s",4,41]],
[1640,861,["s",4,41]],[1640,1573,["E7",3]],
[1640,1573,["l",8,3]],[1650,1649,["l",2,3299]],
[1651,1650,["l",2,3301]],[1654,1653,["l",2,3307]],
[1657,829,["l",2,1657]],[1657,1656,["l",2,3313]],
[1660,1659,["l",2,3319]],[1662,1661,["l",2,3323]],
[1663,832,["l",2,1663]],[1665,1664,["l",2,3329]],
[1666,1665,["l",2,3331]],[1667,834,["l",2,1667]],
[1669,835,["l",2,1669]],[1672,1671,["l",2,3343]],
[1674,1673,["l",2,3347]],[1680,1657,["u",3,71]],
[1680,1679,["l",2,3359]],[1681,1680,["l",2,3361]],
[1686,1685,["l",2,3371]],[1687,1686,["l",2,3373]],
[1693,847,["l",2,1693]],[1695,1694,["l",2,3389]],
[1696,1695,["l",2,3391]],[1697,849,["l",2,1697]],
[1699,850,["l",2,1699]],[1704,1680,["u",3,71]],
[1704,1703,["l",2,3407]],[1705,1687,["E6",4]],
[1707,1706,["l",2,3413]],[1709,855,["l",2,1709]],
[1715,1629,["u",4,19]],[1715,1710,["u",4,19]],
[1717,1716,["l",2,3433]],[1721,861,["l",2,1721]],
[1722,841,["s",4,41]],[1722,861,["s",4,41]],
[1722,1640,["s",4,41]],[1723,862,["l",2,1723]],
[1723,1680,["l",3,41]],[1723,1680,["G2",41]],
[1723,1681,["G2",41]],[1723,1722,["G2",41]],
[1725,1724,["l",2,3449]],[1729,1728,["l",2,3457]],
[1731,1730,["l",2,3461]],[1732,1731,["l",2,3463]],
[1733,867,["l",2,1733]],[1734,1733,["l",2,3467]],
[1735,1734,["l",2,3469]],[1741,871,["l",2,1741]],
[1741,1740,["l",2,3481]],[1741,1740,["s",4,59]],
[1746,1745,["l",2,3491]],[1747,874,["l",2,1747]],
[1750,1749,["l",2,3499]],[1753,877,["l",2,1753]],
[1756,1755,["l",2,3511]],[1759,880,["l",2,1759]],
[1759,1758,["l",2,3517]],[1764,1763,["l",2,3527]],
[1765,1764,["l",2,3529]],[1767,1766,["l",2,3533]],
[1770,1741,["s",4,59]],[1770,1769,["l",2,3539]],
[1771,1770,["l",2,3541]],[1774,1773,["l",2,3547]],
[1777,889,["l",2,1777]],[1779,1778,["l",2,3557]],
[1780,1779,["l",2,3559]],[1783,892,["l",2,1783]],
[1785,1533,["o-",20,2]],[1785,1542,["o-",20,2]],
[1786,1785,["l",2,3571]],[1787,894,["l",2,1787]],
[1789,895,["l",2,1789]],[1791,1790,["l",2,3581]],
[1792,1791,["l",2,3583]],[1797,1796,["l",2,3593]],
[1801,901,["l",2,1801]],[1801,1776,["l",3,73]],
[1804,1803,["l",2,3607]],[1806,925,["s",4,43]],
[1806,946,["s",4,43]],[1807,1806,["l",2,3613]],
[1809,1808,["l",2,3617]],[1811,906,["l",2,1811]],
[1812,1811,["l",2,3623]],[1816,1815,["l",2,3631]],
[1819,1818,["l",2,3637]],[1822,1821,["l",2,3643]],
[1823,912,["l",2,1823]],[1830,1829,["l",2,3659]],
[1831,916,["l",2,1831]],[1836,1835,["l",2,3671]],
[1837,1836,["l",2,3673]],[1839,1838,["l",2,3677]],
[1846,1845,["l",2,3691]],[1847,924,["l",2,1847]],
[1848,1807,["u",3,43]],[1849,1848,["l",2,3697]],
[1851,1850,["l",2,3701]],[1855,1854,["l",2,3709]],
[1860,1859,["l",2,3719]],[1861,931,["l",2,1861]],
[1861,1860,["l",2,3721]],[1861,1860,["s",4,61]],
[1864,1863,["l",2,3727]],[1867,934,["l",2,1867]],
[1867,1866,["l",2,3733]],[1870,1869,["l",2,3739]],
[1871,936,["l",2,1871]],[1873,937,["l",2,1873]],
[1877,939,["l",2,1877]],[1878,1638,["o",11,5]],
[1878,1638,["s",10,5]],[1878,1860,["o",11,5]],
[1878,1860,["s",10,5]],[1879,940,["l",2,1879]],
[1881,1880,["l",2,3761]],[1884,1883,["l",2,3767]],
[1885,1884,["l",2,3769]],[1889,945,["l",2,1889]],
[1890,1889,["l",2,3779]],[1891,1861,["s",4,61]],
[1892,925,["s",4,43]],[1892,946,["s",4,43]],
[1892,1806,["s",4,43]],[1892,1848,["u",3,43]],
[1893,1848,["G2",43]],[1893,1849,["G2",43]],
[1893,1892,["G2",43]],[1897,1896,["l",2,3793]],
[1899,1898,["l",2,3797]],[1901,951,["l",2,1901]],
[1902,1901,["l",2,3803]],[1905,1581,["o+",20,2]],
[1905,1785,["s",20,2]],[1905,1860,["o+",20,2]],
[1905,1860,["s",20,2]],[1907,954,["l",2,1907]],
[1911,1910,["l",2,3821]],[1912,1911,["l",2,3823]],
[1913,957,["l",2,1913]],[1917,1916,["l",2,3833]],
[1924,1923,["l",2,3847]],[1926,1925,["l",2,3851]],
[1927,1926,["l",2,3853]],[1931,966,["l",2,1931]],
[1932,1931,["l",2,3863]],[1933,967,["l",2,1933]],
[1939,1938,["l",2,3877]],[1941,1940,["l",2,3881]],
[1945,1944,["l",2,3889]],[1949,975,["l",2,1949]],
[1951,976,["l",2,1951]],[1953,1562,["l",6,5]],
[1954,1953,["l",2,3907]],[1956,1955,["l",2,3911]],
[1959,1958,["l",2,3917]],[1960,1959,["l",2,3919]],
[1962,1961,["l",2,3923]],[1965,1964,["l",2,3929]],
[1966,1965,["l",2,3931]],[1972,1971,["l",2,3943]],
[1973,987,["l",2,1973]],[1974,1973,["l",2,3947]],
[1979,990,["l",2,1979]],[1984,1983,["l",2,3967]],
[1987,994,["l",2,1987]],[1993,997,["l",2,1993]],
[1995,1994,["l",2,3989]],[1997,999,["l",2,1997]],
[1999,1000,["l",2,1999]],[2001,2000,["l",2,4001]],
[2002,2001,["l",2,4003]],[2003,1002,["l",2,2003]],
[2004,2003,["l",2,4007]],[2007,2006,["l",2,4013]],
[2010,2009,["l",2,4019]],[2011,1006,["l",2,2011]],
[2011,2010,["l",2,4021]],[2014,2013,["l",2,4027]],
[2017,1009,["l",2,2017]],[2025,2024,["l",2,4049]],
[2026,2025,["l",2,4051]],[2027,1014,["l",2,2027]],
[2029,1015,["l",2,2029]],[2029,2028,["l",2,4057]],
[2037,2036,["l",2,4073]],[2039,1020,["l",2,2039]],
[2040,1905,["s",20,2]],[2040,2039,["l",2,4079]],
[2046,2045,["l",2,4091]],[2047,1953,["l",11,2]],
[2047,2046,["l",2,4093]],[2049,2047,["l",2,2048]],
[2050,2049,["l",2,4099]],[2053,1027,["l",2,2053]],
[2056,2055,["l",2,4111]],[2063,1032,["l",2,2063]],
[2064,2063,["l",2,4127]],[2065,2064,["l",2,4129]],
[2067,2066,["l",2,4133]],[2069,1035,["l",2,2069]],
[2070,2069,["l",2,4139]],[2077,2076,["l",2,4153]],
[2079,2078,["l",2,4157]],[2080,2079,["l",2,4159]],
[2081,1041,["l",2,2081]],[2083,1042,["l",2,2083]],
[2087,1044,["l",2,2087]],[2089,1045,["l",2,2089]],
[2089,2088,["l",2,4177]],[2099,1050,["l",2,2099]],
[2101,2100,["l",2,4201]],[2106,2105,["l",2,4211]],
[2107,2080,["l",3,79]],[2109,2108,["l",2,4217]],
[2110,2109,["l",2,4219]],[2111,1056,["l",2,2111]],
[2113,1057,["l",2,2113]],[2113,2047,["2B2",2048]],
[2115,2114,["l",2,4229]],[2116,2115,["l",2,4231]],
[2121,2120,["l",2,4241]],[2122,2121,["l",2,4243]],
[2127,2126,["l",2,4253]],[2129,1065,["l",2,2129]],
[2130,2129,["l",2,4259]],[2131,1066,["l",2,2131]],
[2131,2130,["l",2,4261]],[2136,2135,["l",2,4271]],
[2137,1069,["l",2,2137]],[2137,2136,["l",2,4273]],
[2141,1071,["l",2,2141]],[2142,2141,["l",2,4283]],
[2143,1072,["l",2,2143]],[2145,2144,["l",2,4289]],
[2149,2148,["l",2,4297]],[2153,1077,["l",2,2153]],
[2161,1081,["l",2,2161]],[2162,1105,["s",4,47]],
[2162,1128,["s",4,47]],[2164,2163,["l",2,4327]],
[2169,2168,["l",2,4337]],[2170,2169,["l",2,4339]],
[2175,2174,["l",2,4349]],[2178,1460,["s",14,3]],
[2178,1476,["s",14,3]],[2179,1090,["l",2,2179]],
[2179,2178,["l",2,4357]],[2182,2181,["l",2,4363]],
[2184,1190,["s",6,13]],[2184,1460,["s",14,3]],
[2184,1476,["s",14,3]],[2184,2178,["s",14,3]],
[2187,2186,["l",2,4373]],[2190,1460,["s",14,3]],
[2190,1476,["s",14,3]],[2190,2178,["s",14,3]],
[2190,2184,["s",14,3]],[2196,1460,["s",14,3]],
[2196,1476,["s",14,3]],[2196,2178,["s",14,3]],
[2196,2184,["s",14,3]],[2196,2190,["s",14,3]],
[2196,2195,["l",2,4391]],[2199,2198,["l",2,4397]],
[2203,1102,["l",2,2203]],[2205,2204,["l",2,4409]],
[2207,1104,["l",2,2207]],[2210,1190,["s",6,13]],
[2210,2184,["s",6,13]],[2211,2210,["l",2,4421]],
[2212,2211,["l",2,4423]],[2213,1107,["l",2,2213]],
[2221,1111,["l",2,2221]],[2221,2220,["l",2,4441]],
[2224,2223,["l",2,4447]],[2226,2225,["l",2,4451]],
[2229,2228,["l",2,4457]],[2232,2231,["l",2,4463]],
[2237,1119,["l",2,2237]],[2239,1120,["l",2,2239]],
[2241,2240,["l",2,4481]],[2242,2241,["l",2,4483]],
[2243,1122,["l",2,2243]],[2245,2244,["l",2,4489]],
[2245,2244,["s",4,67]],[2247,2246,["l",2,4493]],
[2251,1126,["l",2,2251]],[2254,2253,["l",2,4507]],
[2256,1105,["s",4,47]],[2256,1128,["s",4,47]],
[2256,2162,["s",4,47]],[2257,2208,["l",3,47]],
[2257,2208,["G2",47]],[2257,2209,["G2",47]],
[2257,2256,["G2",47]],[2257,2256,["l",2,4513]],
[2259,2258,["l",2,4517]],[2260,2259,["l",2,4519]],
[2262,2261,["l",2,4523]],[2267,1134,["l",2,2267]],
[2269,1135,["l",2,2269]],[2269,2186,["2G2",2187]],
[2273,1137,["l",2,2273]],[2274,2273,["l",2,4547]],
[2275,2274,["l",2,4549]],[2278,2245,["s",4,67]],
[2281,1141,["l",2,2281]],[2281,2280,["l",2,4561]],
[2284,2283,["l",2,4567]],[2287,1144,["l",2,2287]],
[2292,2291,["l",2,4583]],[2293,1147,["l",2,2293]],
[2296,2269,["u",3,83]],[2296,2295,["l",2,4591]],
[2297,1149,["l",2,2297]],[2299,2298,["l",2,4597]],
[2302,2301,["l",2,4603]],[2309,1155,["l",2,2309]],
[2311,1156,["l",2,2311]],[2311,2310,["l",2,4621]],
[2319,2318,["l",2,4637]],[2320,2319,["l",2,4639]],
[2322,2321,["l",2,4643]],[2324,2296,["u",3,83]],
[2325,2324,["l",2,4649]],[2326,2325,["l",2,4651]],
[2329,2328,["l",2,4657]],[2332,2331,["l",2,4663]],
[2333,1167,["l",2,2333]],[2337,2336,["l",2,4673]],
[2339,1170,["l",2,2339]],[2340,2339,["l",2,4679]],
[2341,1171,["l",2,2341]],[2346,2345,["l",2,4691]],
[2347,1174,["l",2,2347]],[2351,1176,["l",2,2351]],
[2352,2351,["l",2,4703]],[2357,1179,["l",2,2357]],
[2361,2360,["l",2,4721]],[2362,2361,["l",2,4723]],
[2365,2364,["l",2,4729]],[2367,2366,["l",2,4733]],
[2371,1186,["l",2,2371]],[2376,2375,["l",2,4751]],
[2377,1189,["l",2,2377]],[2380,2379,["l",2,4759]],
[2381,1191,["l",2,2381]],[2383,1192,["l",2,2383]],
[2389,1195,["l",2,2389]],[2392,2391,["l",2,4783]],
[2393,1197,["l",2,2393]],[2394,1368,["s",8,7]],
[2394,1400,["s",8,7]],[2394,2393,["l",2,4787]],
[2395,2394,["l",2,4789]],[2397,2396,["l",2,4793]],
[2399,1200,["l",2,2399]],[2400,2101,["u",5,7]],
[2400,2353,["u",3,49]],[2400,2399,["l",2,4799]],
[2401,2400,["l",2,4801]],[2407,2406,["l",2,4813]],
[2408,1368,["s",8,7]],[2408,1400,["s",8,7]],
[2408,2394,["s",8,7]],[2408,2400,["u",5,7]],
[2409,2408,["l",2,4817]],[2411,1206,["l",2,2411]],
[2416,2415,["l",2,4831]],[2417,1209,["l",2,2417]],
[2420,2132,["o+",16,3]],[2423,1212,["l",2,2423]],
[2431,2430,["l",2,4861]],[2436,2435,["l",2,4871]],
[2437,1219,["l",2,2437]],[2439,2438,["l",2,4877]],
[2441,1221,["l",2,2441]],[2445,2444,["l",2,4889]],
[2447,1224,["l",2,2447]],[2451,2400,["G2",49]],
[2452,2451,["l",2,4903]],[2455,2454,["l",2,4909]],
[2457,2320,["u",4,17]],[2457,2448,["u",4,17]],
[2457,2456,["l",2,4913]],[2459,1230,["l",2,2459]],
[2460,2420,["o+",16,3]],[2460,2459,["l",2,4919]],
[2466,2465,["l",2,4931]],[2467,1234,["l",2,2467]],
[2467,2466,["l",2,4933]],[2469,2468,["l",2,4937]],
[2472,2471,["l",2,4943]],[2473,1237,["l",2,2473]],
[2476,2475,["l",2,4951]],[2477,1239,["l",2,2477]],
[2479,2478,["l",2,4957]],[2484,2483,["l",2,4967]],
[2485,2484,["l",2,4969]],[2487,2486,["l",2,4973]],
[2494,2493,["l",2,4987]],[2497,2496,["l",2,4993]],
[2500,2499,["l",2,4999]],[2502,2501,["l",2,5003]],
[2503,1252,["l",2,2503]],[2505,2504,["l",2,5009]],
[2506,2505,["l",2,5011]],[2511,2510,["l",2,5021]],
[2512,2511,["l",2,5023]],[2520,2519,["l",2,5039]],
[2521,1261,["l",2,2521]],[2521,2520,["l",2,5041]],
[2521,2520,["s",4,71]],[2526,2525,["l",2,5051]],
[2530,2529,["l",2,5059]],[2531,1266,["l",2,2531]],
[2539,1270,["l",2,2539]],[2539,2538,["l",2,5077]],
[2541,2540,["l",2,5081]],[2543,1272,["l",2,2543]],
[2544,2543,["l",2,5087]],[2549,1275,["l",2,2549]],
[2550,2549,["l",2,5099]],[2551,1276,["l",2,2551]],
[2551,2550,["l",2,5101]],[2554,2553,["l",2,5107]],
[2556,2521,["s",4,71]],[2557,1279,["l",2,2557]],
[2557,2556,["l",2,5113]],[2560,2559,["l",2,5119]],
[2574,2573,["l",2,5147]],[2577,2576,["l",2,5153]],
[2579,1290,["l",2,2579]],[2584,2583,["l",2,5167]],
[2586,2585,["l",2,5171]],[2590,2589,["l",2,5179]],
[2591,1296,["l",2,2591]],[2593,1297,["l",2,2593]],
[2595,2594,["l",2,5189]],[2599,2598,["l",2,5197]],
[2605,2604,["l",2,5209]],[2609,1305,["l",2,2609]],
[2610,2457,["o",7,17]],[2610,2457,["s",6,17]],
[2610,2465,["o",7,17]],[2610,2465,["s",6,17]],
[2614,2613,["l",2,5227]],[2616,2615,["l",2,5231]],
[2617,1309,["l",2,2617]],[2617,2616,["l",2,5233]],
[2619,2618,["l",2,5237]],[2621,1311,["l",2,2621]],
[2631,2630,["l",2,5261]],[2633,1317,["l",2,2633]],
[2637,2636,["l",2,5273]],[2640,2611,["u",3,89]],
[2640,2639,["l",2,5279]],[2641,2640,["l",2,5281]],
[2647,1324,["l",2,2647]],[2649,2648,["l",2,5297]],
[2652,2651,["l",2,5303]],[2655,2654,["l",2,5309]],
[2657,1329,["l",2,2657]],[2659,1330,["l",2,2659]],
[2662,2661,["l",2,5323]],[2663,1332,["l",2,2663]],
[2665,2664,["l",2,5329]],[2665,2664,["s",4,73]],
[2667,2666,["l",2,5333]],[2670,2640,["u",3,89]],
[2671,1336,["l",2,2671]],[2674,2673,["l",2,5347]],
[2676,2675,["l",2,5351]],[2677,1339,["l",2,2677]],
[2683,1342,["l",2,2683]],[2687,1344,["l",2,2687]],
[2689,1345,["l",2,2689]],[2691,2690,["l",2,5381]],
[2693,1347,["l",2,2693]],[2694,2693,["l",2,5387]],
[2697,2696,["l",2,5393]],[2699,1350,["l",2,2699]],
[2700,2699,["l",2,5399]],[2701,2665,["s",4,73]],
[2704,2703,["l",2,5407]],[2707,1354,["l",2,2707]],
[2707,2706,["l",2,5413]],[2709,2708,["l",2,5417]],
[2710,2709,["l",2,5419]],[2711,1356,["l",2,2711]],
[2713,1357,["l",2,2713]],[2716,2715,["l",2,5431]],
[2719,1360,["l",2,2719]],[2719,2718,["l",2,5437]],
[2721,2720,["l",2,5441]],[2722,2721,["l",2,5443]],
[2725,2724,["l",2,5449]],[2729,1365,["l",2,2729]],
[2731,1366,["l",2,2731]],[2736,2353,["3D4",7]],
[2736,2394,["3D4",7]],[2736,2402,["F4",7]],
[2736,2408,["3D4",7]],[2736,2408,["F4",7]],
[2736,2735,["l",2,5471]],[2739,2738,["l",2,5477]],
[2740,2739,["l",2,5479]],[2741,1371,["l",2,2741]],
[2742,2741,["l",2,5483]],[2749,1375,["l",2,2749]],
[2751,2750,["l",2,5501]],[2752,2751,["l",2,5503]],
[2753,1377,["l",2,2753]],[2754,2753,["l",2,5507]],
[2756,1405,["s",4,53]],[2756,1431,["s",4,53]],
[2760,2759,["l",2,5519]],[2761,2760,["l",2,5521]],
[2764,2763,["l",2,5527]],[2766,2765,["l",2,5531]],
[2767,1384,["l",2,2767]],[2777,1389,["l",2,2777]],
[2779,2778,["l",2,5557]],[2782,2781,["l",2,5563]],
[2785,2784,["l",2,5569]],[2787,2786,["l",2,5573]],
[2789,1395,["l",2,2789]],[2791,1396,["l",2,2791]],
[2791,2790,["l",2,5581]],[2796,2795,["l",2,5591]],
[2797,1399,["l",2,2797]],[2800,2736,["F4",7]],
[2801,1401,["l",2,2801]],[2801,2736,["l",5,7]],
[2803,1402,["l",2,2803]],[2812,2811,["l",2,5623]],
[2819,1410,["l",2,2819]],[2820,2819,["l",2,5639]],
[2821,2820,["l",2,5641]],[2824,2823,["l",2,5647]],
[2826,2825,["l",2,5651]],[2827,2826,["l",2,5653]],
[2829,2828,["l",2,5657]],[2830,2829,["l",2,5659]],
[2833,1417,["l",2,2833]],[2835,2834,["l",2,5669]],
[2837,1419,["l",2,2837]],[2842,2841,["l",2,5683]],
[2843,1422,["l",2,2843]],[2845,2844,["l",2,5689]],
[2847,2846,["l",2,5693]],[2851,1426,["l",2,2851]],
[2851,2850,["l",2,5701]],[2856,2855,["l",2,5711]],
[2857,1429,["l",2,2857]],[2859,2858,["l",2,5717]],
[2861,1431,["l",2,2861]],[2862,1405,["s",4,53]],
[2862,1431,["s",4,53]],[2862,2756,["s",4,53]],
[2863,2808,["l",3,53]],[2863,2808,["G2",53]],
[2863,2809,["G2",53]],[2863,2862,["G2",53]],
[2869,2868,["l",2,5737]],[2871,2870,["l",2,5741]],
[2872,2871,["l",2,5743]],[2875,2874,["l",2,5749]],
[2879,1440,["l",2,2879]],[2887,1444,["l",2,2887]],
[2890,2889,["l",2,5779]],[2892,2891,["l",2,5783]],
[2896,2895,["l",2,5791]],[2897,1449,["l",2,2897]],
[2901,2900,["l",2,5801]],[2903,1452,["l",2,2903]],
[2904,2903,["l",2,5807]],[2907,2906,["l",2,5813]],
[2909,1455,["l",2,2909]],[2911,2910,["l",2,5821]],
[2914,2913,["l",2,5827]],[2917,1459,["l",2,2917]],
[2920,2919,["l",2,5839]],[2922,2921,["l",2,5843]],
[2925,2924,["l",2,5849]],[2926,2925,["l",2,5851]],
[2927,1464,["l",2,2927]],[2929,2928,["l",2,5857]],
[2931,2930,["l",2,5861]],[2934,2933,["l",2,5867]],
[2935,2934,["l",2,5869]],[2939,1470,["l",2,2939]],
[2940,2939,["l",2,5879]],[2941,2940,["l",2,5881]],
[2949,2948,["l",2,5897]],[2952,2951,["l",2,5903]],
[2953,1477,["l",2,2953]],[2957,1479,["l",2,2957]],
[2962,2961,["l",2,5923]],[2963,1482,["l",2,2963]],
[2964,2963,["l",2,5927]],[2969,1485,["l",2,2969]],
[2970,2969,["l",2,5939]],[2971,1486,["l",2,2971]],
[2977,2976,["l",2,5953]],[2991,2990,["l",2,5981]],
[2994,2993,["l",2,5987]],[2999,1500,["l",2,2999]],
[3001,1501,["l",2,3001]],[3004,3003,["l",2,6007]],
[3006,3005,["l",2,6011]],[3011,1506,["l",2,3011]],
[3015,3014,["l",2,6029]],[3019,1510,["l",2,3019]],
[3019,3018,["l",2,6037]],[3022,3021,["l",2,6043]],
[3023,1512,["l",2,3023]],[3024,3023,["l",2,6047]],
[3027,3026,["l",2,6053]],[3034,3033,["l",2,6067]],
[3037,1519,["l",2,3037]],[3037,3036,["l",2,6073]],
[3040,3039,["l",2,6079]],[3041,1521,["l",2,3041]],
[3042,2915,["u",4,23]],[3042,3036,["u",4,23]],
[3045,3044,["l",2,6089]],[3046,3045,["l",2,6091]],
[3049,1525,["l",2,3049]],[3051,3050,["l",2,6101]],
[3057,3056,["l",2,6113]],[3061,1531,["l",2,3061]],
[3061,3060,["l",2,6121]],[3066,3065,["l",2,6131]],
[3067,1534,["l",2,3067]],[3067,3066,["l",2,6133]],
[3072,3071,["l",2,6143]],[3076,3075,["l",2,6151]],
[3079,1540,["l",2,3079]],[3082,3081,["l",2,6163]],
[3083,1542,["l",2,3083]],[3087,3086,["l",2,6173]],
[3089,1545,["l",2,3089]],[3099,3098,["l",2,6197]],
[3100,3099,["l",2,6199]],[3102,3101,["l",2,6203]],
[3106,3105,["l",2,6211]],[3109,1555,["l",2,3109]],
[3109,3108,["l",2,6217]],[3111,3110,["l",2,6221]],
[3115,3114,["l",2,6229]],[3119,1560,["l",2,3119]],
[3120,1878,["s",10,5]],[3121,1561,["l",2,3121]],
[3121,3120,["l",2,6241]],[3121,3120,["s",4,79]],
[3124,3123,["l",2,6247]],[3129,3128,["l",2,6257]],
[3130,1878,["s",10,5]],[3130,3120,["s",10,5]],
[3132,3131,["l",2,6263]],[3135,3134,["l",2,6269]],
[3136,3135,["l",2,6271]],[3137,1569,["l",2,3137]],
[3139,3138,["l",2,6277]],[3144,3143,["l",2,6287]],
[3150,3149,["l",2,6299]],[3151,3150,["l",2,6301]],
[3156,3155,["l",2,6311]],[3159,3158,["l",2,6317]],
[3160,3121,["s",4,79]],[3162,3161,["l",2,6323]],
[3163,1582,["l",2,3163]],[3165,3164,["l",2,6329]],
[3167,1584,["l",2,3167]],[3169,1585,["l",2,3169]],
[3169,3136,["l",3,97]],[3169,3168,["l",2,6337]],
[3172,3171,["l",2,6343]],[3177,3176,["l",2,6353]],
[3180,3179,["l",2,6359]],[3181,1591,["l",2,3181]],
[3181,3180,["l",2,6361]],[3184,3183,["l",2,6367]],
[3187,1594,["l",2,3187]],[3187,3186,["l",2,6373]],
[3190,3189,["l",2,6379]],[3191,1596,["l",2,3191]],
[3195,3194,["l",2,6389]],[3199,3198,["l",2,6397]],
[3203,1602,["l",2,3203]],[3209,1605,["l",2,3209]],
[3211,3210,["l",2,6421]],[3214,3213,["l",2,6427]],
[3217,1609,["l",2,3217]],[3221,1611,["l",2,3221]],
[3221,3192,["l",5,11]],[3225,3224,["l",2,6449]],
[3226,3225,["l",2,6451]],[3229,1615,["l",2,3229]],
[3235,3234,["l",2,6469]],[3237,3236,["l",2,6473]],
[3241,3240,["l",2,6481]],[3246,3245,["l",2,6491]],
[3251,1626,["l",2,3251]],[3253,1627,["l",2,3253]],
[3255,3075,["o+",22,2]],[3255,3084,["o+",22,2]],
[3257,1629,["l",2,3257]],[3259,1630,["l",2,3259]],
[3261,3260,["l",2,6521]],[3265,3264,["l",2,6529]],
[3268,2801,["l",6,7]],[3271,1636,["l",2,3271]],
[3274,3273,["l",2,6547]],[3276,3275,["l",2,6551]],
[3277,3276,["l",2,6553]],[3281,3280,["l",2,6561]],
[3281,3280,["s",4,81]],[3282,3281,["l",2,6563]],
[3285,3284,["l",2,6569]],[3286,3285,["l",2,6571]],
[3289,3288,["l",2,6577]],[3291,3290,["l",2,6581]],
[3299,1650,["l",2,3299]],[3300,3299,["l",2,6599]],
[3301,1651,["l",2,3301]],[3304,3303,["l",2,6607]],
[3307,1654,["l",2,3307]],[3310,3309,["l",2,6619]],
[3313,1657,["l",2,3313]],[3319,1660,["l",2,3319]],
[3319,3318,["l",2,6637]],[3323,1662,["l",2,3323]],
[3327,3326,["l",2,6653]],[3329,1665,["l",2,3329]],
[3330,3329,["l",2,6659]],[3331,1666,["l",2,3331]],
[3331,3330,["l",2,6661]],[3337,3336,["l",2,6673]],
[3340,3339,["l",2,6679]],[3343,1672,["l",2,3343]],
[3345,3344,["l",2,6689]],[3346,3345,["l",2,6691]],
[3347,1674,["l",2,3347]],[3351,3350,["l",2,6701]],
[3352,3351,["l",2,6703]],[3355,3354,["l",2,6709]],
[3359,1680,["l",2,3359]],[3360,3359,["l",2,6719]],
[3361,1681,["l",2,3361]],[3367,3366,["l",2,6733]],
[3369,3368,["l",2,6737]],[3371,1686,["l",2,3371]],
[3373,1687,["l",2,3373]],[3381,3380,["l",2,6761]],
[3382,3381,["l",2,6763]],[3389,1695,["l",2,3389]],
[3390,3389,["l",2,6779]],[3391,1696,["l",2,3391]],
[3391,3390,["l",2,6781]],[3396,3395,["l",2,6791]],
[3397,3396,["l",2,6793]],[3400,3367,["u",3,101]],
[3402,3401,["l",2,6803]],[3407,1704,["l",2,3407]],
[3412,3411,["l",2,6823]],[3413,1707,["l",2,3413]],
[3414,3413,["l",2,6827]],[3415,3414,["l",2,6829]],
[3417,3416,["l",2,6833]],[3421,3420,["l",2,6841]],
[3422,1741,["s",4,59]],[3422,1770,["s",4,59]],
[3429,3428,["l",2,6857]],[3430,3429,["l",2,6859]],
[3432,3431,["l",2,6863]],[3433,1717,["l",2,3433]],
[3434,3400,["u",3,101]],[3435,3434,["l",2,6869]],
[3436,3435,["l",2,6871]],[3442,3441,["l",2,6883]],
[3445,3444,["l",2,6889]],[3445,3444,["s",4,83]],
[3449,1725,["l",2,3449]],[3450,3449,["l",2,6899]],
[3454,3453,["l",2,6907]],[3456,3455,["l",2,6911]],
[3457,1729,["l",2,3457]],[3459,3458,["l",2,6917]],
[3461,1731,["l",2,3461]],[3463,1732,["l",2,3463]],
[3467,1734,["l",2,3467]],[3469,1735,["l",2,3469]],
[3474,3473,["l",2,6947]],[3475,3474,["l",2,6949]],
[3480,3479,["l",2,6959]],[3481,3480,["l",2,6961]],
[3484,3483,["l",2,6967]],[3486,3445,["s",4,83]],
[3486,3485,["l",2,6971]],[3489,3488,["l",2,6977]],
[3491,1746,["l",2,3491]],[3492,3491,["l",2,6983]],
[3496,3495,["l",2,6991]],[3499,1750,["l",2,3499]],
[3499,3498,["l",2,6997]],[3501,3500,["l",2,7001]],
[3507,3506,["l",2,7013]],[3510,3509,["l",2,7019]],
[3511,1756,["l",2,3511]],[3514,3513,["l",2,7027]],
[3517,1759,["l",2,3517]],[3520,3519,["l",2,7039]],
[3522,3521,["l",2,7043]],[3527,1764,["l",2,3527]],
[3529,1765,["l",2,3529]],[3529,3528,["l",2,7057]],
[3533,1767,["l",2,3533]],[3535,3534,["l",2,7069]],
[3539,1770,["l",2,3539]],[3540,1741,["s",4,59]],
[3540,1770,["s",4,59]],[3540,3422,["s",4,59]],
[3540,3539,["l",2,7079]],[3541,1771,["l",2,3541]],
[3541,3480,["l",3,59]],[3541,3480,["G2",59]],
[3541,3481,["G2",59]],[3541,3540,["G2",59]],
[3547,1774,["l",2,3547]],[3552,3551,["l",2,7103]],
[3555,3554,["l",2,7109]],[3557,1779,["l",2,3557]],
[3559,1780,["l",2,3559]],[3561,3560,["l",2,7121]],
[3564,3563,["l",2,7127]],[3565,3564,["l",2,7129]],
[3570,3255,["o+",22,2]],[3571,1786,["l",2,3571]],
[3571,3536,["l",3,103]],[3576,3575,["l",2,7151]],
[3580,3579,["l",2,7159]],[3581,1791,["l",2,3581]],
[3583,1792,["l",2,3583]],[3589,3588,["l",2,7177]],
[3593,1797,["l",2,3593]],[3594,3593,["l",2,7187]],
[3597,3596,["l",2,7193]],[3604,3603,["l",2,7207]],
[3606,3605,["l",2,7211]],[3607,1804,["l",2,3607]],
[3607,3606,["l",2,7213]],[3610,3609,["l",2,7219]],
[3613,1807,["l",2,3613]],[3615,3614,["l",2,7229]],
[3617,1809,["l",2,3617]],[3619,3618,["l",2,7237]],
[3620,3429,["l",4,19]],[3620,3430,["o",7,19]],
[3620,3430,["s",6,19]],[3620,3439,["o",7,19]],
[3620,3439,["s",6,19]],[3622,3621,["l",2,7243]],
[3623,1812,["l",2,3623]],[3624,3623,["l",2,7247]],
[3627,3626,["l",2,7253]],[3631,1816,["l",2,3631]],
[3637,1819,["l",2,3637]],[3640,3281,["o",9,9]],
[3640,3281,["o-",8,9]],[3640,3281,["s",8,9]],
[3642,3641,["l",2,7283]],[3643,1822,["l",2,3643]],
[3649,3648,["l",2,7297]],[3654,3653,["l",2,7307]],
[3655,3654,["l",2,7309]],[3659,1830,["l",2,3659]],
[3660,1830,["o+",8,11]],[3660,1861,["s",4,61]],
[3660,1891,["s",4,61]],[3661,3660,["l",2,7321]],
[3666,3665,["l",2,7331]],[3667,3666,["l",2,7333]],
[3671,1836,["l",2,3671]],[3673,1837,["l",2,3673]],
[3675,3674,["l",2,7349]],[3676,3675,["l",2,7351]],
[3677,1839,["l",2,3677]],[3685,3684,["l",2,7369]],
[3691,1846,["l",2,3691]],[3697,1849,["l",2,3697]],
[3697,3696,["l",2,7393]],[3701,1851,["l",2,3701]],
[3706,3705,["l",2,7411]],[3709,1855,["l",2,3709]],
[3709,3708,["l",2,7417]],[3717,3716,["l",2,7433]],
[3719,1860,["l",2,3719]],[3720,3661,["u",3,61]],
[3726,3725,["l",2,7451]],[3727,1864,["l",2,3727]],
[3729,3728,["l",2,7457]],[3730,3729,["l",2,7459]],
[3733,1867,["l",2,3733]],[3739,1870,["l",2,3739]],
[3739,3738,["l",2,7477]],[3741,3740,["l",2,7481]],
[3744,3743,["l",2,7487]],[3745,3744,["l",2,7489]],
[3750,3749,["l",2,7499]],[3754,3753,["l",2,7507]],
[3759,3758,["l",2,7517]],[3761,1881,["l",2,3761]],
[3762,3761,["l",2,7523]],[3765,3764,["l",2,7529]],
[3767,1884,["l",2,3767]],[3769,1885,["l",2,3769]],
[3769,3768,["l",2,7537]],[3771,3770,["l",2,7541]],
[3774,3773,["l",2,7547]],[3775,3774,["l",2,7549]],
[3779,1890,["l",2,3779]],[3780,3779,["l",2,7559]],
[3781,3780,["l",2,7561]],[3782,1861,["s",4,61]],
[3782,1891,["s",4,61]],[3782,3660,["s",4,61]],
[3782,3720,["u",3,61]],[3783,3720,["G2",61]],
[3783,3721,["G2",61]],[3783,3782,["G2",61]],
[3787,3786,["l",2,7573]],[3789,3788,["l",2,7577]],
[3792,3791,["l",2,7583]],[3793,1897,["l",2,3793]],
[3795,3794,["l",2,7589]],[3796,3795,["l",2,7591]],
[3797,1899,["l",2,3797]],[3802,3801,["l",2,7603]],
[3803,1902,["l",2,3803]],[3804,3803,["l",2,7607]],
[3811,3810,["l",2,7621]],[3816,3781,["u",3,107]],
[3820,3819,["l",2,7639]],[3821,1911,["l",2,3821]],
[3822,3821,["l",2,7643]],[3823,1912,["l",2,3823]],
[3825,3824,["l",2,7649]],[3833,1917,["l",2,3833]],
[3835,3834,["l",2,7669]],[3837,3836,["l",2,7673]],
[3841,3840,["l",2,7681]],[3844,3843,["l",2,7687]],
[3846,3845,["l",2,7691]],[3847,1924,["l",2,3847]],
[3850,3849,["l",2,7699]],[3851,1926,["l",2,3851]],
[3852,3816,["u",3,107]],[3852,3851,["l",2,7703]],
[3853,1927,["l",2,3853]],[3855,3315,["o-",22,2]],
[3855,3315,["s",22,2]],[3855,3570,["s",22,2]],
[3855,3720,["s",22,2]],[3855,3810,["o-",22,2]],
[3855,3810,["s",22,2]],[3859,3858,["l",2,7717]],
[3862,3861,["l",2,7723]],[3863,1932,["l",2,3863]],
[3864,3863,["l",2,7727]],[3871,3870,["l",2,7741]],
[3877,1939,["l",2,3877]],[3877,3876,["l",2,7753]],
[3879,3878,["l",2,7757]],[3880,3879,["l",2,7759]],
[3881,1941,["l",2,3881]],[3889,1945,["l",2,3889]],
[3895,3894,["l",2,7789]],[3897,3896,["l",2,7793]],
[3907,1954,["l",2,3907]],[3909,3908,["l",2,7817]],
[3911,1956,["l",2,3911]],[3912,3911,["l",2,7823]],
[3915,3914,["l",2,7829]],[3917,1959,["l",2,3917]],
[3919,1960,["l",2,3919]],[3921,3920,["l",2,7841]],
[3923,1962,["l",2,3923]],[3927,3926,["l",2,7853]],
[3929,1965,["l",2,3929]],[3931,1966,["l",2,3931]],
[3934,3933,["l",2,7867]],[3937,3936,["l",2,7873]],
[3939,3938,["l",2,7877]],[3940,3939,["l",2,7879]],
[3942,3941,["l",2,7883]],[3943,1972,["l",2,3943]],
[3947,1974,["l",2,3947]],[3951,3950,["l",2,7901]],
[3954,3953,["l",2,7907]],[3960,3959,["l",2,7919]],
[3961,3960,["l",2,7921]],[3961,3960,["s",4,89]],
[3964,3963,["l",2,7927]],[3967,1984,["l",2,3967]],
[3967,3966,["l",2,7933]],[3969,3968,["l",2,7937]],
[3975,3974,["l",2,7949]],[3976,3975,["l",2,7951]],
[3982,3981,["l",2,7963]],[3989,1995,["l",2,3989]],
[3997,3960,["l",3,109]],[3997,3996,["l",2,7993]],
[4001,2001,["l",2,4001]],[4003,2002,["l",2,4003]],
[4005,3961,["s",4,89]],[4005,4004,["l",2,8009]],
[4006,4005,["l",2,8011]],[4007,2004,["l",2,4007]],
[4009,4008,["l",2,8017]],[4013,2007,["l",2,4013]],
[4019,2010,["l",2,4019]],[4020,4019,["l",2,8039]],
[4021,2011,["l",2,4021]],[4027,2014,["l",2,4027]],
[4027,4026,["l",2,8053]],[4030,4029,["l",2,8059]],
[4035,4034,["l",2,8069]],[4041,4040,["l",2,8081]],
[4044,4043,["l",2,8087]],[4045,4044,["l",2,8089]],
[4047,4046,["l",2,8093]],[4049,2025,["l",2,4049]],
[4051,2026,["l",2,4051]],[4051,4050,["l",2,8101]],
[4056,4055,["l",2,8111]],[4057,2029,["l",2,4057]],
[4059,4058,["l",2,8117]],[4062,4061,["l",2,8123]],
[4069,3906,["l",4,25]],[4073,2037,["l",2,4073]],
[4074,4073,["l",2,8147]],[4079,2040,["l",2,4079]],
[4081,4080,["l",2,8161]],[4084,4083,["l",2,8167]],
[4086,4085,["l",2,8171]],[4090,4089,["l",2,8179]],
[4091,2046,["l",2,4091]],[4093,2047,["l",2,4093]],
[4095,1365,["o+",8,8]],[4095,3069,["u",13,2]],
[4095,3315,["u",7,4]],[4095,3641,["u",5,8]],
[4095,3937,["l",12,2]],[4095,4033,["u",3,64]],
[4095,4092,["u",13,2]],[4096,4095,["l",2,8191]],
[4097,3855,["u",4,16]],[4097,4095,["l",2,4096]],
[4097,4095,["s",4,64]],[4098,4095,["u",13,2]],
[4099,2050,["l",2,4099]],[4105,4104,["l",2,8209]],
[4110,4109,["l",2,8219]],[4111,2056,["l",2,4111]],
[4111,4110,["l",2,8221]],[4116,4115,["l",2,8231]],
[4117,4116,["l",2,8233]],[4119,4118,["l",2,8237]],
[4122,4121,["l",2,8243]],[4127,2064,["l",2,4127]],
[4129,2065,["l",2,4129]],[4132,4131,["l",2,8263]],
[4133,2067,["l",2,4133]],[4135,4134,["l",2,8269]],
[4137,4136,["l",2,8273]],[4139,2070,["l",2,4139]],
[4144,4143,["l",2,8287]],[4146,4145,["l",2,8291]],
[4147,4146,["l",2,8293]],[4149,4148,["l",2,8297]],
[4153,2077,["l",2,4153]],[4156,4155,["l",2,8311]],
[4157,2079,["l",2,4157]],[4159,2080,["l",2,4159]],
[4159,4158,["l",2,8317]],[4161,4095,["G2",64]],
[4165,4164,["l",2,8329]],[4177,2089,["l",2,4177]],
[4177,4176,["l",2,8353]],[4182,4181,["l",2,8363]],
[4185,4184,["l",2,8369]],[4189,4188,["l",2,8377]],
[4194,4193,["l",2,8387]],[4195,4194,["l",2,8389]],
[4201,2101,["l",2,4201]],[4210,4209,["l",2,8419]],
[4211,2106,["l",2,4211]],[4212,4211,["l",2,8423]],
[4215,4214,["l",2,8429]],[4216,4215,["l",2,8431]],
[4217,2109,["l",2,4217]],[4219,2110,["l",2,4219]],
[4222,4221,["l",2,8443]],[4224,4223,["l",2,8447]],
[4229,2115,["l",2,4229]],[4231,2116,["l",2,4231]],
[4231,4230,["l",2,8461]],[4234,4233,["l",2,8467]],
[4241,2121,["l",2,4241]],[4243,2122,["l",2,4243]],
[4251,4250,["l",2,8501]],[4253,2127,["l",2,4253]],
[4256,4219,["u",3,113]],[4257,4256,["l",2,8513]],
[4259,2130,["l",2,4259]],[4261,2131,["l",2,4261]],
[4261,4260,["l",2,8521]],[4264,4263,["l",2,8527]],
[4269,4268,["l",2,8537]],[4270,4269,["l",2,8539]],
[4271,2136,["l",2,4271]],[4272,4271,["l",2,8543]],
[4273,2137,["l",2,4273]],[4275,4202,["o-",10,7]],
[4282,4281,["l",2,8563]],[4283,2142,["l",2,4283]],
[4287,4286,["l",2,8573]],[4289,2145,["l",2,4289]],
[4291,4290,["l",2,8581]],[4294,4256,["u",3,113]],
[4297,2149,["l",2,4297]],[4299,4298,["l",2,8597]],
[4300,4299,["l",2,8599]],[4305,4304,["l",2,8609]],
[4312,4311,["l",2,8623]],[4314,4313,["l",2,8627]],
[4315,4314,["l",2,8629]],[4321,4320,["l",2,8641]],
[4324,4323,["l",2,8647]],[4327,2164,["l",2,4327]],
[4332,4331,["l",2,8663]],[4335,4334,["l",2,8669]],
[4337,2169,["l",2,4337]],[4339,2170,["l",2,4339]],
[4339,4338,["l",2,8677]],[4341,4340,["l",2,8681]],
[4345,4344,["l",2,8689]],[4347,4346,["l",2,8693]],
[4349,2175,["l",2,4349]],[4350,4349,["l",2,8699]],
[4354,4353,["l",2,8707]],[4357,2179,["l",2,4357]],
[4357,4356,["l",2,8713]],[4360,4359,["l",2,8719]],
[4363,2182,["l",2,4363]],[4366,4365,["l",2,8731]],
[4369,4095,["l",4,16]],[4369,4097,["s",6,16]],
[4369,4368,["l",2,8737]],[4371,4370,["l",2,8741]],
[4372,3640,["o",17,3]],[4372,3640,["o-",16,3]],
[4372,3640,["s",16,3]],[4372,3660,["o",17,3]],
[4372,3660,["s",16,3]],[4372,3690,["o",17,3]],
[4372,3690,["s",16,3]],[4372,4356,["o",17,3]],
[4372,4356,["s",16,3]],[4373,2187,["l",2,4373]],
[4374,4373,["l",2,8747]],[4377,4376,["l",2,8753]],
[4380,4372,["o",17,3]],[4380,4372,["o-",16,3]],
[4380,4372,["s",16,3]],[4381,4380,["l",2,8761]],
[4390,4389,["l",2,8779]],[4391,2196,["l",2,4391]],
[4392,4391,["l",2,8783]],[4397,2199,["l",2,4397]],
[4402,4401,["l",2,8803]],[4404,4403,["l",2,8807]],
[4409,2205,["l",2,4409]],[4410,4409,["l",2,8819]],
[4411,4410,["l",2,8821]],[4416,4415,["l",2,8831]],
[4419,4418,["l",2,8837]],[4420,4419,["l",2,8839]],
[4421,2211,["l",2,4421]],[4422,2245,["s",4,67]],
[4422,2278,["s",4,67]],[4423,2212,["l",2,4423]],
[4425,4424,["l",2,8849]],[4431,4430,["l",2,8861]],
[4432,4431,["l",2,8863]],[4434,4433,["l",2,8867]],
[4441,2221,["l",2,4441]],[4444,4443,["l",2,8887]],
[4447,2224,["l",2,4447]],[4447,4446,["l",2,8893]],
[4451,2226,["l",2,4451]],[4457,2229,["l",2,4457]],
[4462,4461,["l",2,8923]],[4463,2232,["l",2,4463]],
[4465,4464,["l",2,8929]],[4467,4466,["l",2,8933]],
[4471,4470,["l",2,8941]],[4476,4475,["l",2,8951]],
[4481,2241,["l",2,4481]],[4482,4481,["l",2,8963]],
[4483,2242,["l",2,4483]],[4485,4484,["l",2,8969]],
[4486,4485,["l",2,8971]],[4488,4423,["u",3,67]],
[4493,2247,["l",2,4493]],[4500,4499,["l",2,8999]],
[4501,4500,["l",2,9001]],[4504,4503,["l",2,9007]],
[4506,4505,["l",2,9011]],[4507,2254,["l",2,4507]],
[4507,4506,["l",2,9013]],[4513,2257,["l",2,4513]],
[4515,4514,["l",2,9029]],[4517,2259,["l",2,4517]],
[4519,2260,["l",2,4519]],[4521,4520,["l",2,9041]],
[4522,4521,["l",2,9043]],[4523,2262,["l",2,4523]],
[4525,4524,["l",2,9049]],[4530,4529,["l",2,9059]],
[4534,4533,["l",2,9067]],[4546,4545,["l",2,9091]],
[4547,2274,["l",2,4547]],[4549,2275,["l",2,4549]],
[4552,4551,["l",2,9103]],[4555,4554,["l",2,9109]],
[4556,2245,["s",4,67]],[4556,2278,["s",4,67]],
[4556,4422,["s",4,67]],[4556,4488,["u",3,67]],
[4557,4488,["G2",67]],[4557,4489,["G2",67]],
[4557,4556,["G2",67]],[4561,2281,["l",2,4561]],
[4564,4563,["l",2,9127]],[4567,2284,["l",2,4567]],
[4567,4566,["l",2,9133]],[4569,4568,["l",2,9137]],
[4576,4575,["l",2,9151]],[4579,4578,["l",2,9157]],
[4581,4580,["l",2,9161]],[4583,2292,["l",2,4583]],
[4587,4586,["l",2,9173]],[4591,2296,["l",2,4591]],
[4591,4590,["l",2,9181]],[4594,4593,["l",2,9187]],
[4597,2299,["l",2,4597]],[4599,4033,["3D4",8]],
[4599,4097,["F4",8]],[4599,4097,["o-",8,8]],
[4599,4097,["s",8,8]],[4600,4599,["l",2,9199]],
[4602,4601,["l",2,9203]],[4603,2302,["l",2,4603]],
[4605,4604,["l",2,9209]],[4611,4610,["l",2,9221]],
[4614,4613,["l",2,9227]],[4620,4619,["l",2,9239]],
[4621,2311,["l",2,4621]],[4621,4620,["l",2,9241]],
[4629,4628,["l",2,9257]],[4637,2319,["l",2,4637]],
[4639,2320,["l",2,4639]],[4639,4638,["l",2,9277]],
[4641,4640,["l",2,9281]],[4642,4641,["l",2,9283]],
[4643,2322,["l",2,4643]],[4647,4646,["l",2,9293]],
[4649,2325,["l",2,4649]],[4651,2326,["l",2,4651]],
[4656,4655,["l",2,9311]],[4657,2329,["l",2,4657]],
[4660,4659,["l",2,9319]],[4662,4661,["l",2,9323]],
[4663,2332,["l",2,4663]],[4669,4668,["l",2,9337]],
[4671,4670,["l",2,9341]],[4672,4671,["l",2,9343]],
[4673,2337,["l",2,4673]],[4675,4674,["l",2,9349]],
[4679,2340,["l",2,4679]],[4681,4599,["l",5,8]],
[4686,4685,["l",2,9371]],[4689,4688,["l",2,9377]],
[4691,2346,["l",2,4691]],[4696,4695,["l",2,9391]],
[4699,4698,["l",2,9397]],[4702,4701,["l",2,9403]],
[4703,2352,["l",2,4703]],[4705,4704,["l",2,9409]],
[4705,4704,["s",4,97]],[4707,4706,["l",2,9413]],
[4710,4709,["l",2,9419]],[4711,4710,["l",2,9421]],
[4716,4715,["l",2,9431]],[4717,4716,["l",2,9433]],
[4719,4718,["l",2,9437]],[4720,4719,["l",2,9439]],
[4721,2361,["l",2,4721]],[4723,2362,["l",2,4723]],
[4729,2365,["l",2,4729]],[4731,4730,["l",2,9461]],
[4732,4731,["l",2,9463]],[4733,2367,["l",2,4733]],
[4734,4733,["l",2,9467]],[4737,4736,["l",2,9473]],
[4740,4739,["l",2,9479]],[4746,4745,["l",2,9491]],
[4749,4748,["l",2,9497]],[4751,2376,["l",2,4751]],
[4753,4705,["s",4,97]],[4756,4755,["l",2,9511]],
[4759,2380,["l",2,4759]],[4761,4760,["l",2,9521]],
[4767,4766,["l",2,9533]],[4770,4769,["l",2,9539]],
[4774,4773,["l",2,9547]],[4776,4775,["l",2,9551]],
[4783,2392,["l",2,4783]],[4787,2394,["l",2,4787]],
[4789,2395,["l",2,4789]],[4793,2397,["l",2,4793]],
[4794,4793,["l",2,9587]],[4799,2400,["l",2,4799]],
[4801,2401,["l",2,4801]],[4801,4800,["l",2,9601]],
[4807,4806,["l",2,9613]],[4810,4809,["l",2,9619]],
[4812,4811,["l",2,9623]],[4813,2407,["l",2,4813]],
[4815,4814,["l",2,9629]],[4816,4815,["l",2,9631]],
[4817,2409,["l",2,4817]],[4822,4821,["l",2,9643]],
[4825,4824,["l",2,9649]],[4831,2416,["l",2,4831]],
[4831,4830,["l",2,9661]],[4836,4069,["o+",12,5]],
[4839,4838,["l",2,9677]],[4840,4839,["l",2,9679]],
[4845,4844,["l",2,9689]],[4849,4848,["l",2,9697]],
[4860,4859,["l",2,9719]],[4861,2431,["l",2,4861]],
[4861,4860,["l",2,9721]],[4867,4866,["l",2,9733]],
[4870,4869,["l",2,9739]],[4871,2436,["l",2,4871]],
[4872,4871,["l",2,9743]],[4875,4874,["l",2,9749]],
[4877,2439,["l",2,4877]],[4884,4883,["l",2,9767]],
[4885,4884,["l",2,9769]],[4889,2445,["l",2,4889]],
[4891,4890,["l",2,9781]],[4894,4893,["l",2,9787]],
[4896,2610,["s",6,17]],[4896,4895,["l",2,9791]],
[4902,4901,["l",2,9803]],[4903,2452,["l",2,4903]],
[4906,4905,["l",2,9811]],[4909,2455,["l",2,4909]],
[4909,4908,["l",2,9817]],[4915,4914,["l",2,9829]],
[4917,4916,["l",2,9833]],[4919,2460,["l",2,4919]],
[4920,4919,["l",2,9839]],[4921,4745,["u",4,27]],
[4921,4880,["l",3,121]],[4926,4925,["l",2,9851]],
[4929,4928,["l",2,9857]],[4930,2610,["s",6,17]],
[4930,4896,["s",6,17]],[4930,4929,["l",2,9859]],
[4931,2466,["l",2,4931]],[4933,2467,["l",2,4933]],
[4936,4935,["l",2,9871]],[4937,2469,["l",2,4937]],
[4942,4941,["l",2,9883]],[4943,2472,["l",2,4943]],
[4944,4943,["l",2,9887]],[4951,2476,["l",2,4951]],
[4951,4950,["l",2,9901]],[4954,4953,["l",2,9907]],
[4957,2479,["l",2,4957]],[4962,4961,["l",2,9923]],
[4965,4964,["l",2,9929]],[4966,4965,["l",2,9931]],
[4967,2484,["l",2,4967]],[4969,2485,["l",2,4969]],
[4970,2521,["s",4,71]],[4970,2556,["s",4,71]],
[4971,4970,["l",2,9941]],[4973,2487,["l",2,4973]],
[4975,4974,["l",2,9949]],[4984,4983,["l",2,9967]],
[4987,2494,["l",2,4987]],[4987,4986,["l",2,9973]],
[4993,2497,["l",2,4993]],[4999,2500,["l",2,4999]],
[5003,2502,["l",2,5003]],[5004,5003,["l",2,10007]],
[5005,5004,["l",2,10009]],[5009,2505,["l",2,5009]],
[5011,2506,["l",2,5011]],[5019,5018,["l",2,10037]],
[5020,5019,["l",2,10039]],[5021,2511,["l",2,5021]],
[5023,2512,["l",2,5023]],[5031,5030,["l",2,10061]],
[5034,5033,["l",2,10067]],[5035,5034,["l",2,10069]],
[5039,2520,["l",2,5039]],[5040,5039,["l",2,10079]],
[5046,5045,["l",2,10091]],[5047,5046,["l",2,10093]],
[5050,5049,["l",2,10099]],[5051,2526,["l",2,5051]],
[5052,5051,["l",2,10103]],[5056,5055,["l",2,10111]],
[5059,2530,["l",2,5059]],[5067,5066,["l",2,10133]],
[5070,5069,["l",2,10139]],[5071,5070,["l",2,10141]],
[5076,5075,["l",2,10151]],[5077,2539,["l",2,5077]],
[5080,5079,["l",2,10159]],[5081,2541,["l",2,5081]],
[5082,5081,["l",2,10163]],[5085,5084,["l",2,10169]],
[5087,2544,["l",2,5087]],[5089,5088,["l",2,10177]],
[5091,5090,["l",2,10181]],[5097,5096,["l",2,10193]],
[5099,2550,["l",2,5099]],[5101,2551,["l",2,5101]],
[5101,5100,["l",2,10201]],[5101,5100,["s",4,101]],
[5106,5105,["l",2,10211]],[5107,2554,["l",2,5107]],
[5112,2521,["s",4,71]],[5112,2556,["s",4,71]],
[5112,4970,["s",4,71]],[5112,5111,["l",2,10223]],
[5113,2557,["l",2,5113]],[5113,5040,["l",3,71]],
[5113,5040,["G2",71]],[5113,5041,["G2",71]],
[5113,5112,["G2",71]],[5115,4097,["o-",12,4]],
[5119,2560,["l",2,5119]],[5122,5121,["l",2,10243]],
[5124,5123,["l",2,10247]],[5127,5126,["l",2,10253]],
[5130,5129,["l",2,10259]],[5134,5133,["l",2,10267]],
[5136,5135,["l",2,10271]],[5137,5136,["l",2,10273]],
[5145,5144,["l",2,10289]],[5147,2574,["l",2,5147]],
[5151,5101,["s",4,101]],[5151,5150,["l",2,10301]],
[5152,5151,["l",2,10303]],[5153,2577,["l",2,5153]],
[5157,5156,["l",2,10313]],[5161,5160,["l",2,10321]],
[5166,5165,["l",2,10331]],[5167,2584,["l",2,5167]],
[5167,5166,["l",2,10333]],[5169,5168,["l",2,10337]],
[5171,2586,["l",2,5171]],[5172,5171,["l",2,10343]],
[5179,2590,["l",2,5179]],[5179,5178,["l",2,10357]],
[5185,5184,["l",2,10369]],[5189,2595,["l",2,5189]],
[5196,5195,["l",2,10391]],[5197,2599,["l",2,5197]],
[5200,5199,["l",2,10399]],[5208,5167,["u",3,125]],
[5209,2605,["l",2,5209]],[5214,5213,["l",2,10427]],
[5215,5214,["l",2,10429]],[5217,5216,["l",2,10433]],
[5227,2614,["l",2,5227]],[5227,5226,["l",2,10453]],
[5229,5228,["l",2,10457]],[5230,5229,["l",2,10459]],
[5231,2616,["l",2,5231]],[5232,5231,["l",2,10463]],
[5233,2617,["l",2,5233]],[5237,2619,["l",2,5237]],
[5239,5238,["l",2,10477]],[5244,5243,["l",2,10487]],
[5250,5249,["l",2,10499]],[5251,5250,["l",2,10501]],
[5256,2665,["s",4,73]],[5256,2701,["s",4,73]],
[5257,5256,["l",2,10513]],[5261,2631,["l",2,5261]],
[5265,5264,["l",2,10529]],[5266,5265,["l",2,10531]],
[5273,2637,["l",2,5273]],[5279,2640,["l",2,5279]],
[5280,5279,["l",2,10559]],[5281,2641,["l",2,5281]],
[5284,5283,["l",2,10567]],[5295,5294,["l",2,10589]],
[5297,2649,["l",2,5297]],[5299,5298,["l",2,10597]],
[5301,5300,["l",2,10601]],[5303,2652,["l",2,5303]],
[5304,5303,["l",2,10607]],[5305,5304,["l",2,10609]],
[5305,5304,["s",4,103]],[5307,5306,["l",2,10613]],
[5309,2655,["l",2,5309]],[5314,5313,["l",2,10627]],
[5316,5315,["l",2,10631]],[5320,5319,["l",2,10639]],
[5323,2662,["l",2,5323]],[5326,5325,["l",2,10651]],
[5328,5257,["u",3,73]],[5329,5328,["l",2,10657]],
[5332,5331,["l",2,10663]],[5333,2667,["l",2,5333]],
[5334,5333,["l",2,10667]],[5344,5343,["l",2,10687]],
[5346,5345,["l",2,10691]],[5347,2674,["l",2,5347]],
[5351,2676,["l",2,5351]],[5355,4095,["2E6",4]],
[5355,4369,["o+",12,4]],[5355,5115,["s",12,4]],
[5355,5354,["l",2,10709]],[5356,5305,["s",4,103]],
[5356,5355,["l",2,10711]],[5362,5361,["l",2,10723]],
[5365,5364,["l",2,10729]],[5367,5366,["l",2,10733]],
[5370,5369,["l",2,10739]],[5377,5376,["l",2,10753]],
[5381,2691,["l",2,5381]],[5386,5385,["l",2,10771]],
[5387,2694,["l",2,5387]],[5391,5390,["l",2,10781]],
[5393,2697,["l",2,5393]],[5395,5394,["l",2,10789]],
[5399,2700,["l",2,5399]],[5400,5399,["l",2,10799]],
[5402,2665,["s",4,73]],[5402,2701,["s",4,73]],
[5402,5256,["s",4,73]],[5402,5328,["u",3,73]],
[5403,5328,["G2",73]],[5403,5329,["G2",73]],
[5403,5402,["G2",73]],[5407,2704,["l",2,5407]],
[5413,2707,["l",2,5413]],[5416,5415,["l",2,10831]],
[5417,2709,["l",2,5417]],[5419,2710,["l",2,5419]],
[5419,5376,["l",3,127]],[5419,5418,["l",2,10837]],
[5424,5423,["l",2,10847]],[5427,5426,["l",2,10853]],
[5430,5429,["l",2,10859]],[5431,2716,["l",2,5431]],
[5431,5430,["l",2,10861]],[5434,5433,["l",2,10867]],
[5437,2719,["l",2,5437]],[5441,2721,["l",2,5441]],
[5442,5441,["l",2,10883]],[5443,2722,["l",2,5443]],
[5445,5444,["l",2,10889]],[5446,5445,["l",2,10891]],
[5449,2725,["l",2,5449]],[5452,5451,["l",2,10903]],
[5455,5454,["l",2,10909]],[5461,5355,["l",7,4]],
[5461,5419,["u",3,128]],[5469,5468,["l",2,10937]],
[5470,5469,["l",2,10939]],[5471,2736,["l",2,5471]],
[5475,5474,["l",2,10949]],[5477,2739,["l",2,5477]],
[5479,2740,["l",2,5479]],[5479,5478,["l",2,10957]],
[5483,2742,["l",2,5483]],[5487,5486,["l",2,10973]],
[5490,5489,["l",2,10979]],[5494,5493,["l",2,10987]],
[5497,5496,["l",2,10993]],[5501,2751,["l",2,5501]],
[5502,5501,["l",2,11003]],[5503,2752,["l",2,5503]],
[5507,2754,["l",2,5507]],[5514,5513,["l",2,11027]],
[5519,2760,["l",2,5519]],[5521,2761,["l",2,5521]],
[5524,5523,["l",2,11047]],[5527,2764,["l",2,5527]],
[5529,5528,["l",2,11057]],[5530,5529,["l",2,11059]],
[5531,2766,["l",2,5531]],[5535,5534,["l",2,11069]],
[5536,5535,["l",2,11071]],[5542,5541,["l",2,11083]],
[5544,5543,["l",2,11087]],[5547,5546,["l",2,11093]],
[5557,2779,["l",2,5557]],[5557,5556,["l",2,11113]],
[5559,5558,["l",2,11117]],[5560,5559,["l",2,11119]],
[5563,2782,["l",2,5563]],[5566,5565,["l",2,11131]],
[5569,2785,["l",2,5569]],[5573,2787,["l",2,5573]],
[5575,5574,["l",2,11149]],[5580,5579,["l",2,11159]],
[5581,2791,["l",2,5581]],[5581,5580,["l",2,11161]],
[5586,5585,["l",2,11171]],[5587,5586,["l",2,11173]],
[5589,5588,["l",2,11177]],[5591,2796,["l",2,5591]],
[5599,5598,["l",2,11197]],[5607,5606,["l",2,11213]],
[5620,5619,["l",2,11239]],[5622,5621,["l",2,11243]],
[5623,2812,["l",2,5623]],[5626,5625,["l",2,11251]],
[5629,5628,["l",2,11257]],[5631,5630,["l",2,11261]],
[5637,5636,["l",2,11273]],[5639,2820,["l",2,5639]],
[5640,5639,["l",2,11279]],[5641,2821,["l",2,5641]],
[5644,5643,["l",2,11287]],[5647,2824,["l",2,5647]],
[5650,5649,["l",2,11299]],[5651,2826,["l",2,5651]],
[5653,2827,["l",2,5653]],[5656,5655,["l",2,11311]],
[5657,2829,["l",2,5657]],[5659,2830,["l",2,5659]],
[5659,5658,["l",2,11317]],[5661,5660,["l",2,11321]],
[5665,5664,["l",2,11329]],[5669,2835,["l",2,5669]],
[5676,5675,["l",2,11351]],[5677,5676,["l",2,11353]],
[5683,2842,["l",2,5683]],[5685,5684,["l",2,11369]],
[5689,2845,["l",2,5689]],[5692,5691,["l",2,11383]],
[5693,2847,["l",2,5693]],[5697,5696,["l",2,11393]],
[5700,5699,["l",2,11399]],[5701,2851,["l",2,5701]],
[5706,5705,["l",2,11411]],[5711,2856,["l",2,5711]],
[5712,5711,["l",2,11423]],[5717,2859,["l",2,5717]],
[5719,5718,["l",2,11437]],[5720,5677,["u",3,131]],
[5722,5721,["l",2,11443]],[5724,5723,["l",2,11447]],
[5725,5724,["l",2,11449]],[5725,5724,["s",4,107]],
[5734,5733,["l",2,11467]],[5736,5735,["l",2,11471]],
[5737,2869,["l",2,5737]],[5741,2871,["l",2,5741]],
[5742,5741,["l",2,11483]],[5743,2872,["l",2,5743]],
[5745,5744,["l",2,11489]],[5746,5745,["l",2,11491]],
[5749,2875,["l",2,5749]],[5749,5748,["l",2,11497]],
[5752,5751,["l",2,11503]],[5760,5759,["l",2,11519]],
[5764,5720,["u",3,131]],[5764,5763,["l",2,11527]],
[5775,5774,["l",2,11549]],[5776,5775,["l",2,11551]],
[5778,5725,["s",4,107]],[5779,2890,["l",2,5779]],
[5783,2892,["l",2,5783]],[5790,5789,["l",2,11579]],
[5791,2896,["l",2,5791]],[5794,5793,["l",2,11587]],
[5797,5796,["l",2,11593]],[5799,5798,["l",2,11597]],
[5801,2901,["l",2,5801]],[5807,2904,["l",2,5807]],
[5809,5808,["l",2,11617]],[5811,5810,["l",2,11621]],
[5813,2907,["l",2,5813]],[5817,5816,["l",2,11633]],
[5821,2911,["l",2,5821]],[5827,2914,["l",2,5827]],
[5829,5828,["l",2,11657]],[5839,2920,["l",2,5839]],
[5839,5838,["l",2,11677]],[5841,5840,["l",2,11681]],
[5843,2922,["l",2,5843]],[5845,5844,["l",2,11689]],
[5849,2925,["l",2,5849]],[5850,5849,["l",2,11699]],
[5851,2926,["l",2,5851]],[5851,5850,["l",2,11701]],
[5857,2929,["l",2,5857]],[5859,5858,["l",2,11717]],
[5860,5859,["l",2,11719]],[5861,2931,["l",2,5861]],
[5866,5865,["l",2,11731]],[5867,2934,["l",2,5867]],
[5869,2935,["l",2,5869]],[5872,5871,["l",2,11743]],
[5879,2940,["l",2,5879]],[5881,2941,["l",2,5881]],
[5889,5888,["l",2,11777]],[5890,5889,["l",2,11779]],
[5892,5891,["l",2,11783]],[5895,5894,["l",2,11789]],
[5897,2949,["l",2,5897]],[5901,5900,["l",2,11801]],
[5903,2952,["l",2,5903]],[5904,5903,["l",2,11807]],
[5907,5906,["l",2,11813]],[5911,5910,["l",2,11821]],
[5914,5913,["l",2,11827]],[5916,5915,["l",2,11831]],
[5917,5916,["l",2,11833]],[5920,5919,["l",2,11839]],
[5923,2962,["l",2,5923]],[5927,2964,["l",2,5927]],
[5932,5931,["l",2,11863]],[5934,5933,["l",2,11867]],
[5939,2970,["l",2,5939]],[5941,5940,["l",2,11881]],
[5941,5940,["s",4,109]],[5944,5943,["l",2,11887]],
[5949,5948,["l",2,11897]],[5952,5951,["l",2,11903]],
[5953,2977,["l",2,5953]],[5955,5954,["l",2,11909]],
[5962,5961,["l",2,11923]],[5964,5963,["l",2,11927]],
[5967,5966,["l",2,11933]],[5970,5969,["l",2,11939]],
[5971,5970,["l",2,11941]],[5977,5976,["l",2,11953]],
[5980,5979,["l",2,11959]],[5981,2991,["l",2,5981]],
[5985,5984,["l",2,11969]],[5986,5985,["l",2,11971]],
[5987,2994,["l",2,5987]],[5991,5990,["l",2,11981]],
[5994,5993,["l",2,11987]],[5995,5941,["s",4,109]],
[6004,6003,["l",2,12007]],[6006,6005,["l",2,12011]],
[6007,3004,["l",2,6007]],[6011,3006,["l",2,6011]],
[6019,6018,["l",2,12037]],[6021,6020,["l",2,12041]],
[6022,6021,["l",2,12043]],[6025,6024,["l",2,12049]],
[6029,3015,["l",2,6029]],[6036,6035,["l",2,12071]],
[6037,3019,["l",2,6037]],[6037,6036,["l",2,12073]],
[6043,3022,["l",2,6043]],[6047,3024,["l",2,6047]],
[6049,6048,["l",2,12097]],[6051,6050,["l",2,12101]],
[6053,3027,["l",2,6053]],[6054,6053,["l",2,12107]],
[6055,6054,["l",2,12109]],[6057,6056,["l",2,12113]],
[6060,6059,["l",2,12119]],[6067,3034,["l",2,6067]],
[6072,6071,["l",2,12143]],[6073,3037,["l",2,6073]],
[6075,6074,["l",2,12149]],[6079,3040,["l",2,6079]],
[6079,6078,["l",2,12157]],[6081,6080,["l",2,12161]],
[6082,6081,["l",2,12163]],[6084,6083,["l",2,12167]],
[6089,3045,["l",2,6089]],[6091,3046,["l",2,6091]],
[6099,6098,["l",2,12197]],[6101,3051,["l",2,6101]],
[6102,6101,["l",2,12203]],[6106,6105,["l",2,12211]],
[6113,3057,["l",2,6113]],[6114,6113,["l",2,12227]],
[6120,6119,["l",2,12239]],[6121,3061,["l",2,6121]],
[6121,6120,["l",2,12241]],[6126,6125,["l",2,12251]],
[6127,6126,["l",2,12253]],[6131,3066,["l",2,6131]],
[6132,6131,["l",2,12263]],[6133,3067,["l",2,6133]],
[6135,6134,["l",2,12269]],[6139,6138,["l",2,12277]],
[6141,6140,["l",2,12281]],[6143,3072,["l",2,6143]],
[6145,6144,["l",2,12289]],[6151,3076,["l",2,6151]],
[6151,6150,["l",2,12301]],[6162,3121,["s",4,79]],
[6162,3160,["s",4,79]],[6162,6161,["l",2,12323]],
[6163,3082,["l",2,6163]],[6165,6164,["l",2,12329]],
[6172,6171,["l",2,12343]],[6173,3087,["l",2,6173]],
[6174,6173,["l",2,12347]],[6187,6186,["l",2,12373]],
[6189,6188,["l",2,12377]],[6190,6189,["l",2,12379]],
[6196,6195,["l",2,12391]],[6197,3099,["l",2,6197]],
[6199,3100,["l",2,6199]],[6201,6200,["l",2,12401]],
[6203,3102,["l",2,6203]],[6205,6204,["l",2,12409]],
[6207,6206,["l",2,12413]],[6211,3106,["l",2,6211]],
[6211,6210,["l",2,12421]],[6217,3109,["l",2,6217]],
[6217,6216,["l",2,12433]],[6219,6218,["l",2,12437]],
[6221,3111,["l",2,6221]],[6226,6225,["l",2,12451]],
[6229,3115,["l",2,6229]],[6229,6228,["l",2,12457]],
[6237,6236,["l",2,12473]],[6240,6163,["u",3,79]],
[6240,6239,["l",2,12479]],[6244,6243,["l",2,12487]],
[6246,6245,["l",2,12491]],[6247,3124,["l",2,6247]],
[6249,6248,["l",2,12497]],[6252,6251,["l",2,12503]],
[6256,6211,["u",3,137]],[6256,6255,["l",2,12511]],
[6257,3129,["l",2,6257]],[6259,6258,["l",2,12517]],
[6263,3132,["l",2,6263]],[6264,6263,["l",2,12527]],
[6269,3135,["l",2,6269]],[6270,6269,["l",2,12539]],
[6271,3136,["l",2,6271]],[6271,6270,["l",2,12541]],
[6274,6273,["l",2,12547]],[6277,3139,["l",2,6277]],
[6277,6276,["l",2,12553]],[6285,6284,["l",2,12569]],
[6287,3144,["l",2,6287]],[6289,6288,["l",2,12577]],
[6292,6291,["l",2,12583]],[6295,6294,["l",2,12589]],
[6299,3150,["l",2,6299]],[6301,3151,["l",2,6301]],
[6301,6300,["l",2,12601]],[6302,6256,["u",3,137]],
[6306,6305,["l",2,12611]],[6307,6306,["l",2,12613]],
[6310,6309,["l",2,12619]],[6311,3156,["l",2,6311]],
[6315,6097,["l",4,29]],[6317,3159,["l",2,6317]],
[6319,6318,["l",2,12637]],[6320,3121,["s",4,79]],
[6320,3160,["s",4,79]],[6320,6162,["s",4,79]],
[6320,6240,["u",3,79]],[6321,6240,["G2",79]],
[6321,6241,["G2",79]],[6321,6320,["G2",79]],
[6321,6320,["l",2,12641]],[6323,3162,["l",2,6323]],
[6324,6323,["l",2,12647]],[6327,6326,["l",2,12653]],
[6329,3165,["l",2,6329]],[6330,6329,["l",2,12659]],
[6336,6335,["l",2,12671]],[6337,3169,["l",2,6337]],
[6343,3172,["l",2,6343]],[6345,6344,["l",2,12689]],
[6349,6348,["l",2,12697]],[6352,6351,["l",2,12703]],
[6353,3177,["l",2,6353]],[6357,6356,["l",2,12713]],
[6359,3180,["l",2,6359]],[6360,6083,["l",4,23]],
[6360,6084,["o",7,23]],[6360,6084,["s",6,23]],
[6360,6095,["o",7,23]],[6360,6095,["s",6,23]],
[6361,3181,["l",2,6361]],[6361,6360,["l",2,12721]],
[6367,3184,["l",2,6367]],[6370,6369,["l",2,12739]],
[6372,6371,["l",2,12743]],[6373,3187,["l",2,6373]],
[6379,3190,["l",2,6379]],[6379,6378,["l",2,12757]],
[6382,6381,["l",2,12763]],[6385,6384,["l",2,12769]],
[6385,6384,["s",4,113]],[6389,3195,["l",2,6389]],
[6391,6390,["l",2,12781]],[6396,6395,["l",2,12791]],
[6397,3199,["l",2,6397]],[6400,6399,["l",2,12799]],
[6405,6404,["l",2,12809]],[6411,6410,["l",2,12821]],
[6412,6411,["l",2,12823]],[6415,6414,["l",2,12829]],
[6421,3211,["l",2,6421]],[6421,6420,["l",2,12841]],
[6427,3214,["l",2,6427]],[6427,6426,["l",2,12853]],
[6441,6385,["s",4,113]],[6445,6444,["l",2,12889]],
[6447,6446,["l",2,12893]],[6448,5208,["2E6",5]],
[6448,5210,["2E6",5]],[6449,3225,["l",2,6449]],
[6450,6449,["l",2,12899]],[6451,3226,["l",2,6451]],
[6454,6453,["l",2,12907]],[6456,6455,["l",2,12911]],
[6459,6458,["l",2,12917]],[6460,6459,["l",2,12919]],
[6462,6461,["l",2,12923]],[6469,3235,["l",2,6469]],
[6471,6470,["l",2,12941]],[6473,3237,["l",2,6473]],
[6477,6476,["l",2,12953]],[6480,6479,["l",2,12959]],
[6481,3241,["l",2,6481]],[6484,6483,["l",2,12967]],
[6487,6440,["l",3,139]],[6487,6486,["l",2,12973]],
[6490,6489,["l",2,12979]],[6491,3246,["l",2,6491]],
[6492,6491,["l",2,12983]],[6501,6500,["l",2,13001]],
[6502,6501,["l",2,13003]],[6504,6503,["l",2,13007]],
[6505,6504,["l",2,13009]],[6517,6516,["l",2,13033]],
[6519,6518,["l",2,13037]],[6521,3261,["l",2,6521]],
[6522,6521,["l",2,13043]],[6525,6524,["l",2,13049]],
[6529,3265,["l",2,6529]],[6532,6531,["l",2,13063]],
[6547,3274,["l",2,6547]],[6547,6546,["l",2,13093]],
[6550,6549,["l",2,13099]],[6551,3276,["l",2,6551]],
[6552,4372,["s",16,3]],[6552,4380,["s",16,3]],
[6552,6551,["l",2,13103]],[6553,3277,["l",2,6553]],
[6555,6554,["l",2,13109]],[6558,4372,["s",16,3]],
[6558,4380,["s",16,3]],[6558,6552,["s",16,3]],
[6560,4921,["u",9,3]],[6560,6292,["o-",18,3]],
[6560,6396,["o-",18,3]],[6560,6481,["u",3,81]],
[6561,6560,["l",2,13121]],[6563,3282,["l",2,6563]],
[6564,4372,["s",16,3]],[6564,4380,["s",16,3]],
[6564,6552,["s",16,3]],[6564,6558,["s",16,3]],
[6564,6560,["o-",18,3]],[6564,6560,["u",9,3]],
[6564,6563,["l",2,13127]],[6569,3285,["l",2,6569]],
[6570,4372,["s",16,3]],[6570,4380,["s",16,3]],
[6570,6552,["s",16,3]],[6570,6558,["s",16,3]],
[6570,6564,["s",16,3]],[6571,3286,["l",2,6571]],
[6574,6573,["l",2,13147]],[6576,6575,["l",2,13151]],
[6577,3289,["l",2,6577]],[6580,6579,["l",2,13159]],
[6581,3291,["l",2,6581]],[6582,6581,["l",2,13163]],
[6586,6585,["l",2,13171]],[6589,6588,["l",2,13177]],
[6592,6591,["l",2,13183]],[6594,6593,["l",2,13187]],
[6599,3300,["l",2,6599]],[6607,3304,["l",2,6607]],
[6609,6608,["l",2,13217]],[6610,6609,["l",2,13219]],
[6615,6614,["l",2,13229]],[6619,3310,["l",2,6619]],
[6621,6620,["l",2,13241]],[6625,6624,["l",2,13249]],
[6630,6629,["l",2,13259]],[6634,6633,["l",2,13267]],
[6637,3319,["l",2,6637]],[6643,6560,["l",3,81]],
[6643,6560,["G2",81]],[6646,6645,["l",2,13291]],
[6649,6648,["l",2,13297]],[6653,3327,["l",2,6653]],
[6655,6654,["l",2,13309]],[6657,6656,["l",2,13313]],
[6659,3330,["l",2,6659]],[6661,3331,["l",2,6661]],
[6664,6663,["l",2,13327]],[6666,6665,["l",2,13331]],
[6669,6668,["l",2,13337]],[6670,6669,["l",2,13339]],
[6673,3337,["l",2,6673]],[6679,3340,["l",2,6679]],
[6684,6683,["l",2,13367]],[6689,3345,["l",2,6689]],
[6691,3346,["l",2,6691]],[6691,6690,["l",2,13381]],
[6699,6698,["l",2,13397]],[6700,6699,["l",2,13399]],
[6701,3351,["l",2,6701]],[6703,3352,["l",2,6703]],
[6706,6705,["l",2,13411]],[6709,3355,["l",2,6709]],
[6709,6708,["l",2,13417]],[6711,6710,["l",2,13421]],
[6719,3360,["l",2,6719]],[6721,6720,["l",2,13441]],
[6726,6725,["l",2,13451]],[6729,6728,["l",2,13457]],
[6732,6731,["l",2,13463]],[6733,3367,["l",2,6733]],
[6735,6734,["l",2,13469]],[6737,3369,["l",2,6737]],
[6739,6738,["l",2,13477]],[6744,6743,["l",2,13487]],
[6750,6749,["l",2,13499]],[6757,6756,["l",2,13513]],
[6761,3381,["l",2,6761]],[6762,6761,["l",2,13523]],
[6763,3382,["l",2,6763]],[6769,6768,["l",2,13537]],
[6777,6776,["l",2,13553]],[6779,3390,["l",2,6779]],
[6781,3391,["l",2,6781]],[6784,6783,["l",2,13567]],
[6789,6788,["l",2,13577]],[6791,3396,["l",2,6791]],
[6793,3397,["l",2,6793]],[6796,6795,["l",2,13591]],
[6799,6798,["l",2,13597]],[6803,3402,["l",2,6803]],
[6806,3445,["s",4,83]],[6806,3486,["s",4,83]],
[6807,6806,["l",2,13613]],[6810,6809,["l",2,13619]],
[6814,6813,["l",2,13627]],[6817,6816,["l",2,13633]],
[6823,3412,["l",2,6823]],[6825,6824,["l",2,13649]],
[6827,3414,["l",2,6827]],[6829,3415,["l",2,6829]],
[6833,3417,["l",2,6833]],[6835,6834,["l",2,13669]],
[6840,3620,["s",6,19]],[6840,6839,["l",2,13679]],
[6841,3421,["l",2,6841]],[6841,6840,["l",2,13681]],
[6844,6843,["l",2,13687]],[6846,6845,["l",2,13691]],
[6847,6846,["l",2,13693]],[6849,6848,["l",2,13697]],
[6855,6854,["l",2,13709]],[6856,6855,["l",2,13711]],
[6857,3429,["l",2,6857]],[6861,6860,["l",2,13721]],
[6862,6861,["l",2,13723]],[6863,3432,["l",2,6863]],
[6865,6864,["l",2,13729]],[6869,3435,["l",2,6869]],
[6871,3436,["l",2,6871]],[6876,6875,["l",2,13751]],
[6878,3620,["s",6,19]],[6878,6840,["s",6,19]],
[6879,6878,["l",2,13757]],[6880,6879,["l",2,13759]],
[6882,6881,["l",2,13763]],[6883,3442,["l",2,6883]],
[6891,6890,["l",2,13781]],[6895,6894,["l",2,13789]],
[6899,3450,["l",2,6899]],[6900,6899,["l",2,13799]],
[6904,6903,["l",2,13807]],[6907,3454,["l",2,6907]],
[6911,3456,["l",2,6911]],[6915,6914,["l",2,13829]],
[6916,6915,["l",2,13831]],[6917,3459,["l",2,6917]],
[6921,6920,["l",2,13841]],[6930,6929,["l",2,13859]],
[6937,6936,["l",2,13873]],[6939,6938,["l",2,13877]],
[6940,6939,["l",2,13879]],[6942,6941,["l",2,13883]],
[6947,3474,["l",2,6947]],[6949,3475,["l",2,6949]],
[6951,6950,["l",2,13901]],[6952,6951,["l",2,13903]],
[6954,6953,["l",2,13907]],[6957,6956,["l",2,13913]],
[6959,3480,["l",2,6959]],[6961,3481,["l",2,6961]],
[6961,6960,["l",2,13921]],[6966,6965,["l",2,13931]],
[6967,3484,["l",2,6967]],[6967,6966,["l",2,13933]],
[6971,3486,["l",2,6971]],[6972,3445,["s",4,83]],
[6972,3486,["s",4,83]],[6972,6806,["s",4,83]],
[6973,6888,["l",3,83]],[6973,6888,["G2",83]],
[6973,6889,["G2",83]],[6973,6972,["G2",83]],
[6977,3489,["l",2,6977]],[6982,6981,["l",2,13963]],
[6983,3492,["l",2,6983]],[6984,6983,["l",2,13967]],
[6991,3496,["l",2,6991]],[6997,3499,["l",2,6997]],
[6999,6998,["l",2,13997]],[7000,6999,["l",2,13999]],
[7001,3501,["l",2,7001]],[7005,7004,["l",2,14009]],
[7006,7005,["l",2,14011]],[7013,3507,["l",2,7013]],
[7015,7014,["l",2,14029]],[7017,7016,["l",2,14033]],
[7019,3510,["l",2,7019]],[7026,7025,["l",2,14051]],
[7027,3514,["l",2,7027]],[7029,7028,["l",2,14057]],
[7036,7035,["l",2,14071]],[7039,3520,["l",2,7039]],
[7041,7040,["l",2,14081]],[7042,7041,["l",2,14083]],
[7043,3522,["l",2,7043]],[7044,7043,["l",2,14087]],
[7054,7053,["l",2,14107]],[7057,3529,["l",2,7057]],
[7069,3535,["l",2,7069]],[7072,7071,["l",2,14143]],
[7075,7074,["l",2,14149]],[7077,7076,["l",2,14153]],
[7079,3540,["l",2,7079]],[7080,7079,["l",2,14159]],
[7087,7086,["l",2,14173]],[7089,7088,["l",2,14177]],
[7099,7098,["l",2,14197]],[7103,3552,["l",2,7103]],
[7104,7103,["l",2,14207]],[7109,3555,["l",2,7109]],
[7111,7110,["l",2,14221]],[7121,3561,["l",2,7121]],
[7122,7121,["l",2,14243]],[7125,7124,["l",2,14249]],
[7126,7125,["l",2,14251]],[7127,3564,["l",2,7127]],
[7129,3565,["l",2,7129]],[7140,3570,["o+",8,13]],
[7141,7140,["l",2,14281]],[7147,7146,["l",2,14293]],
[7151,3576,["l",2,7151]],[7152,7151,["l",2,14303]],
[7159,3580,["l",2,7159]],[7161,7160,["l",2,14321]],
[7162,7161,["l",2,14323]],[7164,7163,["l",2,14327]],
[7171,7170,["l",2,14341]],[7174,7173,["l",2,14347]],
[7177,3589,["l",2,7177]],[7185,7184,["l",2,14369]],
[7187,3594,["l",2,7187]],[7193,3597,["l",2,7193]],
[7194,7193,["l",2,14387]],[7195,7194,["l",2,14389]],
[7201,7200,["l",2,14401]],[7204,7203,["l",2,14407]],
[7206,7205,["l",2,14411]],[7207,3604,["l",2,7207]],
[7210,7209,["l",2,14419]],[7211,3606,["l",2,7211]],
[7212,7211,["l",2,14423]],[7213,3607,["l",2,7213]],
[7216,7215,["l",2,14431]],[7219,3610,["l",2,7219]],
[7219,7218,["l",2,14437]],[7224,7223,["l",2,14447]],
[7225,7224,["l",2,14449]],[7229,3615,["l",2,7229]],
[7231,7230,["l",2,14461]],[7237,3619,["l",2,7237]],
[7240,7239,["l",2,14479]],[7243,3622,["l",2,7243]],
[7245,7244,["l",2,14489]],[7247,3624,["l",2,7247]],
[7252,7251,["l",2,14503]],[7253,3627,["l",2,7253]],
[7260,6560,["o-",18,3]],[7260,6564,["o-",18,3]],
[7260,7259,["l",2,14519]],[7267,7266,["l",2,14533]],
[7269,7268,["l",2,14537]],[7272,7271,["l",2,14543]],
[7275,7274,["l",2,14549]],[7276,7275,["l",2,14551]],
[7279,7278,["l",2,14557]],[7280,6481,["3D4",9]],
[7280,6562,["F4",9]],[7281,7280,["l",2,14561]],
[7282,7281,["l",2,14563]],[7283,3642,["l",2,7283]],
[7296,7295,["l",2,14591]],[7297,3649,["l",2,7297]],
[7297,7296,["l",2,14593]],[7307,3654,["l",2,7307]],
[7309,3655,["l",2,7309]],[7311,7310,["l",2,14621]],
[7314,7313,["l",2,14627]],[7315,7314,["l",2,14629]],
[7317,7316,["l",2,14633]],[7320,7319,["l",2,14639]],
[7321,3661,["l",2,7321]],[7321,7320,["l",2,14641]],
[7321,7320,["s",4,121]],[7327,7326,["l",2,14653]],
[7329,7328,["l",2,14657]],[7331,3666,["l",2,7331]],
[7333,3667,["l",2,7333]],[7335,7334,["l",2,14669]],
[7342,7341,["l",2,14683]],[7349,3675,["l",2,7349]],
[7350,7349,["l",2,14699]],[7351,3676,["l",2,7351]],
[7357,7356,["l",2,14713]],[7359,7358,["l",2,14717]],
[7362,7361,["l",2,14723]],[7366,7365,["l",2,14731]],
[7369,3685,["l",2,7369]],[7369,7368,["l",2,14737]],
[7371,7370,["l",2,14741]],[7374,7373,["l",2,14747]],
[7377,7376,["l",2,14753]],[7380,7379,["l",2,14759]],
[7381,7280,["l",5,9]],[7384,7383,["l",2,14767]],
[7386,7385,["l",2,14771]],[7390,7389,["l",2,14779]],
[7392,7391,["l",2,14783]],[7393,3697,["l",2,7393]],
[7399,7398,["l",2,14797]],[7400,7351,["u",3,149]],
[7407,7406,["l",2,14813]],[7411,3706,["l",2,7411]],
[7411,7410,["l",2,14821]],[7414,7413,["l",2,14827]],
[7416,7415,["l",2,14831]],[7417,3709,["l",2,7417]],
[7422,7421,["l",2,14843]],[7426,7425,["l",2,14851]],
[7433,3717,["l",2,7433]],[7434,7433,["l",2,14867]],
[7435,7434,["l",2,14869]],[7440,7439,["l",2,14879]],
[7444,7443,["l",2,14887]],[7446,7445,["l",2,14891]],
[7448,7215,["u",4,31]],[7448,7440,["u",4,31]],
[7449,7448,["l",2,14897]],[7450,7400,["u",3,149]],
[7451,3726,["l",2,7451]],[7457,3729,["l",2,7457]],
[7459,3730,["l",2,7459]],[7462,7461,["l",2,14923]],
[7465,7464,["l",2,14929]],[7470,7469,["l",2,14939]],
[7474,7473,["l",2,14947]],[7476,7475,["l",2,14951]],
[7477,3739,["l",2,7477]],[7479,7478,["l",2,14957]],
[7481,3741,["l",2,7481]],[7485,7484,["l",2,14969]],
[7487,3744,["l",2,7487]],[7489,3745,["l",2,7489]],
[7492,7491,["l",2,14983]],[7499,3750,["l",2,7499]],
[7507,3754,["l",2,7507]],[7507,7506,["l",2,15013]],
[7509,7508,["l",2,15017]],[7516,7515,["l",2,15031]],
[7517,3759,["l",2,7517]],[7523,3762,["l",2,7523]],
[7527,7526,["l",2,15053]],[7529,3765,["l",2,7529]],
[7531,7530,["l",2,15061]],[7537,3769,["l",2,7537]],
[7537,7536,["l",2,15073]],[7539,7538,["l",2,15077]],
[7541,3771,["l",2,7541]],[7542,7541,["l",2,15083]],
[7546,7545,["l",2,15091]],[7547,3774,["l",2,7547]],
[7549,3775,["l",2,7549]],[7551,7550,["l",2,15101]],
[7554,7553,["l",2,15107]],[7559,3780,["l",2,7559]],
[7561,3781,["l",2,7561]],[7561,7560,["l",2,15121]],
[7566,7565,["l",2,15131]],[7569,7568,["l",2,15137]],
[7570,7569,["l",2,15139]],[7573,3787,["l",2,7573]],
[7575,7574,["l",2,15149]],[7577,3789,["l",2,7577]],
[7581,7580,["l",2,15161]],[7583,3792,["l",2,7583]],
[7587,7586,["l",2,15173]],[7589,3795,["l",2,7589]],
[7591,3796,["l",2,7591]],[7594,7593,["l",2,15187]],
[7597,7596,["l",2,15193]],[7600,7599,["l",2,15199]],
[7603,3802,["l",2,7603]],[7607,3804,["l",2,7607]],
[7609,7608,["l",2,15217]],[7614,7613,["l",2,15227]],
[7617,7616,["l",2,15233]],[7621,3811,["l",2,7621]],
[7621,7620,["l",2,15241]],[7630,7629,["l",2,15259]],
[7632,7631,["l",2,15263]],[7635,7634,["l",2,15269]],
[7636,7635,["l",2,15271]],[7639,3820,["l",2,7639]],
[7639,7638,["l",2,15277]],[7643,3822,["l",2,7643]],
[7644,7643,["l",2,15287]],[7645,7644,["l",2,15289]],
[7649,3825,["l",2,7649]],[7650,7649,["l",2,15299]],
[7651,7600,["l",3,151]],[7654,7653,["l",2,15307]],
[7657,7656,["l",2,15313]],[7660,7659,["l",2,15319]],
[7665,6477,["o+",24,2]],[7665,6630,["o+",24,2]],
[7665,7620,["o+",24,2]],[7665,7664,["l",2,15329]],
[7666,7665,["l",2,15331]],[7669,3835,["l",2,7669]],
[7673,3837,["l",2,7673]],[7675,7674,["l",2,15349]],
[7680,7679,["l",2,15359]],[7681,3841,["l",2,7681]],
[7681,7680,["l",2,15361]],[7687,3844,["l",2,7687]],
[7687,7686,["l",2,15373]],[7689,7688,["l",2,15377]],
[7691,3846,["l",2,7691]],[7692,7691,["l",2,15383]],
[7696,7695,["l",2,15391]],[7699,3850,["l",2,7699]],
[7701,7700,["l",2,15401]],[7703,3852,["l",2,7703]],
[7707,7706,["l",2,15413]],[7710,7665,["o+",24,2]],
[7714,7713,["l",2,15427]],[7717,3859,["l",2,7717]],
[7720,7719,["l",2,15439]],[7722,7721,["l",2,15443]],
[7723,3862,["l",2,7723]],[7726,7725,["l",2,15451]],
[7727,3864,["l",2,7727]],[7731,7730,["l",2,15461]],
[7734,7733,["l",2,15467]],[7737,7736,["l",2,15473]],
[7741,3871,["l",2,7741]],[7747,7746,["l",2,15493]],
[7749,7748,["l",2,15497]],[7753,3877,["l",2,7753]],
[7756,7755,["l",2,15511]],[7757,3879,["l",2,7757]],
[7759,3880,["l",2,7759]],[7764,7763,["l",2,15527]],
[7771,7770,["l",2,15541]],[7776,7775,["l",2,15551]],
[7780,7779,["l",2,15559]],[7785,7784,["l",2,15569]],
[7789,3895,["l",2,7789]],[7791,7790,["l",2,15581]],
[7792,7791,["l",2,15583]],[7793,3897,["l",2,7793]],
[7801,7800,["l",2,15601]],[7804,7803,["l",2,15607]],
[7810,7809,["l",2,15619]],[7813,7512,["u",4,25]],
[7813,7812,["l",2,15625]],[7813,7812,["s",4,125]],
[7815,7814,["l",2,15629]],[7817,3909,["l",2,7817]],
[7821,7820,["l",2,15641]],[7822,7821,["l",2,15643]],
[7823,3912,["l",2,7823]],[7824,7823,["l",2,15647]],
[7825,7824,["l",2,15649]],[7829,3915,["l",2,7829]],
[7831,7830,["l",2,15661]],[7832,3961,["s",4,89]],
[7832,4005,["s",4,89]],[7834,7833,["l",2,15667]],
[7836,7835,["l",2,15671]],[7840,7839,["l",2,15679]],
[7841,3921,["l",2,7841]],[7842,7841,["l",2,15683]],
[7853,3927,["l",2,7853]],[7864,7863,["l",2,15727]],
[7866,7865,["l",2,15731]],[7867,3934,["l",2,7867]],
[7867,7866,["l",2,15733]],[7869,7868,["l",2,15737]],
[7870,7869,["l",2,15739]],[7873,3937,["l",2,7873]],
[7875,7874,["l",2,15749]],[7877,3939,["l",2,7877]],
[7879,3940,["l",2,7879]],[7881,7880,["l",2,15761]],
[7883,3942,["l",2,7883]],[7884,7883,["l",2,15767]],
[7887,7886,["l",2,15773]],[7894,7893,["l",2,15787]],
[7896,7895,["l",2,15791]],[7899,7898,["l",2,15797]],
[7901,3951,["l",2,7901]],[7902,7901,["l",2,15803]],
[7905,6141,["o-",24,2]],[7905,6150,["o-",24,2]],
[7905,6510,["o-",24,2]],[7905,7140,["o-",24,2]],
[7905,7665,["s",24,2]],[7905,7710,["s",24,2]],
[7905,7904,["l",2,15809]],[7907,3954,["l",2,7907]],
[7909,7908,["l",2,15817]],[7912,7911,["l",2,15823]],
[7919,3960,["l",2,7919]],[7927,3964,["l",2,7927]],
[7930,7929,["l",2,15859]],[7933,3967,["l",2,7933]],
[7937,3969,["l",2,7937]],[7939,7938,["l",2,15877]],
[7941,7940,["l",2,15881]],[7944,7943,["l",2,15887]],
[7945,7944,["l",2,15889]],[7949,3975,["l",2,7949]],
[7951,3976,["l",2,7951]],[7951,7950,["l",2,15901]],
[7954,7953,["l",2,15907]],[7957,7956,["l",2,15913]],
[7960,7959,["l",2,15919]],[7962,7961,["l",2,15923]],
[7963,3982,["l",2,7963]],[7969,7968,["l",2,15937]],
[7980,7321,["o",9,11]],[7980,7321,["o-",8,11]],
[7980,7321,["s",8,11]],[7980,7326,["o",9,11]],
[7980,7326,["s",8,11]],[7980,7979,["l",2,15959]],
[7986,7985,["l",2,15971]],[7987,7986,["l",2,15973]],
[7993,3997,["l",2,7993]],[7996,7995,["l",2,15991]],
[8001,8000,["l",2,16001]],[8004,8003,["l",2,16007]],
[8009,4005,["l",2,8009]],[8010,3961,["s",4,89]],
[8010,4005,["s",4,89]],[8010,7832,["s",4,89]],
[8011,4006,["l",2,8011]],[8011,7920,["l",3,89]],
[8011,7920,["G2",89]],[8011,7921,["G2",89]],
[8011,8010,["G2",89]],[8017,4009,["l",2,8017]],
[8017,8016,["l",2,16033]],[8029,8028,["l",2,16057]],
[8031,8030,["l",2,16061]],[8032,8031,["l",2,16063]],
[8034,8033,["l",2,16067]],[8035,8034,["l",2,16069]],
[8037,8036,["l",2,16073]],[8039,4020,["l",2,8039]],
[8044,8043,["l",2,16087]],[8046,8045,["l",2,16091]],
[8049,8048,["l",2,16097]],[8052,7980,["o",9,11]],
[8052,7980,["o-",8,11]],[8052,7980,["s",8,11]],
[8052,8051,["l",2,16103]],[8053,4027,["l",2,8053]],
[8056,8055,["l",2,16111]],[8059,4030,["l",2,8059]],
[8064,8063,["l",2,16127]],[8065,8064,["l",2,16129]],
[8065,8064,["s",4,127]],[8069,4035,["l",2,8069]],
[8070,8069,["l",2,16139]],[8071,8070,["l",2,16141]],
[8081,4041,["l",2,8081]],[8087,4044,["l",2,8087]],
[8089,4045,["l",2,8089]],[8092,8091,["l",2,16183]],
[8093,4047,["l",2,8093]],[8094,8093,["l",2,16187]],
[8095,8094,["l",2,16189]],[8097,8096,["l",2,16193]],
[8101,4051,["l",2,8101]],[8109,8108,["l",2,16217]],
[8111,4056,["l",2,8111]],[8112,8111,["l",2,16223]],
[8115,8114,["l",2,16229]],[8116,8115,["l",2,16231]],
[8117,4059,["l",2,8117]],[8123,4062,["l",2,8123]],
[8125,8124,["l",2,16249]],[8127,8126,["l",2,16253]],
[8128,8065,["s",4,127]],[8134,8133,["l",2,16267]],
[8137,8136,["l",2,16273]],[8138,7813,["o",7,25]],
[8138,7813,["s",6,25]],[8147,4074,["l",2,8147]],
[8151,8150,["l",2,16301]],[8160,8159,["l",2,16319]],
[8161,4081,["l",2,8161]],[8167,4084,["l",2,8167]],
[8167,8166,["l",2,16333]],[8170,8169,["l",2,16339]],
[8171,4086,["l",2,8171]],[8175,8174,["l",2,16349]],
[8179,4090,["l",2,8179]],[8181,8180,["l",2,16361]],
[8182,8181,["l",2,16363]],[8185,8184,["l",2,16369]],
[8191,4096,["l",2,8191]],[8191,8001,["l",13,2]],
[8191,8190,["l",2,16381]],[8193,6147,["u",14,2]],
[8193,6147,["u",15,2]],[8193,8190,["u",14,2]],
[8193,8190,["u",15,2]],[8193,8191,["l",2,8192]],
[8196,8193,["u",14,2]],[8196,8193,["u",15,2]],
[8206,8205,["l",2,16411]],[8209,4105,["l",2,8209]],
[8209,8208,["l",2,16417]],[8211,8210,["l",2,16421]],
[8214,8213,["l",2,16427]],[8217,8216,["l",2,16433]],
[8219,4110,["l",2,8219]],[8221,4111,["l",2,8221]],
[8224,8223,["l",2,16447]],[8226,8225,["l",2,16451]],
[8227,8226,["l",2,16453]],[8231,4116,["l",2,8231]],
[8233,4117,["l",2,8233]],[8237,4119,["l",2,8237]],
[8239,8238,["l",2,16477]],[8241,8240,["l",2,16481]],
[8243,4122,["l",2,8243]],[8244,8243,["l",2,16487]],
[8247,8246,["l",2,16493]],[8260,8259,["l",2,16519]],
[8263,4132,["l",2,8263]],[8265,8264,["l",2,16529]],
[8269,4135,["l",2,8269]],[8269,8216,["l",3,157]],
[8273,4137,["l",2,8273]],[8274,8273,["l",2,16547]],
[8277,8276,["l",2,16553]],[8281,8280,["l",2,16561]],
[8284,8283,["l",2,16567]],[8287,4144,["l",2,8287]],
[8287,8286,["l",2,16573]],[8291,4146,["l",2,8291]],
[8293,4147,["l",2,8293]],[8297,4149,["l",2,8297]],
[8302,8301,["l",2,16603]],[8304,8303,["l",2,16607]],
[8310,8309,["l",2,16619]],[8311,4156,["l",2,8311]],
[8316,8315,["l",2,16631]],[8317,4159,["l",2,8317]],
[8317,8316,["l",2,16633]],[8321,8191,["2B2",8192]],
[8325,8324,["l",2,16649]],[8326,8325,["l",2,16651]],
[8329,4165,["l",2,8329]],[8329,8328,["l",2,16657]],
[8331,8330,["l",2,16661]],[8337,8336,["l",2,16673]],
[8346,8345,["l",2,16691]],[8347,8346,["l",2,16693]],
[8350,8349,["l",2,16699]],[8352,8351,["l",2,16703]],
[8353,4177,["l",2,8353]],[8363,4182,["l",2,8363]],
[8365,8364,["l",2,16729]],[8369,4185,["l",2,8369]],
[8371,8370,["l",2,16741]],[8374,8373,["l",2,16747]],
[8377,4189,["l",2,8377]],[8380,8379,["l",2,16759]],
[8382,8381,["l",2,16763]],[8387,4194,["l",2,8387]],
[8389,4195,["l",2,8389]],[8394,8393,["l",2,16787]],
[8404,7353,["u",6,7]],[8404,8400,["u",6,7]],
[8404,8403,["l",2,16807]],[8406,8405,["l",2,16811]],
[8412,8411,["l",2,16823]],[8415,8414,["l",2,16829]],
[8416,8415,["l",2,16831]],[8419,4210,["l",2,8419]],
[8422,8421,["l",2,16843]],[8423,4212,["l",2,8423]],
[8429,4215,["l",2,8429]],[8431,4216,["l",2,8431]],
[8436,8435,["l",2,16871]],[8440,8439,["l",2,16879]],
[8442,8441,["l",2,16883]],[8443,4222,["l",2,8443]],
[8445,8444,["l",2,16889]],[8447,4224,["l",2,8447]],
[8451,8450,["l",2,16901]],[8452,8451,["l",2,16903]],
[8461,4231,["l",2,8461]],[8461,8460,["l",2,16921]],
[8464,8463,["l",2,16927]],[8466,8465,["l",2,16931]],
[8467,4234,["l",2,8467]],[8469,8468,["l",2,16937]],
[8472,8471,["l",2,16943]],[8482,8481,["l",2,16963]],
[8490,8489,["l",2,16979]],[8491,8490,["l",2,16981]],
[8494,8493,["l",2,16987]],[8497,8496,["l",2,16993]],
[8501,4251,["l",2,8501]],[8506,8505,["l",2,17011]],
[8511,8510,["l",2,17021]],[8513,4257,["l",2,8513]],
[8514,8513,["l",2,17027]],[8515,8514,["l",2,17029]],
[8517,8516,["l",2,17033]],[8521,4261,["l",2,8521]],
[8521,8520,["l",2,17041]],[8524,8523,["l",2,17047]],
[8527,4264,["l",2,8527]],[8527,8526,["l",2,17053]],
[8537,4269,["l",2,8537]],[8539,4270,["l",2,8539]],
[8539,8538,["l",2,17077]],[8543,4272,["l",2,8543]],
[8547,8546,["l",2,17093]],[8550,8549,["l",2,17099]],
[8554,8553,["l",2,17107]],[8559,8558,["l",2,17117]],
[8562,8561,["l",2,17123]],[8563,4282,["l",2,8563]],
[8569,8568,["l",2,17137]],[8573,4287,["l",2,8573]],
[8580,8579,["l",2,17159]],[8581,4291,["l",2,8581]],
[8581,8580,["l",2,17161]],[8581,8580,["s",4,131]],
[8584,8583,["l",2,17167]],[8592,8591,["l",2,17183]],
[8595,8594,["l",2,17189]],[8596,8595,["l",2,17191]],
[8597,4299,["l",2,8597]],[8599,4300,["l",2,8599]],
[8602,8601,["l",2,17203]],[8604,8603,["l",2,17207]],
[8605,8604,["l",2,17209]],[8609,4305,["l",2,8609]],
[8616,8615,["l",2,17231]],[8620,8619,["l",2,17239]],
[8623,4312,["l",2,8623]],[8627,4314,["l",2,8627]],
[8629,4315,["l",2,8629]],[8629,8628,["l",2,17257]],
[8641,4321,["l",2,8641]],[8646,8581,["s",4,131]],
[8646,8645,["l",2,17291]],[8647,4324,["l",2,8647]],
[8647,8646,["l",2,17293]],[8650,8649,["l",2,17299]],
[8659,8658,["l",2,17317]],[8661,8660,["l",2,17321]],
[8663,4332,["l",2,8663]],[8664,8663,["l",2,17327]],
[8667,8666,["l",2,17333]],[8669,4335,["l",2,8669]],
[8671,8670,["l",2,17341]],[8676,8675,["l",2,17351]],
[8677,4339,["l",2,8677]],[8680,8679,["l",2,17359]],
[8681,4341,["l",2,8681]],[8689,4345,["l",2,8689]],
[8689,8688,["l",2,17377]],[8692,8691,["l",2,17383]],
[8693,4347,["l",2,8693]],[8694,8693,["l",2,17387]],
[8695,8694,["l",2,17389]],[8697,8696,["l",2,17393]],
[8699,4350,["l",2,8699]],[8701,8700,["l",2,17401]],
[8707,4354,["l",2,8707]],[8709,8708,["l",2,17417]],
[8710,8709,["l",2,17419]],[8713,4357,["l",2,8713]],
[8716,8715,["l",2,17431]],[8719,4360,["l",2,8719]],
[8722,8721,["l",2,17443]],[8725,8724,["l",2,17449]],
[8731,4366,["l",2,8731]],[8734,8733,["l",2,17467]],
[8736,8735,["l",2,17471]],[8737,4369,["l",2,8737]],
[8739,8738,["l",2,17477]],[8741,4371,["l",2,8741]],
[8742,8741,["l",2,17483]],[8745,8744,["l",2,17489]],
[8746,8745,["l",2,17491]],[8747,4374,["l",2,8747]],
[8749,8748,["l",2,17497]],[8753,4377,["l",2,8753]],
[8755,8754,["l",2,17509]],[8760,8759,["l",2,17519]],
[8761,4381,["l",2,8761]],[8770,8769,["l",2,17539]],
[8776,8775,["l",2,17551]],[8779,4390,["l",2,8779]],
[8783,4392,["l",2,8783]],[8785,8784,["l",2,17569]],
[8787,8786,["l",2,17573]],[8790,8789,["l",2,17579]],
[8791,8790,["l",2,17581]],[8799,8798,["l",2,17597]],
[8800,8799,["l",2,17599]],[8803,4402,["l",2,8803]],
[8805,8804,["l",2,17609]],[8807,4404,["l",2,8807]],
[8812,8811,["l",2,17623]],[8814,8813,["l",2,17627]],
[8819,4410,["l",2,8819]],[8821,4411,["l",2,8821]],
[8829,8828,["l",2,17657]],[8830,8829,["l",2,17659]],
[8831,4416,["l",2,8831]],[8835,8834,["l",2,17669]],
[8837,4419,["l",2,8837]],[8839,4420,["l",2,8839]],
[8841,8840,["l",2,17681]],[8842,8841,["l",2,17683]],
[8849,4425,["l",2,8849]],[8854,8853,["l",2,17707]],
[8857,8856,["l",2,17713]],[8861,4431,["l",2,8861]],
[8863,4432,["l",2,8863]],[8865,8864,["l",2,17729]],
[8867,4434,["l",2,8867]],[8869,8868,["l",2,17737]],
[8874,8873,["l",2,17747]],[8875,8874,["l",2,17749]],
[8881,8880,["l",2,17761]],[8887,4444,["l",2,8887]],
[8892,8891,["l",2,17783]],[8893,4447,["l",2,8893]],
[8895,8894,["l",2,17789]],[8896,8895,["l",2,17791]],
[8904,8903,["l",2,17807]],[8911,8856,["l",3,163]],
[8914,8913,["l",2,17827]],[8919,8918,["l",2,17837]],
[8920,8919,["l",2,17839]],[8923,4462,["l",2,8923]],
[8926,8925,["l",2,17851]],[8929,4465,["l",2,8929]],
[8932,8931,["l",2,17863]],[8933,4467,["l",2,8933]],
[8941,4471,["l",2,8941]],[8941,8940,["l",2,17881]],
[8946,8945,["l",2,17891]],[8951,4476,["l",2,8951]],
[8952,8951,["l",2,17903]],[8955,8954,["l",2,17909]],
[8956,8955,["l",2,17911]],[8961,8960,["l",2,17921]],
[8962,8961,["l",2,17923]],[8963,4482,["l",2,8963]],
[8965,8964,["l",2,17929]],[8969,4485,["l",2,8969]],
[8970,8969,["l",2,17939]],[8971,4486,["l",2,8971]],
[8979,8978,["l",2,17957]],[8980,8979,["l",2,17959]],
[8986,8985,["l",2,17971]],[8989,8988,["l",2,17977]],
[8991,8990,["l",2,17981]],[8994,8993,["l",2,17987]],
[8995,8994,["l",2,17989]],[8999,4500,["l",2,8999]],
[9001,4501,["l",2,9001]],[9007,4504,["l",2,9007]],
[9007,9006,["l",2,18013]],[9011,4506,["l",2,9011]],
[9013,4507,["l",2,9013]],[9021,9020,["l",2,18041]],
[9022,9021,["l",2,18043]],[9024,9023,["l",2,18047]],
[9025,9024,["l",2,18049]],[9029,4515,["l",2,9029]],
[9030,9029,["l",2,18059]],[9031,9030,["l",2,18061]],
[9039,9038,["l",2,18077]],[9041,4521,["l",2,9041]],
[9043,4522,["l",2,9043]],[9045,9044,["l",2,18089]],
[9049,4525,["l",2,9049]],[9049,9048,["l",2,18097]],
[9059,4530,["l",2,9059]],[9060,9059,["l",2,18119]],
[9061,9060,["l",2,18121]],[9064,9063,["l",2,18127]],
[9066,9065,["l",2,18131]],[9067,4534,["l",2,9067]],
[9067,9066,["l",2,18133]],[9072,9071,["l",2,18143]],
[9075,9074,["l",2,18149]],[9085,9084,["l",2,18169]],
[9091,4546,["l",2,9091]],[9091,9090,["l",2,18181]],
[9096,9095,["l",2,18191]],[9100,9099,["l",2,18199]],
[9103,4552,["l",2,9103]],[9106,9105,["l",2,18211]],
[9109,4555,["l",2,9109]],[9109,9108,["l",2,18217]],
[9112,9111,["l",2,18223]],[9115,9114,["l",2,18229]],
[9117,9116,["l",2,18233]],[9126,9125,["l",2,18251]],
[9127,4564,["l",2,9127]],[9127,9126,["l",2,18253]],
[9129,9128,["l",2,18257]],[9133,4567,["l",2,9133]],
[9135,9134,["l",2,18269]],[9137,4569,["l",2,9137]],
[9144,9143,["l",2,18287]],[9145,9144,["l",2,18289]],
[9151,4576,["l",2,9151]],[9151,9150,["l",2,18301]],
[9154,9153,["l",2,18307]],[9156,9155,["l",2,18311]],
[9157,4579,["l",2,9157]],[9157,9156,["l",2,18313]],
[9161,4581,["l",2,9161]],[9165,9164,["l",2,18329]],
[9171,9170,["l",2,18341]],[9173,4587,["l",2,9173]],
[9177,9176,["l",2,18353]],[9181,4591,["l",2,9181]],
[9184,9183,["l",2,18367]],[9186,9185,["l",2,18371]],
[9187,4594,["l",2,9187]],[9190,9189,["l",2,18379]],
[9199,4600,["l",2,9199]],[9199,9198,["l",2,18397]],
[9201,9200,["l",2,18401]],[9203,4602,["l",2,9203]],
[9207,9206,["l",2,18413]],[9209,4605,["l",2,9209]],
[9214,9213,["l",2,18427]],[9217,9216,["l",2,18433]],
[9220,9219,["l",2,18439]],[9221,4611,["l",2,9221]],
[9222,9221,["l",2,18443]],[9226,9225,["l",2,18451]],
[9227,4614,["l",2,9227]],[9229,9228,["l",2,18457]],
[9231,9230,["l",2,18461]],[9239,4620,["l",2,9239]],
[9241,4621,["l",2,9241]],[9241,9240,["l",2,18481]],
[9247,9246,["l",2,18493]],[9252,9251,["l",2,18503]],
[9257,4629,["l",2,9257]],[9259,9258,["l",2,18517]],
[9261,9260,["l",2,18521]],[9262,9261,["l",2,18523]],
[9270,9269,["l",2,18539]],[9271,9270,["l",2,18541]],
[9277,4639,["l",2,9277]],[9277,9276,["l",2,18553]],
[9281,4641,["l",2,9281]],[9283,4642,["l",2,9283]],
[9292,9291,["l",2,18583]],[9293,4647,["l",2,9293]],
[9294,9293,["l",2,18587]],[9296,9241,["u",3,167]],
[9297,9296,["l",2,18593]],[9309,9308,["l",2,18617]],
[9311,4656,["l",2,9311]],[9312,4705,["s",4,97]],
[9312,4753,["s",4,97]],[9319,4660,["l",2,9319]],
[9319,9318,["l",2,18637]],[9323,4662,["l",2,9323]],
[9331,9330,["l",2,18661]],[9336,9335,["l",2,18671]],
[9337,4669,["l",2,9337]],[9340,9339,["l",2,18679]],
[9341,4671,["l",2,9341]],[9343,4672,["l",2,9343]],
[9346,9345,["l",2,18691]],[9349,4675,["l",2,9349]],
[9351,9350,["l",2,18701]],[9352,9296,["u",3,167]],
[9357,9356,["l",2,18713]],[9360,9359,["l",2,18719]],
[9366,9365,["l",2,18731]],[9371,4686,["l",2,9371]],
[9372,7813,["o-",12,5]],[9372,8138,["o",13,5]],
[9372,8138,["s",12,5]],[9372,8190,["o",13,5]],
[9372,8190,["s",12,5]],[9372,9371,["l",2,18743]],
[9375,9374,["l",2,18749]],[9377,4689,["l",2,9377]],
[9379,9378,["l",2,18757]],[9385,9384,["l",2,18769]],
[9385,9384,["s",4,137]],[9387,9386,["l",2,18773]],
[9390,9372,["o",13,5]],[9390,9372,["o-",12,5]],
[9390,9372,["s",12,5]],[9391,4696,["l",2,9391]],
[9394,9393,["l",2,18787]],[9397,4699,["l",2,9397]],
[9397,9396,["l",2,18793]],[9399,9398,["l",2,18797]],
[9402,9401,["l",2,18803]],[9403,4702,["l",2,9403]],
[9408,9313,["u",3,97]],[9413,4707,["l",2,9413]],
[9419,4710,["l",2,9419]],[9420,9419,["l",2,18839]],
[9421,4711,["l",2,9421]],[9430,9429,["l",2,18859]],
[9431,4716,["l",2,9431]],[9433,4717,["l",2,9433]],
[9435,9434,["l",2,18869]],[9437,4719,["l",2,9437]],
[9439,4720,["l",2,9439]],[9450,9449,["l",2,18899]],
[9453,9385,["s",4,137]],[9456,9455,["l",2,18911]],
[9457,9456,["l",2,18913]],[9459,9458,["l",2,18917]],
[9460,9459,["l",2,18919]],[9461,4731,["l",2,9461]],
[9463,4732,["l",2,9463]],[9467,4734,["l",2,9467]],
[9473,4737,["l",2,9473]],[9474,9473,["l",2,18947]],
[9479,4740,["l",2,9479]],[9480,9479,["l",2,18959]],
[9487,9486,["l",2,18973]],[9490,9489,["l",2,18979]],
[9491,4746,["l",2,9491]],[9497,4749,["l",2,9497]],
[9501,9500,["l",2,19001]],[9505,9504,["l",2,19009]],
[9506,4705,["s",4,97]],[9506,4753,["s",4,97]],
[9506,9312,["s",4,97]],[9506,9408,["u",3,97]],
[9507,9408,["G2",97]],[9507,9409,["G2",97]],
[9507,9506,["G2",97]],[9507,9506,["l",2,19013]],
[9511,4756,["l",2,9511]],[9516,9515,["l",2,19031]],
[9519,9518,["l",2,19037]],[9521,4761,["l",2,9521]],
[9526,9525,["l",2,19051]],[9533,4767,["l",2,9533]],
[9535,9534,["l",2,19069]],[9537,9536,["l",2,19073]],
[9539,4770,["l",2,9539]],[9540,9539,["l",2,19079]],
[9541,9540,["l",2,19081]],[9544,9543,["l",2,19087]],
[9547,4774,["l",2,9547]],[9551,4776,["l",2,9551]],
[9561,9560,["l",2,19121]],[9570,9569,["l",2,19139]],
[9571,9570,["l",2,19141]],[9577,9520,["l",3,169]],
[9579,9578,["l",2,19157]],[9582,9581,["l",2,19163]],
[9587,4794,["l",2,9587]],[9591,9590,["l",2,19181]],
[9592,9591,["l",2,19183]],[9601,4801,["l",2,9601]],
[9604,9603,["l",2,19207]],[9606,9605,["l",2,19211]],
[9607,9606,["l",2,19213]],[9608,8600,["o",11,7]],
[9608,8600,["o+",10,7]],[9608,8600,["s",10,7]],
[9608,9576,["o",11,7]],[9608,9576,["o+",10,7]],
[9608,9576,["s",10,7]],[9610,9609,["l",2,19219]],
[9613,4807,["l",2,9613]],[9616,9615,["l",2,19231]],
[9619,4810,["l",2,9619]],[9619,9618,["l",2,19237]],
[9623,4812,["l",2,9623]],[9625,9624,["l",2,19249]],
[9629,4815,["l",2,9629]],[9630,9629,["l",2,19259]],
[9631,4816,["l",2,9631]],[9634,9633,["l",2,19267]],
[9637,9636,["l",2,19273]],[9643,4822,["l",2,9643]],
[9645,9644,["l",2,19289]],[9649,4825,["l",2,9649]],
[9651,9650,["l",2,19301]],[9655,9654,["l",2,19309]],
[9660,9659,["l",2,19319]],[9661,4831,["l",2,9661]],
[9661,9660,["l",2,19321]],[9661,9660,["s",4,139]],
[9667,9666,["l",2,19333]],[9677,4839,["l",2,9677]],
[9679,4840,["l",2,9679]],[9687,9686,["l",2,19373]],
[9689,4845,["l",2,9689]],[9690,9689,["l",2,19379]],
[9691,9690,["l",2,19381]],[9694,9693,["l",2,19387]],
[9696,9695,["l",2,19391]],[9697,4849,["l",2,9697]],
[9702,9701,["l",2,19403]],[9709,9708,["l",2,19417]],
[9711,9710,["l",2,19421]],[9712,9711,["l",2,19423]],
[9714,9713,["l",2,19427]],[9715,9714,["l",2,19429]],
[9717,9716,["l",2,19433]],[9719,4860,["l",2,9719]],
[9721,4861,["l",2,9721]],[9721,9720,["l",2,19441]],
[9724,9723,["l",2,19447]],[9729,9728,["l",2,19457]],
[9730,9661,["s",4,139]],[9732,9731,["l",2,19463]],
[9733,4867,["l",2,9733]],[9735,9734,["l",2,19469]],
[9736,9735,["l",2,19471]],[9739,4870,["l",2,9739]],
[9739,9738,["l",2,19477]],[9742,9741,["l",2,19483]],
[9743,4872,["l",2,9743]],[9745,9744,["l",2,19489]],
[9749,4875,["l",2,9749]],[9751,9750,["l",2,19501]],
[9754,9753,["l",2,19507]],[9766,9765,["l",2,19531]],
[9767,4884,["l",2,9767]],[9769,4885,["l",2,9769]],
[9771,9770,["l",2,19541]],[9772,9771,["l",2,19543]],
[9777,9776,["l",2,19553]],[9780,9779,["l",2,19559]],
[9781,4891,["l",2,9781]],[9786,9785,["l",2,19571]],
[9787,4894,["l",2,9787]],[9789,9788,["l",2,19577]],
[9791,4896,["l",2,9791]],[9792,9791,["l",2,19583]],
[9799,9798,["l",2,19597]],[9802,9801,["l",2,19603]],
[9803,4902,["l",2,9803]],[9805,9804,["l",2,19609]],
[9811,4906,["l",2,9811]],[9817,4909,["l",2,9817]],
[9829,4915,["l",2,9829]],[9831,9830,["l",2,19661]],
[9833,4917,["l",2,9833]],[9839,4920,["l",2,9839]],
[9841,9680,["l",9,3]],[9841,9840,["l",2,19681]],
[9842,7658,["u",10,3]],[9842,9840,["u",10,3]],
[9842,9841,["l",2,19683]],[9844,9843,["l",2,19687]],
[9849,9848,["l",2,19697]],[9850,9849,["l",2,19699]],
[9851,4926,["l",2,9851]],[9855,9854,["l",2,19709]],
[9857,4929,["l",2,9857]],[9859,4930,["l",2,9859]],
[9859,9858,["l",2,19717]],[9864,9863,["l",2,19727]],
[9870,9869,["l",2,19739]],[9871,4936,["l",2,9871]],
[9876,9875,["l",2,19751]],[9877,9876,["l",2,19753]],
[9880,9879,["l",2,19759]],[9882,9881,["l",2,19763]],
[9883,4942,["l",2,9883]],[9887,4944,["l",2,9887]],
[9889,9888,["l",2,19777]],[9897,9896,["l",2,19793]],
[9901,4951,["l",2,9901]],[9901,9900,["l",2,19801]],
[9907,4954,["l",2,9907]],[9907,9906,["l",2,19813]],
[9910,9909,["l",2,19819]],[9921,9920,["l",2,19841]],
[9922,9921,["l",2,19843]],[9923,4962,["l",2,9923]],
[9927,9926,["l",2,19853]],[9929,4965,["l",2,9929]],
[9931,4966,["l",2,9931]],[9931,9930,["l",2,19861]],
[9934,9933,["l",2,19867]],[9941,4971,["l",2,9941]],
[9945,9944,["l",2,19889]],[9946,9945,["l",2,19891]],
[9949,4975,["l",2,9949]],[9957,9956,["l",2,19913]],
[9960,9959,["l",2,19919]],[9964,9963,["l",2,19927]],
[9967,4984,["l",2,9967]],[9969,9968,["l",2,19937]],
[9973,4987,["l",2,9973]],[9975,9974,["l",2,19949]],
[9976,9919,["u",3,173]],[9981,9980,["l",2,19961]],
[9982,9981,["l",2,19963]],[9987,9986,["l",2,19973]],
[9990,9989,["l",2,19979]],[9996,9995,["l",2,19991]],
[9997,9996,["l",2,19993]],[9999,9998,["l",2,19997]],
[10006,10005,["l",2,20011]],[10007,5004,["l",2,10007]],
[10009,5005,["l",2,10009]],[10011,10010,["l",2,20021]],
[10012,10011,["l",2,20023]],[10015,10014,["l",2,20029]],
[10024,10023,["l",2,20047]],[10026,10025,["l",2,20051]],
[10032,10031,["l",2,20063]],[10034,9976,["u",3,173]],
[10036,10035,["l",2,20071]],[10037,5019,["l",2,10037]],
[10039,5020,["l",2,10039]],[10045,10044,["l",2,20089]],
[10051,10050,["l",2,20101]],[10054,10053,["l",2,20107]],
[10057,10056,["l",2,20113]],[10059,10058,["l",2,20117]],
[10061,5031,["l",2,10061]],[10062,10061,["l",2,20123]],
[10065,10064,["l",2,20129]],[10067,5034,["l",2,10067]],
[10069,5035,["l",2,10069]],[10072,10071,["l",2,20143]],
[10074,10073,["l",2,20147]],[10075,10074,["l",2,20149]],
[10079,5040,["l",2,10079]],[10081,10080,["l",2,20161]],
[10087,10086,["l",2,20173]],[10089,10088,["l",2,20177]],
[10091,5046,["l",2,10091]],[10092,10091,["l",2,20183]],
[10093,5047,["l",2,10093]],[10099,5050,["l",2,10099]],
[10100,5101,["s",4,101]],[10100,5151,["s",4,101]],
[10101,10100,["l",2,20201]],[10103,5052,["l",2,10103]],
[10110,10109,["l",2,20219]],[10111,5056,["l",2,10111]],
[10116,10115,["l",2,20231]],[10117,10116,["l",2,20233]],
[10125,10124,["l",2,20249]],[10131,10130,["l",2,20261]],
[10133,5067,["l",2,10133]],[10135,10134,["l",2,20269]],
[10139,5070,["l",2,10139]],[10141,5071,["l",2,10141]],
[10144,10143,["l",2,20287]],[10149,10148,["l",2,20297]],
[10151,5076,["l",2,10151]],[10159,5080,["l",2,10159]],
[10162,10161,["l",2,20323]],[10163,5082,["l",2,10163]],
[10164,10163,["l",2,20327]],[10167,10166,["l",2,20333]],
[10169,5085,["l",2,10169]],[10171,10170,["l",2,20341]],
[10174,10173,["l",2,20347]],[10177,5089,["l",2,10177]],
[10177,10176,["l",2,20353]],[10179,10178,["l",2,20357]],
[10180,10179,["l",2,20359]],[10181,5091,["l",2,10181]],
[10185,10184,["l",2,20369]],[10193,5097,["l",2,10193]],
[10195,10194,["l",2,20389]],[10197,10196,["l",2,20393]],
[10200,10199,["l",2,20399]],[10204,10203,["l",2,20407]],
[10206,10205,["l",2,20411]],[10211,5106,["l",2,10211]],
[10216,10215,["l",2,20431]],[10220,9841,["l",4,27]],
[10220,9842,["o",7,27]],[10220,9842,["s",6,27]],
[10221,10220,["l",2,20441]],[10222,10221,["l",2,20443]],
[10223,5112,["l",2,10223]],[10239,10238,["l",2,20477]],
[10240,10239,["l",2,20479]],[10242,10241,["l",2,20483]],
[10243,5122,["l",2,10243]],[10247,5124,["l",2,10247]],
[10253,5127,["l",2,10253]],[10254,10253,["l",2,20507]],
[10255,10254,["l",2,20509]],[10259,5130,["l",2,10259]],
[10261,10260,["l",2,20521]],[10267,5134,["l",2,10267]],
[10267,10266,["l",2,20533]],[10271,5136,["l",2,10271]],
[10272,10271,["l",2,20543]],[10273,5137,["l",2,10273]],
[10275,10274,["l",2,20549]],[10276,10275,["l",2,20551]],
[10282,10281,["l",2,20563]],[10289,5145,["l",2,10289]],
[10297,10296,["l",2,20593]],[10300,10299,["l",2,20599]],
[10301,5151,["l",2,10301]],[10302,5101,["s",4,101]],
[10302,5151,["s",4,101]],[10302,10100,["s",4,101]],
[10303,5152,["l",2,10303]],[10303,10200,["l",3,101]],
[10303,10200,["G2",101]],[10303,10201,["G2",101]],
[10303,10302,["G2",101]],[10306,10305,["l",2,20611]],
[10313,5157,["l",2,10313]],[10314,10313,["l",2,20627]],
[10320,10319,["l",2,20639]],[10321,5161,["l",2,10321]],
[10321,10320,["l",2,20641]],[10331,5166,["l",2,10331]],
[10332,10331,["l",2,20663]],[10333,5167,["l",2,10333]],
[10337,5169,["l",2,10337]],[10341,10340,["l",2,20681]],
[10343,5172,["l",2,10343]],[10347,10346,["l",2,20693]],
[10354,10353,["l",2,20707]],[10357,5179,["l",2,10357]],
[10359,10358,["l",2,20717]],[10360,10359,["l",2,20719]],
[10366,10365,["l",2,20731]],[10369,5185,["l",2,10369]],
[10372,10371,["l",2,20743]],[10374,10373,["l",2,20747]],
[10375,10374,["l",2,20749]],[10377,10376,["l",2,20753]],
[10380,10379,["l",2,20759]],[10386,10385,["l",2,20771]],
[10387,10386,["l",2,20773]],[10391,5196,["l",2,10391]],
[10395,10394,["l",2,20789]],[10399,5200,["l",2,10399]],
[10404,10403,["l",2,20807]],[10405,10404,["l",2,20809]],
[10425,10424,["l",2,20849]],[10427,5214,["l",2,10427]],
[10429,5215,["l",2,10429]],[10429,10428,["l",2,20857]],
[10433,5217,["l",2,10433]],[10437,10436,["l",2,20873]],
[10440,10439,["l",2,20879]],[10444,10443,["l",2,20887]],
[10449,10448,["l",2,20897]],[10450,10449,["l",2,20899]],
[10452,10451,["l",2,20903]],[10453,5227,["l",2,10453]],
[10457,5229,["l",2,10457]],[10459,5230,["l",2,10459]],
[10461,10460,["l",2,20921]],[10463,5232,["l",2,10463]],
[10465,10464,["l",2,20929]],[10470,10469,["l",2,20939]],
[10474,10473,["l",2,20947]],[10477,5239,["l",2,10477]],
[10480,10479,["l",2,20959]],[10482,10481,["l",2,20963]],
[10487,5244,["l",2,10487]],[10491,10490,["l",2,20981]],
[10492,10491,["l",2,20983]],[10499,5250,["l",2,10499]],
[10501,5251,["l",2,10501]],[10501,10500,["l",2,21001]],
[10506,5305,["s",4,103]],[10506,5356,["s",4,103]],
[10506,10505,["l",2,21011]],[10507,10506,["l",2,21013]],
[10509,10508,["l",2,21017]],[10510,10509,["l",2,21019]],
[10512,10511,["l",2,21023]],[10513,5257,["l",2,10513]],
[10516,10515,["l",2,21031]],[10529,5265,["l",2,10529]],
[10530,10529,["l",2,21059]],[10531,5266,["l",2,10531]],
[10531,10530,["l",2,21061]],[10534,10533,["l",2,21067]],
[10545,10544,["l",2,21089]],[10551,10550,["l",2,21101]],
[10554,10553,["l",2,21107]],[10559,5280,["l",2,10559]],
[10561,10560,["l",2,21121]],[10567,5284,["l",2,10567]],
[10570,10569,["l",2,21139]],[10572,10571,["l",2,21143]],
[10575,10574,["l",2,21149]],[10579,10578,["l",2,21157]],
[10582,10581,["l",2,21163]],[10585,10584,["l",2,21169]],
[10589,5295,["l",2,10589]],[10590,10589,["l",2,21179]],
[10594,10593,["l",2,21187]],[10596,10595,["l",2,21191]],
[10597,5299,["l",2,10597]],[10597,10596,["l",2,21193]],
[10601,5301,["l",2,10601]],[10606,10605,["l",2,21211]],
[10607,5304,["l",2,10607]],[10608,10507,["u",3,103]],
[10611,10610,["l",2,21221]],[10613,5307,["l",2,10613]],
[10614,10613,["l",2,21227]],[10624,10623,["l",2,21247]],
[10627,5314,["l",2,10627]],[10631,5316,["l",2,10631]],
[10635,10634,["l",2,21269]],[10639,5320,["l",2,10639]],
[10639,10638,["l",2,21277]],[10642,10641,["l",2,21283]],
[10651,5326,["l",2,10651]],[10657,5329,["l",2,10657]],
[10657,10656,["l",2,21313]],[10659,10658,["l",2,21317]],
[10660,10659,["l",2,21319]],[10662,10661,["l",2,21323]],
[10663,5332,["l",2,10663]],[10667,5334,["l",2,10667]],
[10671,10670,["l",2,21341]],[10674,10673,["l",2,21347]],
[10680,10621,["u",3,179]],[10687,5344,["l",2,10687]],
[10689,10688,["l",2,21377]],[10690,10689,["l",2,21379]],
[10691,5346,["l",2,10691]],[10692,10691,["l",2,21383]],
[10696,10695,["l",2,21391]],[10699,10698,["l",2,21397]],
[10701,10700,["l",2,21401]],[10704,10703,["l",2,21407]],
[10709,5355,["l",2,10709]],[10710,10709,["l",2,21419]],
[10711,5356,["l",2,10711]],[10712,5305,["s",4,103]],
[10712,5356,["s",4,103]],[10712,10506,["s",4,103]],
[10712,10608,["u",3,103]],[10713,10608,["G2",103]],
[10713,10609,["G2",103]],[10713,10712,["G2",103]],
[10717,10716,["l",2,21433]],[10723,5362,["l",2,10723]],
[10729,5365,["l",2,10729]],[10733,5367,["l",2,10733]],
[10734,10733,["l",2,21467]],[10739,5370,["l",2,10739]],
[10740,10680,["u",3,179]],[10741,10740,["l",2,21481]],
[10744,10743,["l",2,21487]],[10746,10745,["l",2,21491]],
[10747,10746,["l",2,21493]],[10750,10749,["l",2,21499]],
[10752,10751,["l",2,21503]],[10753,5377,["l",2,10753]],
[10759,10758,["l",2,21517]],[10761,10760,["l",2,21521]],
[10762,10761,["l",2,21523]],[10765,10764,["l",2,21529]],
[10771,5386,["l",2,10771]],[10779,10778,["l",2,21557]],
[10780,10779,["l",2,21559]],[10781,5391,["l",2,10781]],
[10782,10781,["l",2,21563]],[10785,10784,["l",2,21569]],
[10789,5395,["l",2,10789]],[10789,10788,["l",2,21577]],
[10794,10793,["l",2,21587]],[10795,10794,["l",2,21589]],
[10799,5400,["l",2,10799]],[10800,10799,["l",2,21599]],
[10801,10800,["l",2,21601]],[10806,10805,["l",2,21611]],
[10807,10806,["l",2,21613]],[10809,10808,["l",2,21617]],
[10824,10823,["l",2,21647]],[10825,10824,["l",2,21649]],
[10831,5416,["l",2,10831]],[10831,10830,["l",2,21661]],
[10837,5419,["l",2,10837]],[10837,10836,["l",2,21673]],
[10842,10841,["l",2,21683]],[10847,5424,["l",2,10847]],
[10851,10850,["l",2,21701]],[10853,5427,["l",2,10853]],
[10857,10856,["l",2,21713]],[10859,5430,["l",2,10859]],
[10861,5431,["l",2,10861]],[10864,10863,["l",2,21727]],
[10867,5434,["l",2,10867]],[10869,10868,["l",2,21737]],
[10870,10869,["l",2,21739]],[10876,10875,["l",2,21751]],
[10879,10878,["l",2,21757]],[10883,5442,["l",2,10883]],
[10884,10883,["l",2,21767]],[10887,10886,["l",2,21773]],
[10889,5445,["l",2,10889]],[10891,5446,["l",2,10891]],
[10894,10893,["l",2,21787]],[10900,10899,["l",2,21799]],
[10902,10901,["l",2,21803]],[10903,5452,["l",2,10903]],
[10909,5455,["l",2,10909]],[10909,10908,["l",2,21817]],
[10911,10910,["l",2,21821]],[10920,10919,["l",2,21839]],
[10921,10920,["l",2,21841]],[10923,9709,["u",6,8]],
[10926,10925,["l",2,21851]],[10930,10929,["l",2,21859]],
[10932,10931,["l",2,21863]],[10936,10935,["l",2,21871]],
[10937,5469,["l",2,10937]],[10939,5470,["l",2,10939]],
[10941,10940,["l",2,21881]],[10947,10946,["l",2,21893]],
[10949,5475,["l",2,10949]],[10956,10955,["l",2,21911]],
[10957,5479,["l",2,10957]],[10965,10964,["l",2,21929]],
[10969,10968,["l",2,21937]],[10972,10971,["l",2,21943]],
[10973,5487,["l",2,10973]],[10979,5490,["l",2,10979]],
[10981,10920,["l",3,181]],[10981,10980,["l",2,21961]],
[10987,5494,["l",2,10987]],[10989,10988,["l",2,21977]],
[10993,5497,["l",2,10993]],[10996,10995,["l",2,21991]],
[10999,10998,["l",2,21997]],[11002,11001,["l",2,22003]],
[11003,5502,["l",2,11003]],[11007,11006,["l",2,22013]],
[11014,11013,["l",2,22027]],[11016,11015,["l",2,22031]],
[11019,11018,["l",2,22037]],[11020,11019,["l",2,22039]],
[11026,11025,["l",2,22051]],[11027,5514,["l",2,11027]],
[11032,11031,["l",2,22063]],[11034,11033,["l",2,22067]],
[11037,11036,["l",2,22073]],[11040,11039,["l",2,22079]],
[11046,11045,["l",2,22091]],[11047,5524,["l",2,11047]],
[11047,11046,["l",2,22093]],[11055,11054,["l",2,22109]],
[11056,11055,["l",2,22111]],[11057,5529,["l",2,11057]],
[11059,5530,["l",2,11059]],[11062,11061,["l",2,22123]],
[11065,11064,["l",2,22129]],[11067,11066,["l",2,22133]],
[11069,5535,["l",2,11069]],[11071,5536,["l",2,11071]],
[11074,11073,["l",2,22147]],[11077,11076,["l",2,22153]],
[11079,11078,["l",2,22157]],[11080,11079,["l",2,22159]],
[11083,5542,["l",2,11083]],[11086,11085,["l",2,22171]],
[11087,5544,["l",2,11087]],[11093,5547,["l",2,11093]],
[11095,11094,["l",2,22189]],[11097,11096,["l",2,22193]],
[11101,11100,["l",2,22201]],[11101,11100,["s",4,149]],
[11113,5557,["l",2,11113]],[11115,11114,["l",2,22229]],
[11117,5559,["l",2,11117]],[11119,5560,["l",2,11119]],
[11124,11123,["l",2,22247]],[11130,11129,["l",2,22259]],
[11131,5566,["l",2,11131]],[11136,11135,["l",2,22271]],
[11137,11136,["l",2,22273]],[11139,11138,["l",2,22277]],
[11140,11139,["l",2,22279]],[11142,11141,["l",2,22283]],
[11146,11145,["l",2,22291]],[11149,5575,["l",2,11149]],
[11152,11151,["l",2,22303]],[11154,11153,["l",2,22307]],
[11159,5580,["l",2,11159]],[11161,5581,["l",2,11161]],
[11171,5586,["l",2,11171]],[11172,11171,["l",2,22343]],
[11173,5587,["l",2,11173]],[11175,11101,["s",4,149]],
[11175,11174,["l",2,22349]],[11177,5589,["l",2,11177]],
[11184,11183,["l",2,22367]],[11185,11184,["l",2,22369]],
[11191,11190,["l",2,22381]],[11196,11195,["l",2,22391]],
[11197,5599,["l",2,11197]],[11199,11198,["l",2,22397]],
[11205,11204,["l",2,22409]],[11213,5607,["l",2,11213]],
[11217,11216,["l",2,22433]],[11221,11220,["l",2,22441]],
[11224,11223,["l",2,22447]],[11227,11226,["l",2,22453]],
[11235,11234,["l",2,22469]],[11239,5620,["l",2,11239]],
[11241,11240,["l",2,22481]],[11242,11241,["l",2,22483]],
[11243,5622,["l",2,11243]],[11251,5626,["l",2,11251]],
[11251,11250,["l",2,22501]],[11256,11255,["l",2,22511]],
[11257,5629,["l",2,11257]],[11261,5631,["l",2,11261]],
[11266,11265,["l",2,22531]],[11271,11270,["l",2,22541]],
[11272,11271,["l",2,22543]],[11273,5637,["l",2,11273]],
[11275,11274,["l",2,22549]],[11279,5640,["l",2,11279]],
[11284,11283,["l",2,22567]],[11286,11285,["l",2,22571]],
[11287,5644,["l",2,11287]],[11287,11286,["l",2,22573]],
[11299,5650,["l",2,11299]],[11307,11306,["l",2,22613]],
[11310,11309,["l",2,22619]],[11311,5656,["l",2,11311]],
[11311,11310,["l",2,22621]],[11317,5659,["l",2,11317]],
[11319,11318,["l",2,22637]],[11320,11319,["l",2,22639]],
[11321,5661,["l",2,11321]],[11322,11321,["l",2,22643]],
[11326,11325,["l",2,22651]],[11329,5665,["l",2,11329]],
[11335,11334,["l",2,22669]],[11340,11339,["l",2,22679]],
[11342,5725,["s",4,107]],[11342,5778,["s",4,107]],
[11346,11345,["l",2,22691]],[11349,11348,["l",2,22697]],
[11350,11349,["l",2,22699]],[11351,5676,["l",2,11351]],
[11353,5677,["l",2,11353]],[11355,11354,["l",2,22709]],
[11359,11358,["l",2,22717]],[11361,11360,["l",2,22721]],
[11364,11363,["l",2,22727]],[11369,5685,["l",2,11369]],
[11370,11369,["l",2,22739]],[11371,11370,["l",2,22741]],
[11376,11375,["l",2,22751]],[11383,5692,["l",2,11383]],
[11385,11384,["l",2,22769]],[11389,11388,["l",2,22777]],
[11392,11391,["l",2,22783]],[11393,5697,["l",2,11393]],
[11394,11393,["l",2,22787]],[11399,5700,["l",2,11399]],
[11401,11400,["l",2,22801]],[11401,11400,["s",4,151]],
[11404,11403,["l",2,22807]],[11406,11405,["l",2,22811]],
[11409,11408,["l",2,22817]],[11411,5706,["l",2,11411]],
[11423,5712,["l",2,11423]],[11427,11426,["l",2,22853]],
[11430,11429,["l",2,22859]],[11431,11430,["l",2,22861]],
[11436,11435,["l",2,22871]],[11437,5719,["l",2,11437]],
[11439,11438,["l",2,22877]],[11443,5722,["l",2,11443]],
[11447,5724,["l",2,11447]],[11451,11450,["l",2,22901]],
[11454,11453,["l",2,22907]],[11461,11460,["l",2,22921]],
[11467,5734,["l",2,11467]],[11469,11468,["l",2,22937]],
[11471,5736,["l",2,11471]],[11472,11471,["l",2,22943]],
[11476,11401,["s",4,151]],[11481,11480,["l",2,22961]],
[11482,11481,["l",2,22963]],[11483,5742,["l",2,11483]],
[11487,11486,["l",2,22973]],[11489,5745,["l",2,11489]],
[11491,5746,["l",2,11491]],[11497,5749,["l",2,11497]],
[11497,11496,["l",2,22993]],[11502,11501,["l",2,23003]],
[11503,5752,["l",2,11503]],[11506,11505,["l",2,23011]],
[11509,11508,["l",2,23017]],[11511,11510,["l",2,23021]],
[11514,11513,["l",2,23027]],[11515,11514,["l",2,23029]],
[11519,5760,["l",2,11519]],[11520,11519,["l",2,23039]],
[11521,11520,["l",2,23041]],[11527,5764,["l",2,11527]],
[11527,11526,["l",2,23053]],[11529,11528,["l",2,23057]],
[11530,11529,["l",2,23059]],[11532,11531,["l",2,23063]],
[11536,11535,["l",2,23071]],[11541,11540,["l",2,23081]],
[11544,11543,["l",2,23087]],[11549,5775,["l",2,11549]],
[11550,11549,["l",2,23099]],[11551,5776,["l",2,11551]],
[11556,5725,["s",4,107]],[11556,5778,["s",4,107]],
[11556,11342,["s",4,107]],[11557,11448,["l",3,107]],
[11557,11448,["G2",107]],[11557,11449,["G2",107]],
[11557,11556,["G2",107]],[11559,11558,["l",2,23117]],
[11566,11565,["l",2,23131]],[11572,11571,["l",2,23143]],
[11579,5790,["l",2,11579]],[11580,11579,["l",2,23159]],
[11584,11583,["l",2,23167]],[11587,5794,["l",2,11587]],
[11587,11586,["l",2,23173]],[11593,5797,["l",2,11593]],
[11595,11594,["l",2,23189]],[11597,5799,["l",2,11597]],
[11599,11598,["l",2,23197]],[11601,11600,["l",2,23201]],
[11602,11601,["l",2,23203]],[11605,11604,["l",2,23209]],
[11614,11613,["l",2,23227]],[11617,5809,["l",2,11617]],
[11621,5811,["l",2,11621]],[11626,11625,["l",2,23251]],
[11633,5817,["l",2,11633]],[11635,11634,["l",2,23269]],
[11640,11639,["l",2,23279]],[11646,11645,["l",2,23291]],
[11647,11646,["l",2,23293]],[11649,11648,["l",2,23297]],
[11656,11655,["l",2,23311]],[11657,5829,["l",2,11657]],
[11661,11660,["l",2,23321]],[11664,11663,["l",2,23327]],
[11667,11666,["l",2,23333]],[11670,11669,["l",2,23339]],
[11677,5839,["l",2,11677]],[11679,11678,["l",2,23357]],
[11681,5841,["l",2,11681]],[11685,11684,["l",2,23369]],
[11686,11685,["l",2,23371]],[11689,5845,["l",2,11689]],
[11699,5850,["l",2,11699]],[11700,11699,["l",2,23399]],
[11701,5851,["l",2,11701]],[11709,11708,["l",2,23417]],
[11716,11715,["l",2,23431]],[11717,5859,["l",2,11717]],
[11719,5860,["l",2,11719]],[11724,11723,["l",2,23447]],
[11730,11729,["l",2,23459]],[11731,5866,["l",2,11731]],
[11737,11736,["l",2,23473]],[11743,5872,["l",2,11743]],
[11749,11748,["l",2,23497]],[11755,11754,["l",2,23509]],
[11766,11765,["l",2,23531]],[11769,11768,["l",2,23537]],
[11770,11769,["l",2,23539]],[11772,5941,["s",4,109]],
[11772,5995,["s",4,109]],[11775,11774,["l",2,23549]],
[11777,5889,["l",2,11777]],[11779,5890,["l",2,11779]],
[11779,11778,["l",2,23557]],[11781,11780,["l",2,23561]],
[11782,11781,["l",2,23563]],[11783,5892,["l",2,11783]],
[11784,11783,["l",2,23567]],[11789,5895,["l",2,11789]],
[11791,11790,["l",2,23581]],[11797,11796,["l",2,23593]],
[11800,11799,["l",2,23599]],[11801,5901,["l",2,11801]],
[11802,11801,["l",2,23603]],[11805,11804,["l",2,23609]],
[11807,5904,["l",2,11807]],[11812,11811,["l",2,23623]],
[11813,5907,["l",2,11813]],[11814,11813,["l",2,23627]],
[11815,11814,["l",2,23629]],[11817,11816,["l",2,23633]],
[11821,5911,["l",2,11821]],[11827,5914,["l",2,11827]],
[11831,5916,["l",2,11831]],[11832,11831,["l",2,23663]],
[11833,5917,["l",2,11833]],[11835,11834,["l",2,23669]],
[11836,11835,["l",2,23671]],[11839,5920,["l",2,11839]],
[11839,11838,["l",2,23677]],[11844,11843,["l",2,23687]],
[11845,11844,["l",2,23689]],[11860,11859,["l",2,23719]],
[11863,5932,["l",2,11863]],[11867,5934,["l",2,11867]],
[11871,11870,["l",2,23741]],[11872,11871,["l",2,23743]],
[11874,11873,["l",2,23747]],[11877,11876,["l",2,23753]],
[11880,11773,["u",3,109]],[11881,11880,["l",2,23761]],
[11884,11883,["l",2,23767]],[11887,5944,["l",2,11887]],
[11887,11886,["l",2,23773]],[11895,11894,["l",2,23789]],
[11897,5949,["l",2,11897]],[11901,11900,["l",2,23801]],
[11903,5952,["l",2,11903]],[11907,11906,["l",2,23813]],
[11909,5955,["l",2,11909]],[11910,11909,["l",2,23819]],
[11914,11913,["l",2,23827]],[11916,11915,["l",2,23831]],
[11917,11916,["l",2,23833]],[11923,5962,["l",2,11923]],
[11927,5964,["l",2,11927]],[11929,11928,["l",2,23857]],
[11933,5967,["l",2,11933]],[11935,11934,["l",2,23869]],
[11937,11936,["l",2,23873]],[11939,5970,["l",2,11939]],
[11940,11939,["l",2,23879]],[11941,5971,["l",2,11941]],
[11944,11943,["l",2,23887]],[11947,11946,["l",2,23893]],
[11950,11949,["l",2,23899]],[11953,5977,["l",2,11953]],
[11955,11954,["l",2,23909]],[11956,11955,["l",2,23911]],
[11959,5980,["l",2,11959]],[11959,11958,["l",2,23917]],
[11965,11964,["l",2,23929]],[11969,5985,["l",2,11969]],
[11971,5986,["l",2,11971]],[11979,11978,["l",2,23957]],
[11981,5991,["l",2,11981]],[11986,11985,["l",2,23971]],
[11987,5994,["l",2,11987]],[11989,11988,["l",2,23977]],
[11990,5941,["s",4,109]],[11990,5995,["s",4,109]],
[11990,11772,["s",4,109]],[11990,11880,["u",3,109]],
[11991,11880,["G2",109]],[11991,11881,["G2",109]],
[11991,11990,["G2",109]],[11991,11990,["l",2,23981]],
[11997,11996,["l",2,23993]],[12001,12000,["l",2,24001]],
[12004,12003,["l",2,24007]],[12007,6004,["l",2,12007]],
[12010,12009,["l",2,24019]],[12011,6006,["l",2,12011]],
[12012,12011,["l",2,24023]],[12015,12014,["l",2,24029]],
[12022,12021,["l",2,24043]],[12025,12024,["l",2,24049]],
[12031,12030,["l",2,24061]],[12036,12035,["l",2,24071]],
[12037,6019,["l",2,12037]],[12039,12038,["l",2,24077]],
[12041,6021,["l",2,12041]],[12042,12041,["l",2,24083]],
[12043,6022,["l",2,12043]],[12046,12045,["l",2,24091]],
[12049,6025,["l",2,12049]],[12049,12048,["l",2,24097]],
[12052,12051,["l",2,24103]],[12054,12053,["l",2,24107]],
[12055,12054,["l",2,24109]],[12057,12056,["l",2,24113]],
[12061,12060,["l",2,24121]],[12067,12066,["l",2,24133]],
[12069,12068,["l",2,24137]],[12071,6036,["l",2,12071]],
[12073,6037,["l",2,12073]],[12076,12075,["l",2,24151]],
[12085,12084,["l",2,24169]],[12090,12089,["l",2,24179]],
[12091,12090,["l",2,24181]],[12097,6049,["l",2,12097]],
[12099,12098,["l",2,24197]],[12101,6051,["l",2,12101]],
[12102,12101,["l",2,24203]],[12107,6054,["l",2,12107]],
[12109,6055,["l",2,12109]],[12112,12111,["l",2,24223]],
[12113,6057,["l",2,12113]],[12115,12114,["l",2,24229]],
[12119,6060,["l",2,12119]],[12120,12119,["l",2,24239]],
[12124,12123,["l",2,24247]],[12126,12125,["l",2,24251]],
[12141,12140,["l",2,24281]],[12143,6072,["l",2,12143]],
[12144,6360,["s",6,23]],[12149,6075,["l",2,12149]],
[12157,6079,["l",2,12157]],[12159,12158,["l",2,24317]],
[12160,12097,["u",3,191]],[12161,6081,["l",2,12161]],
[12163,6082,["l",2,12163]],[12165,12164,["l",2,24329]],
[12169,12168,["l",2,24337]],[12180,12179,["l",2,24359]],
[12186,12185,["l",2,24371]],[12187,12186,["l",2,24373]],
[12190,6360,["s",6,23]],[12190,12144,["s",6,23]],
[12190,12189,["l",2,24379]],[12195,11788,["u",4,29]],
[12195,12180,["u",4,29]],[12195,12194,["l",2,24389]],
[12196,12195,["l",2,24391]],[12197,6099,["l",2,12197]],
[12203,6102,["l",2,12203]],[12204,12203,["l",2,24407]],
[12207,12206,["l",2,24413]],[12210,12209,["l",2,24419]],
[12211,6106,["l",2,12211]],[12211,12210,["l",2,24421]],
[12220,12219,["l",2,24439]],[12222,12221,["l",2,24443]],
[12224,12160,["u",3,191]],[12227,6114,["l",2,12227]],
[12235,12234,["l",2,24469]],[12237,12236,["l",2,24473]],
[12239,6120,["l",2,12239]],[12241,6121,["l",2,12241]],
[12241,12240,["l",2,24481]],[12250,12249,["l",2,24499]],
[12251,6126,["l",2,12251]],[12253,6127,["l",2,12253]],
[12255,12254,["l",2,24509]],[12259,12258,["l",2,24517]],
[12263,6132,["l",2,12263]],[12264,12263,["l",2,24527]],
[12267,12266,["l",2,24533]],[12269,6135,["l",2,12269]],
[12274,12273,["l",2,24547]],[12276,12275,["l",2,24551]],
[12277,6139,["l",2,12277]],[12281,6141,["l",2,12281]],
[12286,12285,["l",2,24571]],[12289,6145,["l",2,12289]],
[12297,12296,["l",2,24593]],[12301,6151,["l",2,12301]],
[12306,12305,["l",2,24611]],[12312,12311,["l",2,24623]],
[12316,12315,["l",2,24631]],[12323,6162,["l",2,12323]],
[12325,12324,["l",2,24649]],[12325,12324,["s",4,157]],
[12329,6165,["l",2,12329]],[12330,12329,["l",2,24659]],
[12336,12335,["l",2,24671]],[12339,12338,["l",2,24677]],
[12342,12341,["l",2,24683]],[12343,6172,["l",2,12343]],
[12346,12345,["l",2,24691]],[12347,6174,["l",2,12347]],
[12349,12348,["l",2,24697]],[12355,12354,["l",2,24709]],
[12367,12366,["l",2,24733]],[12373,6187,["l",2,12373]],
[12375,12374,["l",2,24749]],[12377,6189,["l",2,12377]],
[12379,6190,["l",2,12379]],[12382,12381,["l",2,24763]],
[12384,12383,["l",2,24767]],[12391,6196,["l",2,12391]],
[12391,12390,["l",2,24781]],[12397,12396,["l",2,24793]],
[12400,12399,["l",2,24799]],[12401,6201,["l",2,12401]],
[12403,12325,["s",4,157]],[12405,12404,["l",2,24809]],
[12409,6205,["l",2,12409]],[12411,12410,["l",2,24821]],
[12413,6207,["l",2,12413]],[12421,6211,["l",2,12421]],
[12421,12420,["l",2,24841]],[12424,12423,["l",2,24847]],
[12426,12425,["l",2,24851]],[12430,12429,["l",2,24859]],
[12433,6217,["l",2,12433]],[12437,6219,["l",2,12437]],
[12439,12438,["l",2,24877]],[12445,12444,["l",2,24889]],
[12451,6226,["l",2,12451]],[12454,12453,["l",2,24907]],
[12457,6229,["l",2,12457]],[12459,12458,["l",2,24917]],
[12460,12459,["l",2,24919]],[12462,12461,["l",2,24923]],
[12472,12471,["l",2,24943]],[12473,6237,["l",2,12473]],
[12477,12476,["l",2,24953]],[12479,6240,["l",2,12479]],
[12481,12416,["l",3,193]],[12484,12483,["l",2,24967]],
[12486,12485,["l",2,24971]],[12487,6244,["l",2,12487]],
[12489,12488,["l",2,24977]],[12490,12489,["l",2,24979]],
[12491,6246,["l",2,12491]],[12495,12494,["l",2,24989]],
[12497,6249,["l",2,12497]],[12503,6252,["l",2,12503]],
[12507,12506,["l",2,25013]],[12511,6256,["l",2,12511]],
[12516,12515,["l",2,25031]],[12517,6259,["l",2,12517]],
[12517,12516,["l",2,25033]],[12519,12518,["l",2,25037]],
[12527,6264,["l",2,12527]],[12529,12528,["l",2,25057]],
[12537,12536,["l",2,25073]],[12539,6270,["l",2,12539]],
[12541,6271,["l",2,12541]],[12544,12543,["l",2,25087]],
[12547,6274,["l",2,12547]],[12549,12548,["l",2,25097]],
[12553,6277,["l",2,12553]],[12556,12555,["l",2,25111]],
[12559,12558,["l",2,25117]],[12561,12560,["l",2,25121]],
[12564,12563,["l",2,25127]],[12569,6285,["l",2,12569]],
[12574,12573,["l",2,25147]],[12577,6289,["l",2,12577]],
[12577,12576,["l",2,25153]],[12582,12581,["l",2,25163]],
[12583,6292,["l",2,12583]],[12584,9841,["E8",3]],
[12585,12584,["l",2,25169]],[12586,12585,["l",2,25171]],
[12589,6295,["l",2,12589]],[12592,12591,["l",2,25183]],
[12595,12594,["l",2,25189]],[12601,6301,["l",2,12601]],
[12610,12609,["l",2,25219]],[12611,6306,["l",2,12611]],
[12613,6307,["l",2,12613]],[12615,12614,["l",2,25229]],
[12619,6310,["l",2,12619]],[12619,12618,["l",2,25237]],
[12622,12621,["l",2,25243]],[12624,12623,["l",2,25247]],
[12627,12626,["l",2,25253]],[12630,12195,["o",7,29]],
[12630,12195,["s",6,29]],[12630,12209,["o",7,29]],
[12630,12209,["s",6,29]],[12631,12630,["l",2,25261]],
[12637,6319,["l",2,12637]],[12641,6321,["l",2,12641]],
[12647,6324,["l",2,12647]],[12651,12650,["l",2,25301]],
[12652,12651,["l",2,25303]],[12653,6327,["l",2,12653]],
[12654,12653,["l",2,25307]],[12655,12654,["l",2,25309]],
[12656,6385,["s",4,113]],[12656,6441,["s",4,113]],
[12659,6330,["l",2,12659]],[12661,12660,["l",2,25321]],
[12670,12669,["l",2,25339]],[12671,6336,["l",2,12671]],
[12672,12671,["l",2,25343]],[12675,12674,["l",2,25349]],
[12679,12678,["l",2,25357]],[12684,12683,["l",2,25367]],
[12687,12686,["l",2,25373]],[12689,6345,["l",2,12689]],
[12696,12695,["l",2,25391]],[12697,6349,["l",2,12697]],
[12703,6352,["l",2,12703]],[12705,12704,["l",2,25409]],
[12706,12705,["l",2,25411]],[12712,12711,["l",2,25423]],
[12713,6357,["l",2,12713]],[12720,12719,["l",2,25439]],
[12721,6361,["l",2,12721]],[12724,12723,["l",2,25447]],
[12727,12726,["l",2,25453]],[12729,12728,["l",2,25457]],
[12732,12731,["l",2,25463]],[12735,12734,["l",2,25469]],
[12736,12735,["l",2,25471]],[12739,6370,["l",2,12739]],
[12743,6372,["l",2,12743]],[12757,6379,["l",2,12757]],
[12762,12761,["l",2,25523]],[12763,6382,["l",2,12763]],
[12769,12768,["l",2,25537]],[12771,12770,["l",2,25541]],
[12781,6391,["l",2,12781]],[12781,12780,["l",2,25561]],
[12789,12788,["l",2,25577]],[12790,12789,["l",2,25579]],
[12791,6396,["l",2,12791]],[12792,12791,["l",2,25583]],
[12795,12794,["l",2,25589]],[12799,6400,["l",2,12799]],
[12801,12800,["l",2,25601]],[12802,12801,["l",2,25603]],
[12805,12804,["l",2,25609]],[12809,6405,["l",2,12809]],
[12811,12810,["l",2,25621]],[12817,12816,["l",2,25633]],
[12820,12819,["l",2,25639]],[12821,6411,["l",2,12821]],
[12822,12821,["l",2,25643]],[12823,6412,["l",2,12823]],
[12829,6415,["l",2,12829]],[12829,12828,["l",2,25657]],
[12834,12833,["l",2,25667]],[12837,12836,["l",2,25673]],
[12840,12839,["l",2,25679]],[12841,6421,["l",2,12841]],
[12847,12846,["l",2,25693]],[12852,12851,["l",2,25703]],
[12853,6427,["l",2,12853]],[12859,12858,["l",2,25717]],
[12867,12866,["l",2,25733]],[12871,12870,["l",2,25741]],
[12874,12873,["l",2,25747]],[12880,12879,["l",2,25759]],
[12882,6385,["s",4,113]],[12882,6441,["s",4,113]],
[12882,12656,["s",4,113]],[12882,12881,["l",2,25763]],
[12883,12768,["l",3,113]],[12883,12768,["G2",113]],
[12883,12769,["G2",113]],[12883,12882,["G2",113]],
[12886,12885,["l",2,25771]],[12889,6445,["l",2,12889]],
[12893,6447,["l",2,12893]],[12897,12896,["l",2,25793]],
[12899,6450,["l",2,12899]],[12900,12899,["l",2,25799]],
[12901,12900,["l",2,25801]],[12907,6454,["l",2,12907]],
[12910,12909,["l",2,25819]],[12911,6456,["l",2,12911]],
[12917,6459,["l",2,12917]],[12919,6460,["l",2,12919]],
[12921,12920,["l",2,25841]],[12923,6462,["l",2,12923]],
[12924,12923,["l",2,25847]],[12925,12924,["l",2,25849]],
[12934,12933,["l",2,25867]],[12936,12871,["u",3,197]],
[12937,12936,["l",2,25873]],[12941,6471,["l",2,12941]],
[12945,12944,["l",2,25889]],[12952,12951,["l",2,25903]],
[12953,6477,["l",2,12953]],[12957,12956,["l",2,25913]],
[12959,6480,["l",2,12959]],[12960,12959,["l",2,25919]],
[12966,12965,["l",2,25931]],[12967,6484,["l",2,12967]],
[12967,12966,["l",2,25933]],[12970,12969,["l",2,25939]],
[12972,12971,["l",2,25943]],[12973,6487,["l",2,12973]],
[12976,12975,["l",2,25951]],[12979,6490,["l",2,12979]],
[12983,6492,["l",2,12983]],[12985,12984,["l",2,25969]],
[12991,12990,["l",2,25981]],[12999,12998,["l",2,25997]],
[13000,12999,["l",2,25999]],[13001,6501,["l",2,13001]],
[13002,12936,["u",3,197]],[13002,13001,["l",2,26003]],
[13003,6502,["l",2,13003]],[13007,6504,["l",2,13007]],
[13009,6505,["l",2,13009]],[13009,13008,["l",2,26017]],
[13011,13010,["l",2,26021]],[13015,12663,["l",4,37]],
[13015,13014,["l",2,26029]],[13021,13020,["l",2,26041]],
[13027,13026,["l",2,26053]],[13033,6517,["l",2,13033]],
[13037,6519,["l",2,13037]],[13042,13041,["l",2,26083]],
[13043,6522,["l",2,13043]],[13049,6525,["l",2,13049]],
[13050,13049,["l",2,26099]],[13054,13053,["l",2,26107]],
[13056,13055,["l",2,26111]],[13057,13056,["l",2,26113]],
[13060,13059,["l",2,26119]],[13063,6532,["l",2,13063]],
[13071,13070,["l",2,26141]],[13077,13076,["l",2,26153]],
[13081,13080,["l",2,26161]],[13086,13085,["l",2,26171]],
[13089,13088,["l",2,26177]],[13092,13091,["l",2,26183]],
[13093,6547,["l",2,13093]],[13095,13094,["l",2,26189]],
[13099,6550,["l",2,13099]],[13102,13101,["l",2,26203]],
[13103,6552,["l",2,13103]],[13105,13104,["l",2,26209]],
[13107,11811,["o-",26,2]],[13107,12090,["o-",26,2]],
[13107,12954,["o-",26,2]],[13109,6555,["l",2,13109]],
[13114,13113,["l",2,26227]],[13119,13118,["l",2,26237]],
[13121,6561,["l",2,13121]],[13124,10940,["o+",18,3]],
[13124,10940,["o",19,3]],[13124,10940,["s",18,3]],
[13124,10980,["o",19,3]],[13124,10980,["s",18,3]],
[13124,13116,["o",19,3]],[13124,13116,["o+",18,3]],
[13124,13116,["s",18,3]],[13125,13124,["l",2,26249]],
[13126,13125,["l",2,26251]],[13127,6564,["l",2,13127]],
[13131,13130,["l",2,26261]],[13132,13131,["l",2,26263]],
[13134,13133,["l",2,26267]],[13140,13124,["o",19,3]],
[13140,13124,["s",18,3]],[13147,6574,["l",2,13147]],
[13147,13146,["l",2,26293]],[13149,13148,["l",2,26297]],
[13151,6576,["l",2,13151]],[13155,13154,["l",2,26309]],
[13159,6580,["l",2,13159]],[13159,13158,["l",2,26317]],
[13161,13160,["l",2,26321]],[13163,6582,["l",2,13163]],
[13170,13169,["l",2,26339]],[13171,6586,["l",2,13171]],
[13174,13173,["l",2,26347]],[13177,6589,["l",2,13177]],
[13179,13178,["l",2,26357]],[13183,6592,["l",2,13183]],
[13186,13185,["l",2,26371]],[13187,6594,["l",2,13187]],
[13194,13193,["l",2,26387]],[13197,13196,["l",2,26393]],
[13200,13199,["l",2,26399]],[13204,13203,["l",2,26407]],
[13209,13208,["l",2,26417]],[13212,13211,["l",2,26423]],
[13216,13215,["l",2,26431]],[13217,6609,["l",2,13217]],
[13219,6610,["l",2,13219]],[13219,13218,["l",2,26437]],
[13225,13224,["l",2,26449]],[13229,6615,["l",2,13229]],
[13230,13229,["l",2,26459]],[13240,13239,["l",2,26479]],
[13241,6621,["l",2,13241]],[13245,13244,["l",2,26489]],
[13249,6625,["l",2,13249]],[13249,13248,["l",2,26497]],
[13251,13250,["l",2,26501]],[13257,13256,["l",2,26513]],
[13259,6630,["l",2,13259]],[13260,13107,["o-",26,2]],
[13267,6634,["l",2,13267]],[13267,13200,["l",3,199]],
[13270,13269,["l",2,26539]],[13279,13278,["l",2,26557]],
[13281,13280,["l",2,26561]],[13285,13284,["l",2,26569]],
[13285,13284,["s",4,163]],[13287,13286,["l",2,26573]],
[13291,6646,["l",2,13291]],[13296,13295,["l",2,26591]],
[13297,6649,["l",2,13297]],[13299,13298,["l",2,26597]],
[13309,6655,["l",2,13309]],[13313,6657,["l",2,13313]],
[13314,13313,["l",2,26627]],[13317,13316,["l",2,26633]],
[13321,13320,["l",2,26641]],[13324,13323,["l",2,26647]],
[13327,6664,["l",2,13327]],[13331,6666,["l",2,13331]],
[13335,12291,["o+",26,2]],[13335,12300,["o+",26,2]],
[13335,13020,["o+",26,2]],[13335,13107,["s",26,2]],
[13335,13260,["s",26,2]],[13335,13334,["l",2,26669]],
[13337,6669,["l",2,13337]],[13339,6670,["l",2,13339]],
[13341,13340,["l",2,26681]],[13342,13341,["l",2,26683]],
[13344,13343,["l",2,26687]],[13347,13346,["l",2,26693]],
[13350,13349,["l",2,26699]],[13351,13350,["l",2,26701]],
[13356,13355,["l",2,26711]],[13357,13356,["l",2,26713]],
[13359,13358,["l",2,26717]],[13362,13361,["l",2,26723]],
[13365,13364,["l",2,26729]],[13366,13285,["s",4,163]],
[13366,13365,["l",2,26731]],[13367,6684,["l",2,13367]],
[13369,13368,["l",2,26737]],[13380,13379,["l",2,26759]],
[13381,6691,["l",2,13381]],[13389,13388,["l",2,26777]],
[13392,13391,["l",2,26783]],[13397,6699,["l",2,13397]],
[13399,6700,["l",2,13399]],[13401,13400,["l",2,26801]],
[13407,13406,["l",2,26813]],[13411,6706,["l",2,13411]],
[13411,13410,["l",2,26821]],[13417,6709,["l",2,13417]],
[13417,13416,["l",2,26833]],[13420,13419,["l",2,26839]],
[13421,6711,["l",2,13421]],[13425,13424,["l",2,26849]],
[13431,13430,["l",2,26861]],[13432,13431,["l",2,26863]],
[13440,13439,["l",2,26879]],[13441,6721,["l",2,13441]],
[13441,13440,["l",2,26881]],[13446,13445,["l",2,26891]],
[13447,13446,["l",2,26893]],[13451,6726,["l",2,13451]],
[13452,13451,["l",2,26903]],[13457,6729,["l",2,13457]],
[13461,13460,["l",2,26921]],[13463,6732,["l",2,13463]],
[13464,13463,["l",2,26927]],[13469,6735,["l",2,13469]],
[13474,13473,["l",2,26947]],[13476,13475,["l",2,26951]],
[13477,6739,["l",2,13477]],[13477,13476,["l",2,26953]],
[13480,13479,["l",2,26959]],[13487,6744,["l",2,13487]],
[13491,13490,["l",2,26981]],[13494,13493,["l",2,26987]],
[13497,13496,["l",2,26993]],[13499,6750,["l",2,13499]],
[13506,13505,["l",2,27011]],[13509,13508,["l",2,27017]],
[13513,6757,["l",2,13513]],[13516,13515,["l",2,27031]],
[13522,13521,["l",2,27043]],[13523,6762,["l",2,13523]],
[13530,13529,["l",2,27059]],[13531,13530,["l",2,27061]],
[13534,13533,["l",2,27067]],[13537,6769,["l",2,13537]],
[13537,13536,["l",2,27073]],[13539,13538,["l",2,27077]],
[13546,13545,["l",2,27091]],[13552,13551,["l",2,27103]],
[13553,6777,["l",2,13553]],[13554,13553,["l",2,27107]],
[13555,13554,["l",2,27109]],[13564,13563,["l",2,27127]],
[13567,6784,["l",2,13567]],[13572,13571,["l",2,27143]],
[13577,6789,["l",2,13577]],[13590,13589,["l",2,27179]],
[13591,6796,["l",2,13591]],[13596,13595,["l",2,27191]],
[13597,6799,["l",2,13597]],[13599,13598,["l",2,27197]],
[13606,13605,["l",2,27211]],[13613,6807,["l",2,13613]],
[13619,6810,["l",2,13619]],[13620,13619,["l",2,27239]],
[13621,13620,["l",2,27241]],[13627,6814,["l",2,13627]],
[13627,13626,["l",2,27253]],[13630,13629,["l",2,27259]],
[13633,6817,["l",2,13633]],[13636,13635,["l",2,27271]],
[13639,13638,["l",2,27277]],[13641,13640,["l",2,27281]],
[13642,13641,["l",2,27283]],[13649,6825,["l",2,13649]],
[13650,13649,["l",2,27299]],[13665,13664,["l",2,27329]],
[13669,6835,["l",2,13669]],[13669,13668,["l",2,27337]],
[13679,6840,["l",2,13679]],[13681,6841,["l",2,13681]],
[13681,13680,["l",2,27361]],[13684,13683,["l",2,27367]],
[13687,6844,["l",2,13687]],[13691,6846,["l",2,13691]],
[13693,6847,["l",2,13693]],[13697,6849,["l",2,13697]],
[13699,13698,["l",2,27397]],[13704,13703,["l",2,27407]],
[13705,13704,["l",2,27409]],[13709,6855,["l",2,13709]],
[13711,6856,["l",2,13711]],[13714,13713,["l",2,27427]],
[13716,13715,["l",2,27431]],[13719,13718,["l",2,27437]],
[13721,6861,["l",2,13721]],[13723,6862,["l",2,13723]],
[13725,13724,["l",2,27449]],[13729,6865,["l",2,13729]],
[13729,13728,["l",2,27457]],[13740,13739,["l",2,27479]],
[13741,13740,["l",2,27481]],[13744,13743,["l",2,27487]],
[13751,6876,["l",2,13751]],[13755,13754,["l",2,27509]],
[13757,6879,["l",2,13757]],[13759,6880,["l",2,13759]],
[13763,6882,["l",2,13763]],[13764,13763,["l",2,27527]],
[13765,13764,["l",2,27529]],[13770,13769,["l",2,27539]],
[13771,13770,["l",2,27541]],[13776,13775,["l",2,27551]],
[13781,6891,["l",2,13781]],[13789,6895,["l",2,13789]],
[13791,13790,["l",2,27581]],[13792,13791,["l",2,27583]],
[13799,6900,["l",2,13799]],[13806,13805,["l",2,27611]],
[13807,6904,["l",2,13807]],[13809,13808,["l",2,27617]],
[13816,13815,["l",2,27631]],[13824,13823,["l",2,27647]],
[13827,13826,["l",2,27653]],[13829,6915,["l",2,13829]],
[13831,6916,["l",2,13831]],[13837,13836,["l",2,27673]],
[13841,6921,["l",2,13841]],[13845,13844,["l",2,27689]],
[13846,13845,["l",2,27691]],[13849,13848,["l",2,27697]],
[13851,13850,["l",2,27701]],[13859,6930,["l",2,13859]],
[13867,13866,["l",2,27733]],[13869,13868,["l",2,27737]],
[13870,13869,["l",2,27739]],[13872,13871,["l",2,27743]],
[13873,6937,["l",2,13873]],[13875,13874,["l",2,27749]],
[13876,13875,["l",2,27751]],[13877,6939,["l",2,13877]],
[13879,6940,["l",2,13879]],[13882,13881,["l",2,27763]],
[13883,6942,["l",2,13883]],[13884,13883,["l",2,27767]],
[13887,13886,["l",2,27773]],[13890,13889,["l",2,27779]],
[13896,13895,["l",2,27791]],[13897,13896,["l",2,27793]],
[13900,13899,["l",2,27799]],[13901,6951,["l",2,13901]],
[13902,13901,["l",2,27803]],[13903,6952,["l",2,13903]],
[13905,13904,["l",2,27809]],[13907,6954,["l",2,13907]],
[13909,13908,["l",2,27817]],[13912,13911,["l",2,27823]],
[13913,6957,["l",2,13913]],[13914,13913,["l",2,27827]],
[13921,6961,["l",2,13921]],[13924,13923,["l",2,27847]],
[13926,13925,["l",2,27851]],[13931,6966,["l",2,13931]],
[13933,6967,["l",2,13933]],[13942,13941,["l",2,27883]],
[13945,13944,["l",2,27889]],[13945,13944,["s",4,167]],
[13947,13946,["l",2,27893]],[13951,13950,["l",2,27901]],
[13959,13958,["l",2,27917]],[13960,13959,["l",2,27919]],
[13963,6982,["l",2,13963]],[13967,6984,["l",2,13967]],
[13971,13970,["l",2,27941]],[13972,13971,["l",2,27943]],
[13974,13973,["l",2,27947]],[13977,13976,["l",2,27953]],
[13981,13923,["l",5,16]],[13981,13980,["l",2,27961]],
[13984,13983,["l",2,27967]],[13992,13991,["l",2,27983]],
[13997,6999,["l",2,13997]],[13999,7000,["l",2,13999]],
[13999,13998,["l",2,27997]],[14001,14000,["l",2,28001]],
[14009,7005,["l",2,14009]],[14010,14009,["l",2,28019]],
[14011,7006,["l",2,14011]],[14014,14013,["l",2,28027]],
[14016,14015,["l",2,28031]],[14026,14025,["l",2,28051]],
[14028,13945,["s",4,167]],[14029,7015,["l",2,14029]],
[14029,14028,["l",2,28057]],[14033,7017,["l",2,14033]],
[14035,14034,["l",2,28069]],[14041,14040,["l",2,28081]],
[14044,14043,["l",2,28087]],[14049,14048,["l",2,28097]],
[14050,14049,["l",2,28099]],[14051,7026,["l",2,14051]],
[14055,14054,["l",2,28109]],[14056,14055,["l",2,28111]],
[14057,7029,["l",2,14057]],[14062,14061,["l",2,28123]],
[14071,7036,["l",2,14071]],[14076,14075,["l",2,28151]],
[14081,7041,["l",2,14081]],[14082,14081,["l",2,28163]],
[14083,7042,["l",2,14083]],[14087,7044,["l",2,14087]],
[14091,14090,["l",2,28181]],[14092,14091,["l",2,28183]],
[14101,14100,["l",2,28201]],[14106,14105,["l",2,28211]],
[14107,7054,["l",2,14107]],[14110,14109,["l",2,28219]],
[14115,14114,["l",2,28229]],[14139,14138,["l",2,28277]],
[14140,14139,["l",2,28279]],[14142,14141,["l",2,28283]],
[14143,7072,["l",2,14143]],[14145,14144,["l",2,28289]],
[14149,7075,["l",2,14149]],[14149,14148,["l",2,28297]],
[14153,7077,["l",2,14153]],[14154,14153,["l",2,28307]],
[14155,14154,["l",2,28309]],[14159,7080,["l",2,14159]],
[14160,14159,["l",2,28319]],[14173,7087,["l",2,14173]],
[14175,14174,["l",2,28349]],[14176,14175,["l",2,28351]],
[14177,7089,["l",2,14177]],[14194,14193,["l",2,28387]],
[14197,7099,["l",2,14197]],[14197,14196,["l",2,28393]],
[14202,14201,["l",2,28403]],[14205,14204,["l",2,28409]],
[14206,14205,["l",2,28411]],[14207,7104,["l",2,14207]],
[14215,14214,["l",2,28429]],[14217,14216,["l",2,28433]],
[14220,14219,["l",2,28439]],[14221,7111,["l",2,14221]],
[14224,14223,["l",2,28447]],[14232,14231,["l",2,28463]],
[14239,14238,["l",2,28477]],[14243,7122,["l",2,14243]],
[14247,14246,["l",2,28493]],[14249,7125,["l",2,14249]],
[14250,14249,["l",2,28499]],[14251,7126,["l",2,14251]],
[14257,14256,["l",2,28513]],[14259,14258,["l",2,28517]],
[14269,14268,["l",2,28537]],[14271,14270,["l",2,28541]],
[14274,14273,["l",2,28547]],[14275,14274,["l",2,28549]],
[14280,14279,["l",2,28559]],[14281,7141,["l",2,14281]],
[14281,14280,["l",2,28561]],[14281,14280,["s",4,169]],
[14286,14285,["l",2,28571]],[14287,14286,["l",2,28573]],
[14290,14289,["l",2,28579]],[14293,7147,["l",2,14293]],
[14296,14295,["l",2,28591]],[14299,14298,["l",2,28597]],
[14302,14301,["l",2,28603]],[14303,7152,["l",2,14303]],
[14304,14303,["l",2,28607]],[14310,14309,["l",2,28619]],
[14311,14310,["l",2,28621]],[14314,14313,["l",2,28627]],
[14316,14315,["l",2,28631]],[14321,7161,["l",2,14321]],
[14322,14321,["l",2,28643]],[14323,7162,["l",2,14323]],
[14325,14324,["l",2,28649]],[14327,7164,["l",2,14327]],
[14329,14328,["l",2,28657]],[14331,14330,["l",2,28661]],
[14332,14331,["l",2,28663]],[14335,14334,["l",2,28669]],
[14341,7171,["l",2,14341]],[14344,14343,["l",2,28687]],
[14347,7174,["l",2,14347]],[14349,14348,["l",2,28697]],
[14352,14351,["l",2,28703]],[14356,14355,["l",2,28711]],
[14362,14361,["l",2,28723]],[14365,14364,["l",2,28729]],
[14369,7185,["l",2,14369]],[14376,14375,["l",2,28751]],
[14377,14376,["l",2,28753]],[14380,14379,["l",2,28759]],
[14386,14385,["l",2,28771]],[14387,7194,["l",2,14387]],
[14389,7195,["l",2,14389]],[14395,14394,["l",2,28789]],
[14397,14396,["l",2,28793]],[14401,7201,["l",2,14401]],
[14404,14403,["l",2,28807]],[14407,7204,["l",2,14407]],
[14407,14406,["l",2,28813]],[14409,14408,["l",2,28817]],
[14411,7206,["l",2,14411]],[14419,7210,["l",2,14419]],
[14419,14418,["l",2,28837]],[14422,14421,["l",2,28843]],
[14423,7212,["l",2,14423]],[14430,14429,["l",2,28859]],
[14431,7216,["l",2,14431]],[14434,14433,["l",2,28867]],
[14436,14435,["l",2,28871]],[14437,7219,["l",2,14437]],
[14440,14439,["l",2,28879]],[14447,7224,["l",2,14447]],
[14449,7225,["l",2,14449]],[14451,14450,["l",2,28901]],
[14455,14454,["l",2,28909]],[14461,7231,["l",2,14461]],
[14461,14460,["l",2,28921]],[14464,14463,["l",2,28927]],
[14467,14466,["l",2,28933]],[14475,14474,["l",2,28949]],
[14479,7240,["l",2,14479]],[14481,14480,["l",2,28961]],
[14489,7245,["l",2,14489]],[14490,14489,["l",2,28979]],
[14503,7252,["l",2,14503]],[14505,14504,["l",2,29009]],
[14509,14508,["l",2,29017]],[14511,14510,["l",2,29021]],
[14512,14511,["l",2,29023]],[14514,14513,["l",2,29027]],
[14517,14516,["l",2,29033]],[14519,7260,["l",2,14519]],
[14530,14529,["l",2,29059]],[14532,14531,["l",2,29063]],
[14533,7267,["l",2,14533]],[14537,7269,["l",2,14537]],
[14539,14538,["l",2,29077]],[14543,7272,["l",2,14543]],
[14549,7275,["l",2,14549]],[14551,7276,["l",2,14551]],
[14551,14550,["l",2,29101]],[14557,7279,["l",2,14557]],
[14561,7281,["l",2,14561]],[14562,14561,["l",2,29123]],
[14563,7282,["l",2,14563]],[14565,14564,["l",2,29129]],
[14566,14565,["l",2,29131]],[14569,14568,["l",2,29137]],
[14574,14573,["l",2,29147]],[14577,14576,["l",2,29153]],
[14584,14583,["l",2,29167]],[14587,14586,["l",2,29173]],
[14590,14589,["l",2,29179]],[14591,7296,["l",2,14591]],
[14593,7297,["l",2,14593]],[14596,14595,["l",2,29191]],
[14601,14600,["l",2,29201]],[14604,14603,["l",2,29207]],
[14605,14604,["l",2,29209]],[14611,14610,["l",2,29221]],
[14616,14615,["l",2,29231]],[14621,7311,["l",2,14621]],
[14622,14621,["l",2,29243]],[14626,14625,["l",2,29251]],
[14627,7314,["l",2,14627]],[14629,7315,["l",2,14629]],
[14630,7980,["s",8,11]],[14630,8052,["s",8,11]],
[14633,7317,["l",2,14633]],[14635,14634,["l",2,29269]],
[14639,7320,["l",2,14639]],[14640,13421,["u",5,11]],
[14640,14521,["u",3,121]],[14644,14643,["l",2,29287]],
[14649,14648,["l",2,29297]],[14652,7980,["s",8,11]],
[14652,8052,["s",8,11]],[14652,14630,["s",8,11]],
[14652,14640,["u",5,11]],[14652,14651,["l",2,29303]],
[14653,7327,["l",2,14653]],[14656,14655,["l",2,29311]],
[14657,7329,["l",2,14657]],[14664,14663,["l",2,29327]],
[14667,14666,["l",2,29333]],[14669,7335,["l",2,14669]],
[14670,14669,["l",2,29339]],[14674,14673,["l",2,29347]],
[14682,14681,["l",2,29363]],[14683,7342,["l",2,14683]],
[14692,14691,["l",2,29383]],[14694,14693,["l",2,29387]],
[14695,14694,["l",2,29389]],[14699,7350,["l",2,14699]],
[14700,14699,["l",2,29399]],[14701,14700,["l",2,29401]],
[14706,14705,["l",2,29411]],[14712,14711,["l",2,29423]],
[14713,7357,["l",2,14713]],[14715,14714,["l",2,29429]],
[14717,7359,["l",2,14717]],[14719,14718,["l",2,29437]],
[14722,14721,["l",2,29443]],[14723,7362,["l",2,14723]],
[14727,14726,["l",2,29453]],[14731,7366,["l",2,14731]],
[14737,7369,["l",2,14737]],[14737,14736,["l",2,29473]],
[14741,7371,["l",2,14741]],[14742,14741,["l",2,29483]],
[14747,7374,["l",2,14747]],[14751,14750,["l",2,29501]],
[14753,7377,["l",2,14753]],[14759,7380,["l",2,14759]],
[14762,14209,["l",10,3]],[14763,14640,["G2",121]],
[14764,14763,["l",2,29527]],[14766,14765,["l",2,29531]],
[14767,7384,["l",2,14767]],[14769,14768,["l",2,29537]],
[14771,7386,["l",2,14771]],[14779,7390,["l",2,14779]],
[14783,7392,["l",2,14783]],[14784,14783,["l",2,29567]],
[14785,14784,["l",2,29569]],[14787,14786,["l",2,29573]],
[14791,14790,["l",2,29581]],[14794,14793,["l",2,29587]],
[14797,7399,["l",2,14797]],[14800,14799,["l",2,29599]],
[14806,14805,["l",2,29611]],[14813,7407,["l",2,14813]],
[14815,14814,["l",2,29629]],[14817,14816,["l",2,29633]],
[14821,7411,["l",2,14821]],[14821,14820,["l",2,29641]],
[14827,7414,["l",2,14827]],[14831,7416,["l",2,14831]],
[14832,14831,["l",2,29663]],[14835,14834,["l",2,29669]],
[14836,14835,["l",2,29671]],[14842,14841,["l",2,29683]],
[14843,7422,["l",2,14843]],[14851,7426,["l",2,14851]],
[14859,14858,["l",2,29717]],[14862,14861,["l",2,29723]],
[14867,7434,["l",2,14867]],[14869,7435,["l",2,14869]],
[14871,14870,["l",2,29741]],[14877,14876,["l",2,29753]],
[14879,7440,["l",2,14879]],[14880,14879,["l",2,29759]],
[14881,14880,["l",2,29761]],[14887,7444,["l",2,14887]],
[14891,7446,["l",2,14891]],[14895,14894,["l",2,29789]],
[14896,14895,["l",2,29791]],[14897,7449,["l",2,14897]],
[14902,14901,["l",2,29803]],[14910,14909,["l",2,29819]],
[14911,14840,["l",3,211]],[14917,14916,["l",2,29833]],
[14919,14918,["l",2,29837]],[14923,7462,["l",2,14923]],
[14926,14925,["l",2,29851]],[14929,7465,["l",2,14929]],
[14932,14931,["l",2,29863]],[14934,14933,["l",2,29867]],
[14937,14936,["l",2,29873]],[14939,7470,["l",2,14939]],
[14940,14939,["l",2,29879]],[14941,14940,["l",2,29881]],
[14947,7474,["l",2,14947]],[14951,7476,["l",2,14951]],
[14957,7479,["l",2,14957]],[14959,14958,["l",2,29917]],
[14961,14960,["l",2,29921]],[14964,14963,["l",2,29927]],
[14965,14964,["l",2,29929]],[14965,14964,["s",4,173]],
[14969,7485,["l",2,14969]],[14974,14973,["l",2,29947]],
[14980,14979,["l",2,29959]],[14983,7492,["l",2,14983]],
[14992,14991,["l",2,29983]],[14995,14994,["l",2,29989]]];


#checks whether the orbit of <vec> under g is not longer than bound
RECOG.shortorbit:=function(vec,g,bound)
local short, v, i, pos;

v:=StructuralCopy(vec);
short:=false;
i:=0;
pos:=First([1..Length(vec)],x->vec[x]<>0*vec[1]);
repeat 
  i:=i+1;
  v:=v*g;
  if v=(v[pos]/vec[pos])*vec then
     short:=true;
  fi;
until short or i=bound;

return i;

end;


RECOG.findchar:=function(ri,G,randelfunc)
  # randelfunc must be a function taking ri as one argument and returning
  # uniformly distributed random elements in G together with its
  # projective order (as for example below), or fail.
local mat,vs,vec,bound,count,m1,m2,m3,g,order,list,last,r,p,d,pr;

if randelfunc = fail then
    pr := ProductReplacer(GeneratorsOfGroup(G));
    randelfunc := function(ri)
      local el;
      el := Next(pr);
      return rec( el := el, order := ProjectiveOrder(el)[1] );
    end;
fi;

p := Characteristic(ri!.field);
d := ri!.dimension;
mat:=One(G);
vs:=VectorSpace(GF(p),mat);
repeat
  vec:=Random(vs);
until not(IsZero(vec));

if RECOG.shortorbit(vec,Product(GeneratorsOfGroup(G)), 3*d) = 3*d then 
   return p;
fi;

#find three largest element orders 
bound:=32*(LogInt(d,2))^2*6*4;
count:=0;
m1:=0;
m2:=0;
m3:=0;
last:=0;
repeat
  count:=count+1;
  r := randelfunc(ri);
  g := r.el;
  order:=r.order;
  if order >= 3*d then 
      return p;
  elif order > m1 then
      m3:=m2;
      m2:=m1;
      m1:=order;
      last:=count;
  elif order<m1 and order>m2 then 
      m3:=m2;
      m2:=order;
      last:=count;
  elif order<m2 and order>m3 then
      m3:=order;
      last:=count;
  fi;
until count=bound or count>=2*last+50;

#handle ambiguous cases
if [m1,m2,m3] = [13,7,5] then 
  return [[13,7, ["2B2",8]]];
elif [m1,m2] = [13,8] then
  return [[13,8, ["l",3,3]]];
elif [m1,m2,m3] = [13,7,6] then
  return [[13,7, ["l",2,13]]];
elif [m1,m2,m3] = [13,12,6] then
  return [[13,12,["l",2,5]]];
elif [m1,m2,m3] = [13,12,9] then 
  return [[13,12,["G2",3]]];
elif [m1,m2,m3] = [12,9,6] then 
  return [[12,9,["u",4,2]]];
elif [m1,m2,m3] = [12,9,8] then 
  return [[12,9,["u",4,3]]];
elif [m1,m2] = [5,3] then
  return [[ 5,3,["l",2,4]]];
elif [m1,m2] = [5,4] then
  return [[5,4,["l",2,9]]];
elif [m1,m2] = [7,4] then
  return [[7,4,["l",2,7]]];
elif [m1,m2] = [15,13] then
  return [[15,13,["u",3,4]]];
elif [m1,m2] = [30,20] then
  return [[30,20,["s",4,5]]];
elif [m1,m2] = [30,24] then
  return [[30,24,["s",8,2]]];
elif [m1,m2] = [63,60] then 
  return [[63,60,["u",4,5]]];
elif [m1,m2] = [91,85] then
  return [[91,85,["l",3,16]]];
fi;

list:=Filtered(RECOG.grouplist, x->x[1]=m1 and x[2]=m2);
#one more ambiguous case
if  Length(list) >=2 and (
    (list[1][3]{[1,2]}=["l",2] and list[2][3][1]="G2") or 
    (list[2][3]{[1,2]}=["l",2] and list[1][3][1]="G2")) then
   if m3>m1/2 then
      return Filtered(list,x->x[3][1]="G2");
   else 
      return Filtered(list,x->x[3][1]="l");
   fi;
else
   return list;
fi;

end;


RECOG.MakePSL2Hint := function( name, G )
  local d,defchar,f,p,q;
  f := DefaultFieldOfMatrixGroup(G);
  q := Size(f);
  p := Characteristic(f);
  d := DimensionOfMatrixGroup(G);
  defchar := Factors(name[3])[1];
  if p = defchar then return fail; fi;
  Info(InfoRecog,2,"Making hint for group ",name,"...");
  # we are in cross characteristic.
  # to be made better...
  return rec( elordersstart := [defchar], numberrandgens := 1, tries := 10,
              triesforgens := 3*(name[3]+1), 
              orblenlimit := 3*(name[3]+1) );
end;

RECOG.simplesocle := function(ri,g)
  local x,y,comm,comm2,comm3,gensH;

  repeat
    x:=RandomElm(ri,"simplesocle",true).el;
  until not ri!.isone(x);

  repeat
    y:=RandomElm(ri,"simplesocle",true).el;
    comm:=Comm(x,y);
  until not ri!.isone(comm);

  repeat
    y:=RandomElm(ri,"simplesocle",true).el;
    comm2:=Comm(comm,comm^y);
  until not ri!.isone(comm2);

  repeat
    y:=RandomElm(ri,"simplesocle",true).el;
    comm3:=Comm(comm2,comm2^y);
  until not ri!.isone(comm3);

  gensH:=FastNormalClosure(GeneratorsOfGroup(g),[comm3],20);

  return gensH;
end;

FindHomMethodsProjective.ComputeSimpleSocle := function(ri,G)
  # This simply computes the simple socle, stores it and returns false
  # such that it is never called again for this node.
  local x;
  RECOG.SetPseudoRandomStamp(G,"ComputeSimpleSocle");
  ri!.simplesocle := Group(RECOG.simplesocle(ri,G));
  ri!.simplesoclepr := ProductReplacer(ri!.simplesocle);
  ri!.simplesoclerand := EmptyPlist(100);
  Append(ri!.simplesoclerand,GeneratorsOfGroup(ri!.simplesocle));
  ri!.simplesoclerando := EmptyPlist(100);
  for x in ri!.simplesoclerand do
      Add(ri!.simplesoclerando,ProjectiveOrder(x)[1]);
  od;
  ri!.simplesoclerandp := 0;
  ri!.simplesocle!.pseudorandomfunc := 
       [rec( func := Next, args := [ri!.simplesoclepr] )];
  return false;
end;

RECOG.RandElFuncSimpleSocle := function(ri)
  local el,ord;
  ri!.simplesoclerandp := ri!.simplesoclerandp + 1;
  if not(IsBound(ri!.simplesoclerand[ri!.simplesoclerandp])) then
      el := Next(ri!.simplesoclepr);
      ri!.simplesoclerand[ri!.simplesoclerandp] := el;
      ord := ProjectiveOrder(el)[1];
      ri!.simplesoclerando[ri!.simplesoclerandp] := ord;
  else
      el := ri!.simplesoclerand[ri!.simplesoclerandp];
      ord := ri!.simplesoclerando[ri!.simplesoclerandp];
  fi;
  return rec( el := el, order := ord );
end;

FindHomMethodsProjective.ThreeLargeElOrders := function(ri,G)
  local hint,name,namecat,p,res;
  RECOG.SetPseudoRandomStamp(G,"ThreeLargeElOrders");
  ri!.simplesoclerandp := 0;
  p := RECOG.findchar(ri,ri!.simplesocle,RECOG.RandElFuncSimpleSocle);
  if p = Characteristic(ri!.field) then
      Info(InfoRecog,2,"ThreeLargeElOrders: defining characteristic p=",p);
      return false;
  fi;
  # Try all possibilities:
  Info(InfoRecog,2,"ThreeLargeElOrders: found ",p);
  for hint in p do
      Info(InfoRecog,2,"Trying ",hint);
      name := hint[3];
      if name[1] = "l" then  # Handle PSL specially
          if name[2] = 2 then
              hint := RECOG.MakePSL2Hint(name,G);
              if hint <> fail then
                  res := DoHintedLowIndex(ri,G,hint);
              else   # we use Pete Brooksbank's methods
                  return SLCR.FindHom(ri,G,2,name[3]);
              fi;
          else
              return SLCR.FindHom(ri,G,name[2],name[3]);
          fi;
      else
          if Length(name) = 3 then
              namecat := Concatenation(UppercaseString(name[1]),
                                       String(name[2]),
                                       "(",String(name[3]),")");
          else
              namecat := name[1];
          fi;
          res := LookupHintForSimple(ri,G,namecat);
      fi;
      if res = true then return true; fi;
  od;
  Info(InfoRecog,2,"Did not succeed with hints, giving up...");
  return fail;
end;

RECOG.DegreeAlternating := function (orders)
    local   degs,  prims,  m,  f,  n;
    degs := []; 
    prims := [];
    for m in orders do 
        if m > 1 then
            f := Collected(Factors(m));
            Sort(f);
            n := Sum(f, x->x[1]^x[2]);
            if f[1][1] = 2 then n := n+2; fi;
            AddSet(degs,n);
            UniteSet(prims,Set(f,x->x[1]));
        fi; 
    od;
    return [degs, prims];
end;    #  DegreeAlternating

RECOG.RecognizeAlternating := function (orders)
    local   tmp,  degs,  prims,  mindeg,  p1,  p2,  i;
   tmp := RECOG.DegreeAlternating (orders);
   degs := tmp[1];
   prims := tmp[2];
   if Length(degs) = 0 then 
       return "Unknown"; 
   fi;
   mindeg := Maximum (degs);  # minimal possible degree
   
   p1 := PrevPrimeInt (mindeg + 1);
   p2 := PrevPrimeInt (p1);
   if not p1 in prims or not p2 in prims then
       return 0;
   fi;
   if mindeg mod 2 = 1 then
       if not (mindeg in orders and  mindeg - 2 in orders) then 
           return 0;
       fi;
   else
       if not mindeg - 1 in orders then 
           return 0;
       fi;
   fi;
  
   for i in [3..Minimum (QuoInt(mindeg,2) - 1, 6)] do
       if IsPrime (i) and IsPrime (mindeg - i) then
           if not i * (mindeg - i) in orders then
               return 0;
           fi;
       elif IsPrime (i) and IsPrime (mindeg - i -1) then
           if not i * (mindeg - i - 1) in orders then
               return 0;
           fi;
       fi;
   od;
   return  mindeg;
end;   # RecognizeAlternating

SLPforElementFuncsProjective.Alternating := function(ri,x)
  local y,slp;
  RecSnAnIsOne := IsOneProjective;
  RecSnAnEq := IsEqualProjective;
  y := FindImageAn(ri!.recogSnAnDeg,x,
                   ri!.recogSnAnRec[2][1], ri!.recogSnAnRec[2][2],
                   ri!.recogSnAnRec[3][1], ri!.recogSnAnRec[3][2]);
  RecSnAnIsOne := IsOne;
  RecSnAnEq := EQ;
  if y = fail then return fail; fi;
  slp := SLPforAn(ri!.recogSnAnDeg,y);
  return slp;
end;

SLPforElementFuncsProjective.Symmetric := function(ri,x)
  local y,slp;
  RecSnAnIsOne := IsOneProjective;
  RecSnAnEq := IsEqualProjective;
  y := FindImageSn(ri!.recogSnAnDeg,x,
                   ri!.recogSnAnRec[2][1], ri!.recogSnAnRec[2][2],
                   ri!.recogSnAnRec[3][1], ri!.recogSnAnRec[3][2]);
  RecSnAnIsOne := IsOne;
  RecSnAnEq := EQ;
  if y = fail then return fail; fi;
  slp := SLPforSn(ri!.recogSnAnDeg,y);
  return slp;
end;

FindHomMethodsProjective.AlternatingBBByOrders := function(ri,G)
  local Gm,RecSnAnEq,RecSnAnIsOne,deg,limit,ordersseen,r;
  if IsBound(ri!.projordersseen) then
      ordersseen := ri!.projordersseen;
  else
      ordersseen := [];
  fi;
  limit := QuoInt(3*ri!.dimension,2);
  while Length(ordersseen) <= limit do
      Add(ordersseen,RECOG.ProjectiveOrder(PseudoRandom(G)));
      if Length(ordersseen) mod 20 = 0 or
         Length(ordersseen) = limit then
          deg := RECOG.RecognizeAlternating(ordersseen);
          Info(InfoRecog,2,ordersseen);
          if deg > 0 then  # we strongly suspect Alt(deg):
              # Switch blackbox recognition to projective:
              Info(InfoRecog,2,"Suspect alternating or symmetric group of ",
                   "degree ",deg,"...");
              RecSnAnIsOne := IsOneProjective;
              RecSnAnEq := IsEqualProjective;
              Gm := GroupWithMemory(G);
              r := RecogniseSnAn(deg,Gm,1/100);
              RecSnAnIsOne := IsOne;
              RecSnAnEq := EQ;
              if r = fail or r[1] <> "An" then 
                  Info(InfoRecog,2,"AltByOrders: Did not find generators.");
                  continue; 
              fi;
              Info(InfoRecog,2,"Found Alt(",deg,")!");
              ri!.recogSnAnRec := r;
              ri!.recogSnAnDeg := deg;
              SetSize(ri,Factorial(deg)/2);
              Setslpforelement(ri,SLPforElementFuncsProjective.Alternating);
              Setslptonice(ri,SLPOfElms(Reversed(r[2])));
              ForgetMemory(r[2]);
              ForgetMemory(r[3][1]);
              SetFilterObj(ri,IsLeaf);
              return true;
          fi;
      fi;
  od;
  return fail;
end;

RECOG.HomFDPM := function(data,x)
  local r;
  r := RECOG.FindPermutation(data.cob*x*data.cobi,data.fdpm);
  if r = fail then return fail; fi;
  return r[2];
end;

FindHomMethodsProjective.AltSymBBByDegree := function(ri,G)
  local GG,Gm,RecSnAnEq,RecSnAnIsOne,d,deg,f,fact,hom,newgens,o,orders,p,primes,
        r,totry;
  RECOG.SetPseudoRandomStamp(G,"AltSymBBByDegree");
  d := ri!.dimension;
  orders := RandomOrdersSeen(ri);
  if Length(orders) = 0 then
      orders := [RandomElmOrd(ri,"AltSym",false).order];
  fi;
  primes := Filtered(Primes,x->x <= d+2);
  for o in orders do
      fact := FactorsTD(o,primes);
      if Length(fact[2]) <> 0 then
          Info(InfoRecog,2,"AltSym: prime factor of order excludes A_n");
          return false;
      fi;
  od;
  f := ri!.field;
  # We first try the deleted permutation module method:
  if d >= 6 then
      Info(InfoRecog,3,"Trying deleted permutation module method...");
      r := RECOG.RecogniseFDPM(G,f,1/10);
      if r <> fail and IsRecord(r) then
          # Now make a homomorphism object:
          newgens := List(GeneratorsOfGroup(G),
                          x->RECOG.HomFDPM(r,x));
          if not(fail in newgens) then
              GG := GroupWithGenerators(newgens);
              hom := GroupHomByFuncWithData(G,GG,RECOG.HomFDPM,r);

              Sethomom(ri,hom);
              Setmethodsforfactor(ri,FindHomDbPerm);

              ri!.comment := "_FDPM";
              return true;
          fi;
      fi;
      Info(InfoRecog,3,"Deleted permutation module method failed.");
  fi;
  p := Characteristic(f);
  totry := EmptyPlist(2);
  if (d+1) mod p <> 0 and d+1 > 10 then
      Add(totry,d+1);
  fi;
  if (d+2) mod p = 0 and d+2 > 10 then
      Add(totry,d+2);
  fi;
  return fail;    # do not try any more now
  for deg in totry do
      Info(InfoRecog,3,"Looking for Alt/Sym(",deg,")...");
      RecSnAnIsOne := IsOneProjective;
      RecSnAnEq := IsEqualProjective;
      Gm := GroupWithMemory(G);
      r := RecogniseSnAn(deg,Gm,1/100);
      RecSnAnIsOne := IsOne;
      RecSnAnEq := EQ;
      if r = fail then 
          Info(InfoRecog,2,"AltSym: deg=",deg,": did not find generators.");
          continue; 
      fi;
      if r[1] = "An" then
          Info(InfoRecog,2,"Found Alt(",deg,")!");
          ri!.recogSnAnRec := r;
          ri!.recogSnAnDeg := deg;
          SetSize(ri,Factorial(deg)/2);
          Setslpforelement(ri,SLPforElementFuncsProjective.Alternating);
          Setslptonice(ri,SLPOfElms(Reversed(r[2])));
          ForgetMemory(r[2]);
          ForgetMemory(r[3][1]);
          SetFilterObj(ri,IsLeaf);
          ri!.comment := "_Alt";
          return true;
      else   # r[1] = "Sn" 
          Info(InfoRecog,2,"Found Sym(",deg,")!");
          ri!.recogSnAnRec := r;
          ri!.recogSnAnDeg := deg;
          SetSize(ri,Factorial(deg));
          Setslpforelement(ri,SLPforElementFuncsProjective.Symmetric);
          Setslptonice(ri,SLPOfElms(Reversed(r[2])));
          ForgetMemory(r[2]);
          ForgetMemory(r[3][1]);
          SetFilterObj(ri,IsLeaf);
          ri!.comment := "_Sym";
          return true;
      fi;
  od;
  return fail;
end;

# Looking at element orders to determine which sporadic it could be:

RECOG.SporadicsElementOrders :=
[ [ 1,2,3,5,6,7,10,11,15,19 ],[ 1,2,3,4,5,6,8,11 ],
  [ 1,2,3,4,5,6,8,10,11 ],
  [ 1,2,3,4,5,6,8,9,10,12,15,17,19 ],
  [ 1,2,3,4,5,6,7,8,11,14,15,23 ],[ 1,2,3,4,5,6,7,8,11 ],
  [ 1,2,3,4,5,6,7,8,10,12,15 ],
  [ 1,2,3,4,5,6,7,8,10,12,14,15,17,21,28 ],
  [ 1,2,3,4,5,6,7,8,10,12,13,14,15,16,20,24,26,29 ],
  [ 1,2,3,4,5,6,7,8,10,11,12,15,20 ],
  [ 1,2,3,4,5,6,7,8,10,11,12,14,15,21,23 ],
  [ 1,2,3,4,5,6,7,8,10,11,12,14,15,16,20,21,22,23,24,28,
      29,30,31,33,35,37,40,42,43,44,66 ],
  [ 1,2,3,4,5,6,7,8,10,11,12,14,15,16,19,20,28,31 ],
  [ 1,2,3,4,5,6,7,8,9,10,12,13,14,15,18,19,20,21,24,27,
      28,30,31,36,39 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,14,15,30 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,14,15,19,20,21,22,25,30, 35,40 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,14,15,18,20,21,22,24,25,
      28,30,31,33,37,40,42,67 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,14,15,18,20,21,22,23,24,30 
     ],[ 1,2,3,4,5,6,7,8,9,10,11,12,14,15,16,18,20,23,24,28,30 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,18,20,21,24 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,18,20,21,22,24,30 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,18,20,21,22,
      23,24,26,28,30,33,35,36,39,40,42,60 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,20,21,
      22,23,24,26,27,28,30,35,36,39,42,60 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,20,21,
      22,23,24,26,27,28,29,30,33,35,36,39,42,45,60 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,
      21,22,23,24,25,26,27,28,30,31,32,33,34,35,36,38,39,40,
      42,44,46,47,48,52,55,56,60,66,70 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,
      21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,38,39,
      40,41,42,44,45,46,47,48,50,51,52,54,55,56,57,59,60,62,
      66,68,69,70,71,78,84,87,88,92,93,94,95,104,105,110,119 ]
    ,[ 1,2,3,4,5,6,8,10,11,12 ],
  [ 1,2,3,4,5,6,7,8,10,11,12,14 ],
  [ 1,2,3,4,5,6,7,8,10,11,12,14,15,20,30 ],
  [ 1,2,3,4,5,6,7,8,10,12,14,15,24 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,14,15,20,22,24,30 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,18,20,21,22,24,28,30,40 ],
  [ 1,2,3,4,5,6,7,8,10,12,14,15,16,17,20,21,24,28,30,42 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,14,15,18,19,20,21,22,24,
      25,28,30,35,40,42,44,60 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,18,20,21,22,24,30,36,42 ],
  [ 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,20,21,
      22,23,24,26,27,28,29,30,33,34,35,36,39,40,42,45,46,54,60,66,70,78,84 ],
  [ 1,2,3,4,5,6,7,8,10,11,12,14,15,16,19,20,22,24,28,30,
      31,38,56 ],[ 1,2,3,4,5,6,8,9,10,12,15,17,18,19,24,34 ]
    ,[ 1,2,3,4,5,6,8,10,12,13,16 ],
  [ 1,2,3,4,5,6,8,10,12,13,16,20 ] ];
RECOG.SporadicsProbabilities :=
[ [ 1/175560,1/120,1/30,1/15,1/6,1/7,1/5,1/11,2/15,3/19 ],
  [ 1/7920,1/48,1/18,1/8,1/5,1/6,1/4,2/11 ],
  [ 1/95040,3/320,5/108,1/16,1/10,1/4,1/4,1/10,2/11 ],
  [ 1/50232960,1/1920,49/9720,1/96,1/15,1/24,1/8,1/9,1/5,1/12,2/15,
      2/17,2/19 ],
  [ 1/10200960,1/2688,1/180,1/32,1/15,1/12,1/7,1/8,2/11,1/7,2/15,
      2/23 ],[ 1/443520,1/384,1/36,3/32,1/5,1/12,2/7,1/8,2/11 ],
  [ 1/604800,3/640,31/1080,1/96,7/150,1/8,1/7,1/8,3/10,1/12,2/15 ],
  [ 1/4030387200,17/322560,2/945,1/84,1/300,1/18,95/4116,1/16,1/20,
      1/6,5/28,1/15,2/17,4/21,1/14 ],
  [ 1/145926144000,283/22364160,1/2160,17/5120,13/3000,1/48,1/28,
      11/192,3/40,1/8,1/52,3/28,1/15,1/8,3/20,1/12,3/52,2/29 ],
  [ 1/44352000,11/23040,1/360,19/960,17/375,5/72,1/7,3/16,1/10,2/11,
      1/12,1/15,1/10 ],
  [ 1/244823040,19/107520,11/3780,1/48,1/60,1/12,1/21,1/16,1/20,
      1/11,1/6,1/7,2/15,2/21,2/23 ],
  [ 1/86775571046077562880,13/21799895040,1/2661120,53/1576960,1/6720,
      2311/2661120,1/420,31/7680,13/960,133/31944,1/32,5/84,1/30,
      1/32,1/80,1/21,13/264,1/23,1/24,1/14,1/29,1/30,3/31,1/33,
      2/35,3/37,1/20,1/21,3/43,1/44,1/33 ],
  [ 1/460815505920,1/161280,1/3240,79/20160,1/180,1/72,29/1372,1/16,
      1/20,1/11,1/36,1/28,2/45,1/4,3/19,1/10,1/14,2/31 ],
  [ 1/90745943887872000,1/92897280,13603/1719506880,257/1935360,1/3000,
      67/25920,1/1176,5/384,5/648,1/120,25/432,1/39,1/56,1/15,5/72,
      1/19,1/20,1/21,1/6,1/9,1/28,1/15,2/31,1/12,2/39 ],
  [ 1/898128000,1/40320,31/29160,1/96,31/750,11/360,1/7,1/8,2/27,
      1/30,2/11,1/12,1/7,1/15,1/15 ],
  [ 1/273030912000000,131/473088000,59/1632960,23/46080,16913/31500000,
      1/192,1/420,9/320,1/27,431/12000,1/22,17/144,1/28,13/180,2/19,
      3/20,1/21,1/22,2/25,1/12,2/35,1/20 ],
  [ 1/51765179004000000,1/39916800,15401/2694384000,1/20160,601/2250000,
      1291/362880,1/168,1/80,1/54,73/3600,1/33,5/288,1/168,28/1125,
      1/18,1/40,1/21,1/11,1/8,1/25,1/28,1/45,5/31,2/33,2/37,1/20,
      1/21,3/67 ],
  [ 1/495766656000,179/31933440,631/2449440,1/1440,1/250,373/12960,
      1/42,1/24,1/54,1/15,1/11,1/18,1/14,1/10,1/18,1/10,1/21,1/11,
      2/23,1/12,1/30 ],
  [ 1/42305421312000,523/743178240,1/116640,139/120960,1/500,79/12960,
      1/56,5/192,1/54,1/20,1/11,2/27,5/56,1/10,1/16,1/18,1/10,
      2/23,1/12,1/28,1/10 ],
  [ 1/448345497600,151/23224320,661/1959552,103/23040,7/1800,187/10368,
      1/84,5/96,1/27,3/40,1/11,31/288,2/13,1/28,1/9,1/9,1/20,2/21,
      1/24 ],
  [ 1/64561751654400,4297/7357464576,11419/176359680,181/276480,1/600,
      9121/933120,1/42,17/384,5/108,1/24,1/11,79/864,2/13,1/14,1/30,
      1/16,7/108,1/20,1/21,1/11,1/24,1/30 ],
  [ 1/4157776806543360000,39239/12752938598400,7802083/4035109478400,
      1061/11612160,1433/15120000,198391/69672960,2/2205,79/23040,1/216,
      109/9600,1/66,10949/207360,1/156,1/42,277/5400,1/32,1/24,
      37/480,17/252,1/22,2/23,25/288,1/52,1/14,13/120,1/33,1/35,
      1/36,2/39,1/40,1/84,1/60 ],
  [ 1/4089470473293004800,407161/129123503308800,161281/148565394432,
      239/5806080,1/25200,1036823/705438720,1/840,1/128,127/17496,
      11/1200,1/44,529/12960,1/39,5/168,1/72,1/16,1/17,13/216,1/30,
      1/42,3/44,2/23,1/16,1/13,1/27,1/28,7/120,1/35,1/18,2/39,
      1/42,1/60 ],
  [ 1/1255205709190661721292800,6439/1032988026470400,144613199/
        4412392214630400,25/6967296,1/907200,159797/564350976,67/123480,
      11/4608,1189/1049760,7/4800,1/132,4741/311040,1/234,5/168,
      103/16200,1/32,1/17,11/288,1/48,17/252,1/44,2/23,7/72,1/26,
      1/27,1/28,2/29,1/24,2/33,1/35,1/24,4/117,5/84,2/45,1/60 ],
  [ 1/4154781481226426191177580544000000,
      34727139371/281639525236291462496256000,160187/10459003768012800,
      56445211/3060705263616000,1873/11088000000,7216687/1418939596800,
      1/564480,18983/123863040,5/34992,667/2688000,1/1320,12629/3732480,
      1/312,871/564480,31/3600,1/96,1/68,7/432,1/38,323/12000,1/252,
      5/264,1/23,19/432,1/25,3/104,1/27,5/224,67/1200,2/31,1/32,
      1/66,3/68,1/70,5/108,1/38,1/39,1/20,1/36,1/44,1/23,2/47,
      1/48,1/52,1/55,1/56,1/30,1/66,1/70 ],
  [ 1/808017424794512875886459904961710757005754368000000000,
      952987291/132953007399245638117682577408000000,
      1309301528411/299423045898886400305790976000,
      228177889/1608412858851262464000,361177/34128864000000000,
      352968797/83672030144102400,16369/1382422809600,80467/177124147200,
      7/18895680,1270627/532224000000,1/1045440,20669/313528320,
      31/949104,9/250880,8611/40824000,1/3072,1/2856,91/139968,1/1140,
      2323/1152000,907/370440,3/3520,1/276,167/13824,1/250,1/208,
      1/162,3/392,1/87,529/43200,1/93,1/64,5/1188,1/136,31/2100,
      1/48,1/76,25/702,49/1600,1/41,1/56,1/176,1/135,3/92,1/47,
      1/96,1/50,1/51,3/104,1/54,1/110,5/112,1/57,2/59,41/720,1/31,
      1/44,1/68,2/69,3/140,2/71,1/26,1/28,2/87,1/44,1/46,2/93,
      1/47,2/95,1/52,1/105,1/110,2/119 ],
  [ 1/190080,17/1920,5/216,3/32,1/20,5/24,1/8,3/20,1/11,1/4 ],
  [ 1/887040,29/8960,1/72,7/96,1/10,1/8,1/7,1/8,1/10,1/11,1/12,1/7 
     ],[ 1/88704000,11/21504,1/720,7/240,17/750,17/240,1/14,1/8,1/6,
      1/11,1/12,1/14,1/30,1/5,1/30 ],
  [ 1/1209600,103/26880,31/2160,11/192,7/300,7/48,1/14,5/48,3/20,
      5/24,1/14,1/15,1/12 ],
  [ 1/1796256000,67/887040,31/58320,17/2880,31/1500,31/720,1/14,5/48,
      1/27,7/60,1/11,7/72,1/14,1/30,1/10,1/11,1/12,1/30 ],
  [ 1/896690995200,16081/2554675200,661/3919104,1031/322560,7/3600,
      2879/103680,1/168,53/1440,1/54,89/1200,1/22,65/576,1/13,3/56,
      1/18,1/16,1/18,1/40,1/21,1/22,19/144,1/28,1/30,1/20 ],
  [ 1/8060774400,23/387072,1/945,9/1120,1/600,473/7560,95/8232,7/96,
      1/24,1/8,19/168,1/30,1/8,1/17,1/20,2/21,1/12,1/28,1/30,1/21 ]
    ,[ 1/546061824000000,7057/25546752000,59/3265920,119351/177408000,
      16913/63000000,2497/362880,1/840,21/640,1/54,691/24000,1/44,
      101/1440,5/168,13/360,1/18,1/19,743/6000,1/42,1/44,1/8,1/25,
      1/28,7/120,1/35,1/10,1/42,1/22,1/60 ],
  [ 1/129123503308800,10781/17517772800,11419/352719360,329/414720,
      1/1200,46757/4354560,1/84,1/32,5/216,17/400,1/22,295/2592,1/13,
      1/12,1/60,1/16,29/216,1/20,1/42,1/22,1/8,1/20,1/36,1/42 ],
  [ 1/2510411418381323442585600,352149857/65431527572688076800,
      144613199/8824784429260800,12091/4180377600,1/1814400,
      20115929623/65368773550080,67/246960,13/7680,1189/2099520,97/67200,
      1/264,282547/13063680,1/468,31/1680,103/32400,1/32,1/34,
      4153/139968,41/2400,17/504,7/264,1/23,7/96,5/156,1/54,2/21,
      1/29,11/240,1/33,1/34,1/70,31/432,2/117,1/40,11/168,1/45,
      1/23,1/54,1/60,1/33,1/70,1/39,1/84 ],
  [ 1/921631011840,401/67415040,1/6480,79/40320,1/360,17/720,29/2744,
      43/672,7/120,1/22,1/72,5/56,1/45,1/8,3/38,1/20,1/22,1/12,
      1/28,1/15,1/31,3/38,1/14 ],
  [ 1/100465920,91/195840,49/19440,1/64,1/30,11/144,5/48,1/18,1/10,
      1/8,1/15,1/17,1/6,1/19,1/12,1/17 ],
  [ 1/17971200,23/30720,1/108,11/384,1/50,1/12,3/16,1/10,1/6,2/13,
      1/4 ],[ 1/35942400,23/61440,1/216,37/1280,1/100,1/24,3/16,1/20,
      1/4,1/13,1/4,1/10 ] ];
RECOG.SporadicsNames :=
[ "J1","M11","M12","J3","M23","M22","J2","He","Ru","HS","M24",
  "J4","ON","Th","McL","HN","Ly","Co3","Co2","Suz","Fi22","Co1",
  "Fi23","Fi24'","B","M","M12.2","M22.2","HS.2","J2.2","McL.2","Suz.2",
  "He.2","HN.2","Fi22.2","Fi24'.2","ON.2","J3.2","2F4(2)'","2F4(2)'.2"];
RECOG.SporadicsSizes :=
[ 175560,7920,95040,50232960,10200960,443520,604800,4030387200,
  145926144000,44352000,244823040,86775571046077562880,460815505920,
  90745943887872000,898128000,273030912000000,51765179004000000,
  495766656000,42305421312000,448345497600,64561751654400,
  4157776806543360000,4089470473293004800,1255205709190661721292800,
  4154781481226426191177580544000000,
  808017424794512875886459904961710757005754368000000000,190080,887040,
  88704000,1209600,1796256000,896690995200,8060774400,546061824000000,
  129123503308800,2510411418381323442585600,921631011840,100465920,
  17971200,35942400 ];
RECOG.SporadicsKillers :=
[ [[ 5,7 ]],[[ 5,7 ]],[[ 6,7 ]],[[ 11,9 ]],[[ 10,9 ]],[[ 5,7 ]],[[ 7,9 ]],
  [[ 11,14 ]],[[ 14,15 ]],[[ 10,8 ]],[[ 12,11 ]],[[ 29,20,26,23 ]],
  [[ 15,14 ]],[[ 20,19 ]],[[ 13,11 ]],[[ 12,16 ]],[[ 19,23 ]],[[ 11,14,16 ]],
  [[ 17,14,21 ]],[[ 15,13 ]],[ [ 18 .. 22 ] ],
  [ [ 26 .. 32 ],[ 25 .. 32 ] ],[ [ 28 .. 32 ],[ 27 .. 32 ] ],
  [ [ 27 .. 35 ],[ 29 .. 35 ],[ 27,29,34 ] ],  # the latter is for Fi23
  [ [ 31 .. 49 ],[ 40,41,42,43,44,45,46,48,49 ] ], # the latter is agains Fi23
  [ [ 32 .. 73 ],[ 61 .. 73 ] ],[[ 6,10 ]],[[ 7,12 ]],[[ 9,14 ]],[[ 9,10 ]],
  [[ 15,8,10 ]],[[ 13,12,21 ]],[[ 11,13,10 ]],[[ 25,17,20 ]],
  [[ 21,17 ],[23,24]],   # the latter is to distinguish Fi22.2 and Fi22
  [[ 35,32,23,26 ],[ 36,37,38,40,41,42,43 ]], # the latter is for Fi23
  [[ 18,12,14 ]],[[ 10,13 ]],[[ 7,11 ]],[[ 9,11 ]] ];
RECOG.SporadicsWorkers := [];
# Removed to avoid dependency on unpublished package gensift:
#RECOG.SporadicsWorkers[2] := SporadicsWorkerGenSift;   # M11
# and same for: M12, M22, J2, HS, Ly, Co3, Co2

RECOG.MakeSporadicsInfo := function(name)
  local ct,i,index,killers,o,orders,p,pos,prob,probs,probscopy,sum;
  ct := CharacterTable(name);
  orders := Set(OrdersClassRepresentatives(ct));
  probs := [];
  for o in orders do
      prob := 0;
      pos := Positions(OrdersClassRepresentatives(ct),o);
      for p in pos do
          prob := prob + 1/SizesCentralizers(ct)[p];
      od;
      Add(probs,prob);
  od;
  index := [1..Length(orders)];
  probscopy := ShallowCopy(probs);
  SortParallel(probscopy,index);
  sum := probscopy[Length(orders)];
  i := Length(orders);
  repeat
      i := i - 1;
      sum := sum + probscopy[i];
  until sum > 1/4;
  killers := index{[i..Length(orders)]};
  return rec( size := Size(ct), orders := orders,
              probabilities := probs, killers := killers, name := name );
end;

RECOG.RuleOutSmallProjOrder := function(m)
  local l,o,v;
  if IsPerm(m) then
      o := Order(m);
      if o > 119 then return fail; fi;
      return o;
  fi;
  v := ShallowCopy(m[1]);
  Randomize(v);
  ORB_NormalizeVector(v);
  o := Orb([m],v,OnLines,rec( hashlen := 300, report := 0 ));
  Enumerate(o,121);
  if not(IsClosed(o)) then return fail; fi;
  l := Length(o);
  Randomize(v);
  ORB_NormalizeVector(v);
  o := Orb([m],v,OnLines,rec( hashlen := 300, report := 0 ));
  Enumerate(o,121);
  if not(IsClosed(o)) then return fail; fi;
  l := Lcm(l,Length(o));
  if l > 119 then return fail; fi;
  return l;
end;

FindHomMethodsProjective.SporadicsByOrders := function(ri,G)
  local count,gens,i,j,jj,k,killers,l,limit,o,ordersseen,pp,r,raus,res,x;

  RECOG.SetPseudoRandomStamp(G,"SporadicsByOrders");

  l := [1..Length(RECOG.SporadicsNames)];
  pp := 0*l;
  ordersseen := [];
  count := 0;
  gens := GeneratorsOfGroup(G);
  limit := 120+Length(gens);
  for i in [1..limit] do
      if i <= Length(gens) then
          r := rec( el := gens[i] );
      else
          r := RandomElm(ri,"SporadicsByOrders",false);
      fi;
      o := RECOG.RuleOutSmallProjOrder(r.el);
      if o = fail then
          Info(InfoRecog,2,"Ruled out all sporadic groups.");
          return false;
      fi;
      if i <= Length(gens) then
          if ri!.projective then
              r.order := ProjectiveOrder(r.el)[1];
          else
              r.order := Order(r.el);
          fi;
      else
          GetElmOrd(ri,r);
      fi;
      o := r.order;
      x := r.el;
      AddSet(ordersseen,o);
      Info(InfoRecog,3,"Found order: ",String(o,3)," (element #",i,")");
      l := Filtered(l,i->o in RECOG.SporadicsElementOrders[i]);
      if l = [] then
          Info(InfoRecog,2,"Ruled out all sporadic groups.");
          return false;
      fi;
      # Throw out improbable ones:
      j := 1;
      while j <= Length(l) do
          if Length(l) = 1 then
              limit := 1/1000;
          else
              limit := 1/400;
          fi;
          jj := l[j];
          raus := false;
          for k in [1..Length(RECOG.SporadicsElementOrders[jj])] do
              if not(RECOG.SporadicsElementOrders[jj][k] in ordersseen) and
                 (1-RECOG.SporadicsProbabilities[jj][k])^i < limit then
                  Info(InfoRecog,3,"Have thrown out ",RECOG.SporadicsNames[jj],
                       " (did not see order ",
                       RECOG.SporadicsElementOrders[jj][k],")");
                  raus := true;
                  break;
              fi;
          od;
          if not(raus) and IsBound(RECOG.SporadicsKillers[jj]) then
            for killers in RECOG.SporadicsKillers[jj] do
              if Intersection(ordersseen,
                              RECOG.SporadicsElementOrders[jj]{killers})=[]
                 and (1-Sum(RECOG.SporadicsProbabilities[jj]{killers}))^i 
                     < 10^-3 then
                  raus := true;
                  break;
                  Info(InfoRecog,3,"Have thrown out ",RECOG.SporadicsNames[jj],
                       " (did not see orders in ",
                       RECOG.SporadicsElementOrders[jj]{killers},")");
              fi;
            od;
          fi;
          if raus then
              Remove(l,j);
          else
              j := j + 1;
          fi;
      od;
      if l = [] then
          Info(InfoRecog,2,"Ruled out all sporadic groups.");
          return false;
      fi;
      if Length(l) = 1 then
        count := count + 1;
        if count >= 9 then
          Info(InfoRecog,2,"I guess that this is the sporadic simple group ",
               RECOG.SporadicsNames[l[1]],".");
          break;
        fi;
      fi;
      if Length(l) < 6 then
          Info(InfoRecog,2,"Possible sporadics left: ",
               RECOG.SporadicsNames{l}," i=",i);
      else
          Info(InfoRecog,2,"Possible sporadics left: ",Length(l)," i=",i);
      fi;
  od;
  if ValueOption("DEBUGRECOGSPORADICS") <> fail then
      return RECOG.SporadicsNames{l};
  fi;
  for i in [1..Length(l)] do
      Info(InfoRecog,2,"Trying hint for ",RECOG.SporadicsNames[l[i]],"...");
      res := LookupHintForSimple(ri,G,RECOG.SporadicsNames[l[i]]);
      if res = true then return res; fi;
      if IsBound(RECOG.SporadicsWorkers[l[i]]) then
          Info(InfoRecog,2,"Calling its installed worker...");
          res := RECOG.SporadicsWorkers[l[1]](RECOG.SporadicsNames[l[i]],
                                        RECOG.SporadicsSizes[l[i]],ri,G);
          if res = true then return res; fi;
      fi;
      Info(InfoRecog,2,"This did not work.");
  od;
  return false;
end;

RECOG.LieTypeOrderFunc := RECOG.ProjectiveOrder;
RECOG.LieTypeSampleSize := 250;
RECOG.LieTypeNmrTrials := 10;

RECOG.OMppdset := function(p, o)
    local   primes;
    primes := Set(Factors(o));
    RemoveSet(primes,p);
    return Set(primes, l->OrderMod(p,l));
end;

RECOG.VerifyOrders := function (type, n, q, orders)
    local   p,  allowed,  maxprime,  r,  rq,  ii, LargestPrimeOccurs;
    LargestPrimeOccurs := function(r, orders)
        local   maxp;
        maxp := Maximum(Factors(r));
        return ForAny(orders, i->i mod maxp = 0);
    end;
    p := Factors(q)[1];
    allowed := orders;  
    maxprime := true;
    if type = "L" then
        if n = 2 then
            if p = 2 then
                allowed := Set([2, q-1, q+1]);
            else
                allowed := Set([p, (q-1)/2, (q+1)/2]);
          fi;
      elif n = 3 then
          if (q-1) mod 3 <> 0 then
              allowed := Set([4, p* (q-1), q^2-1, q^2+q+1]);
          else
              allowed := Set([4, p* (q-1)/3, q-1, (q^2-1)/3, (q^2+q+1)/3]);
          fi;
      elif n = 4 then
          if p = 2 then
              allowed := Set([4* (q-1), p* (q^2-1), q^3-1, (q^2+1)* (q-1), 
                              (q^2+1)* (q+1)]);
          elif p = 3 then
              allowed := Set([9, p* (q^2-1), q^3-1, (q^2+1)* (q-1), 
                              (q^2+1)* (q+1)]);
          elif (q-1) mod 2 <> 0 then
              allowed := Set([p*(q^2-1),q^3-1,(q^2+1)* (q-1), (q^2+1)* (q+1)]);
          elif (q-1) mod 4 = 2 then
              allowed := Set([p* (q^2-1), (q^3-1)/2, (q^2+1)* (q-1)/2,
                              (q^2+1)* (q+1)/2 ]);
          else
              allowed := Set([p* (q^2-1), (q^3-1)/4, (q^2+1)* (q-1)/4,
                              (q^2+1)* (q+1)/4 ]);
          fi;
      elif n = 5 and q = 2 then
          allowed := Set([8, 12, 14, 15, 21, 31]);
      elif n = 6 and q = 3 then
          allowed := Set([36, 78, 80, 104, 120, 121, 182]);
          maxprime := 91 in orders or 121 in orders;
      else
          maxprime := LargestPrimeOccurs (q^n-1, orders)
                      and LargestPrimeOccurs (q^(n-1)-1, orders)
                      and Maximum (orders) <= (q^n-1)/ (q-1)/Gcd (n,q-1);
          if n = 8 and q = 2 then
              maxprime := maxprime and LargestPrimeOccurs (7, orders);
              #/Set([ i : i in orders | i mod 21 = 0]) <> Set([]);
          fi;
      fi;
  elif type = "U" then
      if n = 3 then
          if (q+1) mod 3 <> 0 then
              allowed := Set([4, p* (q+1), q^2-1, q^2-q+1]);
          else
              allowed := Set([4, p* (q+1)/3, q+1, (q^2-1)/3, (q^2-q+1)/3]);
          fi;
      elif n = 4 then
          if p = 2 then
              allowed := Set([8, 4* (q+1), p* (q^2-1), q^3+1, (q^2+1)* (q-1), 
                              (q^2+1)* (q+1)]);
          elif p = 3 then
              allowed := Set([9, p* (q^2-1), q^3+1, (q^2+1)* (q-1), 
                              (q^2+1)* (q+1)]);
              if q = 3 then
                  maxprime := 8 in orders and 9 in orders;
              fi;
          elif (q+1) mod 2 <> 0 then
              allowed := Set([p*(q^2-1),q^3+1,(q^2+1)* (q-1), (q^2+1)* (q+1)]);
          elif (q+1) mod 4 = 2 then
              allowed := Set([p* (q^2-1), (q^3+1)/2, (q^2+1)* (q-1)/2,
                              (q^2+1)* (q+1)/2 ]);
              if q = 5 then
                  maxprime := Maximum (orders) > 21;
              fi;
          else
              allowed := Set([p* (q^2-1), (q^3+1)/4, (q^2+1)* (q-1)/4,
                              (q^2+1)* (q+1)/4 ]);
          fi;
      else
          r := 2 * ((n-1)/2)+1;
          maxprime := LargestPrimeOccurs (q^r+1, orders)
                      and Maximum (orders) <= (q^(r+1)-1)/ (q-1);
          if n = 6 and q = 2 then
              maxprime := maxprime and 18 in orders;
          fi;
      fi;
  elif type = "S" then
      if n = 4 then
          if q mod 2 = 0 then
              allowed := Set([4, p * (q-1), p * (q+1), q^2-1, q^2+1]);
          elif q mod 3 = 0 then
              allowed := Set([9, p * (q-1), p * (q+1), (q^2-1)/2, (q^2+1)/2]);
          else
              allowed := Set([p * (q-1), p * (q+1), (q^2-1)/2, (q^2+1)/2]);
          fi;
      elif n = 6 and q = 2 then
          allowed := Set([ 7, 8, 9, 10, 12, 15 ]);
          maxprime := 8 in orders and 15 in orders;
      else
          maxprime := LargestPrimeOccurs (q^(n/2)+1, orders) and
                      LargestPrimeOccurs (q^(n/2)-1, orders);
      fi;
  elif type = "O^+" and n = 8 and q = 2 then
      allowed := Set([ 7, 8, 9, 10, 12, 15 ]);
      maxprime := 8 in orders and 15 in orders;
  elif type = "O^+" and n = 10 and q = 2 then
      allowed := Set([ 18, 24, 31, 42, 45, 51, 60]);
  elif type = "O^-" then
      maxprime := LargestPrimeOccurs (q^(n/2)+1, orders) and
                  LargestPrimeOccurs (q^(n/2 -1)-1, orders);
  elif type = "2B" then
      rq := RootInt(2*q);
      allowed := Set([4, q-1, q-rq+1, q+rq+1]);
  elif type = "2G" then
      rq := RootInt(3*q);
      allowed := Set([9, 3* (q-1), q+1, q-rq+1, q+rq+1]);
  elif type = "G" then
      if p = 2 then
          allowed := Set([8, 4 * (q-1), 4 * (q+1), q^2-1, q^2-q+1, q^2+q+1]);
      elif p <= 5 then
          allowed := Set([p^2, p * (q-1), p * (q+1), q^2-1, q^2-q+1, q^2+q+1]);
      else
          allowed := Set([p * (q-1), p * (q+1), q^2-1, q^2-q+1, q^2+q+1]);
      fi;
  elif type = "2F" and q = 2 then
      allowed := Set([10, 12, 13, 16 ]);
  elif type = "2F" and q = 8 then
      allowed := Set([ 12, 16, 18, 20, 28, 35, 37, 52, 57, 63, 65, 91, 109 ]);
      maxprime := Maximum (orders) > 37;
  elif type = "3D" and q = 2 then
      allowed := Set([ 8, 12, 13, 18, 21, 28 ]);
      maxprime := Maximum (orders) > 13;
  elif type = "F" and q = 2 then
      allowed := Set([ 13, 16, 17, 18, 20, 21, 24, 28, 30 ]);
  elif type = "2E" and q = 2 then
      allowed := Set([ 13, 16, 17, 18, 19, 20, 21, 22, 24, 28, 30, 33, 35 ]);
  elif type = "E" and n = 7 and q = 2 then
      maxprime := Maximum (orders) <= 255;
  fi;
  
  if not maxprime then
      return "RO_CONTRADICTION";
  fi;
  for ii in allowed do
      orders := Filtered( orders, o-> ii mod o <> 0 );
  od;
  if orders = [] then
      return Concatenation(type,String(n), "(", String(q), ")");
  else
      return  "RO_CONTRADICTION";
  fi;
end;  #  VerifyOrders

#/*  P random process for group; 
#    distinguish PSp (2n, p^e) from Omega (2n + 1, p^e);
#    orders are orders of elements */
#

RECOG.DistinguishSpO := function (G, n, p, e, orders)
    local   twopart,   q,  goodtorus,  t1,  tp,  t2,  
            found,  tf,  ttf,  g,  o,  mp,  i,  x,  z,  po,  h;
    
    twopart := function (n)
        local k;
        k := 1;
        while n mod 2 = 0 do
            n := n/2; 
            k := k*2;
        od;
        return k;
    end;
    
    q := p^e;
    if n mod 2 = 1 and (q + 1) mod 4 = 0 then
        goodtorus := 2 * n; 
        t1 := q^n + 1;
        tp := twopart ((q^n + 1) / 2);
    else
        goodtorus := n; 
        t1 := q^n - 1;
        tp := twopart ((q^n - 1) / 2);
    fi;
    t2 := q^QuoInt(n , 2) + 1;
    
    found := false;
    tf := 0; ttf := 0;  # counters to deal with wrong char groups
    repeat
        g := PseudoRandom (G);
        o := RECOG.LieTypeOrderFunc (g);
        if o mod p <> 0 then
            ttf := ttf+1;
            mp := RECOG.OMppdset (p, o);
            
            
            if 2*o = t1 then
                tf := tf+1;
                g := g^(o / 2);
                found := n mod 2 = 1; 
                i := 0;
                while not found and i < 8 * n do
                    i := i+1;
                    x := PseudoRandom (G); 
                    z := g * g^x;
                    o := RECOG.LieTypeOrderFunc (z);
                    if o mod 2 = 1 then
                        po := RECOG.LieTypeOrderFunc (z^((o + 1) / 2) / x);
                        mp := RECOG.OMppdset (p, po);
                        if (q - 1) mod 4 = 0 and (n - 1) * e in mp or
                           (q + 1) mod 4 = 0 and 2 * (n - 1) * e in mp or
                           (q - 1) mod 4 = 0 and 2 * (n - 1) * e in mp or
                           (q + 1) mod 4 = 0 and 2 * n * e in mp
#		      or (n = 4 and 6 in mp)
                           then
                            found := true;
                  #printf"mp= %o, o (z)= %o\n", mp, Factorization (oo);
                        fi;
                    fi;
                od;
            fi;
        fi;
    until found or (tf > 15) or (ttf > 80);
    if ttf > 80 then 
        return "RO_NO_LUCK"; 
    fi;
    
    for i in [1..6 * n] do
        h := PseudoRandom (G); 
        o := Order (g * g^h);
        if (q * (q + 1) mod o <> 0) and (q * (q - 1) mod o <> 0) 
           then
            return RECOG.VerifyOrders ("S", 2 * n, q, orders);
        fi;
    od;
    
    return RECOG.VerifyOrders ("O", 2 * n + 1, q, orders);
    
end;   # DistinguishSpO

#
#/* compute Artin invariants for element of order o; 
#   p is characteristic */

RECOG.ComputeArtin := function (o, p)
    local   IsFermat,  IsMersenne,  primes,  orders;
    IsFermat := n-> IsPrime(n) and Set(Factors(n-1)) = [2];
    IsMersenne := n->IsPrime(n) and Set(Factors(n+1)) = [2];
    primes := Set(Factors(o));
    RemoveSet(primes,p);
    RemoveSet(primes,2);
    orders := Set(primes, x-> OrderMod(p, x));

    if IsFermat (p) and o mod 4 = 0 then 
        AddSet(orders,1);
    fi;
    if IsMersenne (p) and o mod 4 = 0 then 
        AddSet(orders,2);
    fi;
    if p = 2 and o mod 9 = 0 then
        AddSet(orders, 6);
    fi;
    return orders;
end;

#/* partition at most Nmr elements according to their 
#   projective orders listed in values; we consider
#   at most NmrTries elements; P is a random process */ 

RECOG.ppdSample := function (G, ppd, p, values, SampleSize) 
    local   Bins,  x,  j,  original,  NmrTries,  g,  o,  list;

    Bins := ListWithIdenticalEntries(Length(values),0);

   for x in ppd do
       for j in [1..Length(values)] do
           if values[j] in x then
               Bins[j] := Bins[j] + 1;
           fi;
       od;
   od;
   original := Length(ppd);
            
   ppd := [];

   NmrTries := 0;
   while NmrTries <= SampleSize do 
       NmrTries := NmrTries + 1;
       g := PseudoRandom (G);
       o := Order (g);
       list := RECOG.ComputeArtin (o, p);
       Add (ppd, list);
       for j in [1..Length(values)] do
           if values[j] in list then
               Bins[j] := Bins[j]+1;
           fi;
       od;
   od;
   

   return [Bins/(original + SampleSize), ppd, Bins];

end;

RECOG.OrderSample := function (G, p, orders, values, SampleSize)
    local    Bins,  i,  j,  original,  NmrTries,  g,  o,  
            Total;

    Bins := ListWithIdenticalEntries(Length(values),0);

   for i in orders do
      for j in [1..Length(values)] do
         if i mod values[j] = 0 then
            Bins[j] := Bins[j] + 1;
         fi;
      od;
   od;
   original := Length(orders);
            
   NmrTries := 0;
   while NmrTries <= SampleSize do 
      NmrTries := NmrTries + 1;
      g := PseudoRandom (G);
      o := RECOG.LieTypeOrderFunc (g);
      Add (orders, o);
      for j in [1..Length(values)] do
         if o mod values[j] = 0 then
            Bins[j] := Bins[j]+1;
         fi;
      od;
      Total := Sum(Bins);
   od;

   return [ Bins/ (SampleSize + original), orders, Bins] ;

end;

# PSL (2, p^k) vs PSp (4, p^(k / 2)) 
RECOG.PSLvsPSP := function (G, ppd, q, SampleSize, NmrTrials, orders)
    local   p,  g,  o,  v1,  values,  temp,  prob;
   p := Factors (q)[1];
   if q = 2 then
      repeat 
         SampleSize := SampleSize - 1;
         g := PseudoRandom (G);
         o := RECOG.LieTypeOrderFunc (g);
         if o = 4 then 
            return RECOG.VerifyOrders ("L",2,9, orders);
         fi;
      until SampleSize = 0;
      return RECOG.VerifyOrders ("L",2,4, orders);
   fi;

   v1 := Maximum (ppd);
   ppd := [];
   values := [v1];
   repeat 
       temp := RECOG.ppdSample (G, ppd, p, values, SampleSize);
       prob := temp[1];
       ppd  := temp[2];
       prob := prob[1];
       if prob >= 1/3 and prob < 1/2 then
           return RECOG.VerifyOrders ("L",2, q^2, orders);
       elif prob >= 1/5 and prob < 1/4 then
           return RECOG.VerifyOrders ("S",4, q, orders);
       fi;
       NmrTrials := NmrTrials + 1;
   until NmrTrials = 0;

   if NmrTrials = 0 then 
#      return "Have not settled this recognition"; 
      return "RO_NO_LUCK"; 
   fi;

end;


RECOG.OPlus82vsS62 := function (G, orders, SampleSize)
    local   values,  temp,  prob;
    values := [15];
    temp := RECOG.OrderSample (G, 2, [], values, SampleSize);
    prob := temp[1]; 
    orders := temp[2];
    prob := prob[1];
#"prob is ", prob;
    if AbsoluteValue (1/5 - prob) < AbsoluteValue (1/15 - prob) then 
        return RECOG.VerifyOrders ("O^+",8, 2, orders );
    else 
        return RECOG.VerifyOrders ("S",6, 2, orders );
    fi;
end;

RECOG.OPlus83vsO73vsSP63 := function (G, orders, SampleSize)
    local   values,  temp,  prob;
    values := [20];
    temp := RECOG.OrderSample (G, 3, [], values, SampleSize);
    prob := temp[1];
    orders := temp[2];
    prob := prob[1];
    if AbsoluteValue (3/20 - prob) < AbsoluteValue (1/20 - prob) then 
        return "O^+_8(3)";
    else 
        return RECOG.DistinguishSpO (G, 3, 3, 1, orders);
    fi;
end;


RECOG.OPlus8vsO7vsSP6 := function (G, orders, p, e, SampleSize)
    local   i,  g,  o,  list;

   for i in [1..SampleSize] do
       g := PseudoRandom (G);
       o := RECOG.LieTypeOrderFunc (g);
       list := RECOG.ComputeArtin (o, p);
       if IsSubset(list, [e, 2 * e, 4 * e]) then
           return RECOG.VerifyOrders ("O^+",8, p^e , orders);    
       fi;
   od;
   if p = 2 then
       return RECOG.VerifyOrders ("S",6, 2^e, orders);
   else
       return RECOG.DistinguishSpO (G, 3, p, e, orders);
   fi;
end;


#// O- (8, p^e) vs S (8, p^e) vs O (9, p^e) 
RECOG.OMinus8vsSPvsO := function (G, v1, p, e, orders, SampleSize, NmrTrials)
    local   ppd,  values,  epsilon,  temp,  prob;
    ppd := [];
    values := [v1];
    epsilon := 1/50;
    repeat 
        temp := RECOG.ppdSample (G, ppd, p, values, SampleSize);
        prob := temp[1]; 
        ppd := temp[2];
#"prob is ", prob;
        prob := prob[1];
        if prob >= 1/5 - epsilon and prob < 1/4 + epsilon then
            return RECOG.VerifyOrders ("O^-",8, p^(v1/8), orders);
        elif prob >= 1/10 - epsilon and prob < 1/8 + epsilon then
            if p = 2 then
                return RECOG.VerifyOrders ("S",8, 2^e, orders);
            else
                return RECOG.DistinguishSpO (G, 4, p, e, orders);
            fi;
        fi;
        NmrTrials := NmrTrials - 1;
    until NmrTrials = 0;
    
    if NmrTrials = 0 then 
#      return "Have not settled this recognition"; 
        return "RO_NO_LUCK"; 
    fi;
    
end;

RECOG.ArtinInvariants := function (G, p, Nmr)
    local   orders,  combs,  invariants,  newv1,  v1,  i,  g,  o,  
            ppds;

    orders := []; 
    combs := [];
    if p > 2 then 
        invariants := [0, 1, 2];
    else 
        invariants := [0, 1];
    fi;
    newv1 := Maximum (invariants);
    repeat
        v1 := newv1;
        for i in [1..Nmr] do
            g := PseudoRandom (G);
            o := RECOG.LieTypeOrderFunc (g);
            AddSet (orders, o);
            if o mod 3 = 0 then 
                AddSet(orders,3);
            fi;
            if o mod 4 = 0 then 
                AddSet (orders, 4); 
            fi;
            ppds := RECOG.OMppdset (p, o);
            if p = 2 and o mod 9 = 0 then 
                AddSet (ppds, 6);
                AddSet (orders, 9);
            fi;
            UniteSet(invariants,ppds);
            UniteSet(combs, Combinations (ppds, 2));
        od;
        newv1 := Maximum (invariants);
    until newv1 = v1;
    return [invariants, combs, orders];
end; # ArtinInvariants


RECOG.LieType := function (G, p, orders, Nmr)
    local   temp,  invar,  combs,  orders2,  v1,  v2,  w,  v3,  e,  m,  
            bound,  combs2;

    #   P := RandomProcess ( G );
    temp := RECOG.ArtinInvariants (G, p, Nmr);
    invar := temp[1];
    combs := temp[2];
    orders2 := temp[3];
   UniteSet(orders, orders2);
   
   v1 := Maximum (invar);
   RemoveSet(invar, v1);

   if v1 = 2 then
      return RECOG.VerifyOrders ("L",2, p, orders);
   fi;

   if v1 = 3 then
      if p > 2 then
         return RECOG.VerifyOrders ("L",3, p, orders);
      elif 8 in orders then
         return RECOG.VerifyOrders ("U",3, 3, orders);
      else
         return RECOG.VerifyOrders ("L",3, 2, orders);
      fi; 
   fi;


   if v1 = 4 then
      if 3 in invar then
         if p > 2 then
            return RECOG.VerifyOrders ("L",4, p, orders);
         elif 15 in orders then
	    return RECOG.VerifyOrders ("L",4, 2, orders);
         else
            return RECOG.VerifyOrders ("L",3, 4, orders);
         fi; 
      else
         return RECOG.PSLvsPSP (G, [1, 2, 4], p, RECOG.LieTypeSampleSize, 
                   RECOG.LieTypeNmrTrials, orders);
      fi;
   fi;  # v1 = 4

   v2 := Maximum (invar);
   w := v1 / (v1 - v2);

#v1; v2; w; invar; orders;
   if v1 = 12 and v2 = 4 and p = 2 then
      if 21 in orders then
         return RECOG.VerifyOrders ("G",2, 4, orders);
      elif 16 in orders then
         return RECOG.VerifyOrders ("2F",4, 2, orders);
      elif 7 in orders then
         return RECOG.VerifyOrders ("2B",2, 8, orders);
      elif 15 in orders then
         return RECOG.VerifyOrders ("U",3, 4, orders);
      else 
          return "RO_CONTRADICTION";
      fi; 
   fi;  # v2 = 4

   RemoveSet(invar,v2);
   if Length(invar)  = 0 then 
       return "RO_Unknown"; 
   fi;
   v3 := Maximum (invar);

#printf"p, v1, v2, v3: %o %o %o %o;",p,v1,v2,v3; invar; combs; orders;
   if v1 mod 2 = 1 then
      e := v1 - v2;
      if v1 mod e <> 0 then
         return "RO_CONTRADICTION";
      fi;
      m := v1/e;
      if v3 <> e* (m-2) then
          return "RO_CONTRADICTION";
      fi;
      return RECOG.VerifyOrders ("L", m, p^e, orders);
   fi;

   if w = 3/2 then
      if p = 2 and not 3 in orders then
      	 if v1 mod 8 <> 4 then
	    return "RO_CONTRADICTION";
	 fi;
	 return RECOG.VerifyOrders ("2B",2,2^(v1 / 4), orders);
      fi;
      if v1 mod 6 <> 0 then
         return "RO_CONTRADICTION";
      fi;
      if p = 3 and not 4 in orders then
         if v1 > 6 then
            if v1 mod 12 <> 6 then
	       return "RO_CONTRADICTION";
	    fi;
	    return RECOG.VerifyOrders ("2G",2, 3^(v1 / 6), orders);
         else
	    return RECOG.VerifyOrders ("L",2, 8, orders);
         fi;
      fi;
      return RECOG.VerifyOrders ("U",3, p^(v1 / 6), orders);
   fi; 

   if w = 4/3 then
      if p = 2 and v1 mod 8 = 4 then
	 return RECOG.VerifyOrders ("2B",2, 2^(v1 / 4), orders);
      fi;
      return "RO_CONTRADICTION";
   fi;

   if w = 2 then  # exceptional groups
      if v1 mod 12 = 0 and not ([v1 / 3, v1] in combs) then
         if 4 * v3 = v1 then
            return RECOG.VerifyOrders ("3D",4, p^(v1 / 12), orders);
         elif (v1 / 4) in invar or (p = 2 and v1 = 24) then
            return RECOG.VerifyOrders ("G",2, p^(v1 / 6), orders);
         else
	    if p = 2 and v1 mod 24 = 12 and 12*v3 = 4*v1 then
               return RECOG.VerifyOrders ("2F",4,2^(v1 / 12), orders); 
	    else return "RO_CONTRADICTION";
	    fi;
         fi; 

  #    /* next clause is replacement for error in draft of paper */
      elif v1 mod 12 = 6 and Maximum (orders) <= p^(v1/3) + p^(v1/6) + 1 then
         return RECOG.VerifyOrders ("G",2, p^(v1 / 6), orders);
      fi; 

      if v1 mod 4 = 2 then
	 return RECOG.VerifyOrders ("L",2,p^(v1 / 2), orders);
      else
         return RECOG.PSLvsPSP (G, Union(invar,[v1, v2]),p^(v1 / 4),
                  RECOG.LieTypeSampleSize, RECOG.LieTypeNmrTrials, orders);
      fi;
   fi;  # w = 2

#printf"p, v1, v2, v3: %o %o %o %o;",p,v1,v2,v3; invar; combs; orders;
   if w = 3 then
      if v1 mod 18 = 0 and 18 * v3 = 10 * v1 then
         if 8* (v1 / 18) in invar then
            return RECOG.VerifyOrders ("2E",6, p^(v1 / 18), orders);
	 else return "RO_OTHER";
	 fi;
      elif v1 mod 12 = 0 then
         if v1 > 12 or p > 2 then
            if v1 = 2 * v3 and not ([v1 / 2, v1] in combs)
               and not ([v1 / 3, v1] in combs) then
               return RECOG.VerifyOrders ("F",4, p^(v1 / 12), orders);
            fi;
         elif 9 in orders and not ([4, 12] in combs) then
            return RECOG.VerifyOrders ("F",4, 2, orders);
         fi;  
      fi; 
   fi;  # w = 3

   if w = 4 and 8 * v1 = 12 * v3 then
      if v1 mod 12 = 0 then
         return RECOG.VerifyOrders ("E",6, p^(v1 / 12), orders);
      fi;
      return "RO_CONTRADICTION";
   fi;

   if w = 9/2 and 12 * v1 = 18 * v3 then
      if v1 mod 18 = 0 then
         return RECOG.VerifyOrders ("E",7, p^(v1 / 18), orders);
      fi;
      return "RO_CONTRADICTION";
   fi;

   if w = 5 and 20 * v1 = 30 * v3 then
      if v1 mod 30 = 0 then
         return RECOG.VerifyOrders ("E",8, p^(v1 / 30), orders);
      fi;
      return "RO_CONTRADICTION";
   fi;   # exceptional groups

   if v1 mod (v1 - v2) <> 0 then   # unitary groups
      if (v1-v2) mod 4 <> 0  or  2 * v1 mod (v1 - v2) <> 0 then 
          return "RO_OTHER";
      fi;
      e := (v1-v2) / 4;
      m := (2 * v1) / (v1 - v2);
      if ((m + 1) mod 4 = 0 and e * (m + 1) in invar) or
        ((m + 1) mod 4 <> 0 and e * (m + 1) / 2 in invar) then
	    if (m > 7 and v2-v3 = 4*e) or (m <= 7 and v2-v3 = 2*e) then
               return RECOG.VerifyOrders ("U", m + 1, p^e, orders);
	    fi;
      else
         if (m > 5 and v2-v3 = 4*e) or (m = 5 and v2-v3 = 2*e) then
            return RECOG.VerifyOrders ("U", m, p^e, orders);
	 fi;
      fi;
      return "RO_OTHER";
   fi;   # unitary groups
   
#printf"1: v1 v2 v3 = %o %o %o;;",v1, v2, v3; invar;
   if (v1 - v2) mod 2 <> 0 then
      e := v1 - v2;  m := v1 / (v1 - v2);
      if v3 = e* (m-2) or (p = 2 and e* (m-2) = 6) or (m <= 3) then
         return RECOG.VerifyOrders ("L", m, p^e, orders);
      else
         return "RO_OTHER";
      fi;
   fi;
   
   e := (v1 - v2) / 2; m := v1 / (v1 - v2);  # only classical grps remain

   if p = 2 and e * m = 6 and e <= 2 and 91 in orders then
      if v3 = 10-2*e  or  m = 3 then
         return RECOG.VerifyOrders ("L", m, 2^(2 * e), orders);
      else
         return "RO_OTHER";
      fi;
   fi;

   if Set([m * e, v1]) in combs then
      if v3 = 2*e* (m-2) or m <= 3 then
         return RECOG.VerifyOrders ("L", m, p^(2 * e), orders);
      else
         return "RO_OTHER";
      fi;
   fi;

   if m = 3 then
      if 3 * v3 = v1 then
         return RECOG.VerifyOrders ("U",4, p^(v1 / 6), orders);
      else
         if p^e = 2 then
            return RECOG.OPlus82vsS62 (G, orders, RECOG.LieTypeSampleSize);
         fi;
         if p^e = 3 then
            return RECOG.OPlus83vsO73vsSP63 (G,orders,RECOG.LieTypeSampleSize);
         else
            return RECOG.OPlus8vsO7vsSP6 (G,orders,p,e,RECOG.LieTypeSampleSize);
         fi; 
      fi;
   fi;

   if v3 <> 2*e* (m-2) and (m > 4 or v3 <> 5*e) then   # wrong characteristic
      return "RO_OTHER";
   fi;
   
   if IsMatrixGroup(G) then
       bound := 5*DimensionOfMatrixGroup(G);
   else
       bound := 100;
   fi;
   temp := RECOG.ArtinInvariants (G, p, bound);
   invar := temp[1]; combs2 := temp[2]; orders2 := temp[3];
   combs := Union(combs, combs2);
   orders := Union(orders, orders2);
   if m mod 2 = 0 then
      if [m * e, (m + 2) * e] in combs then
          return RECOG.VerifyOrders ("O^+", 2 * m + 2, p^e, orders);
      elif m = 4 then 
         return RECOG.OMinus8vsSPvsO(G,v1,p,e,orders,RECOG.LieTypeSampleSize,
                                     RECOG.LieTypeNmrTrials);
      else #/* m >= 6 */
         if [ (m - 2) * e, (m + 2) * e] in combs then
            if p = 2 then 
               return RECOG.VerifyOrders ("S", 2 * m, 2^e, orders);
            else 
               return RECOG.DistinguishSpO (G, m, p, e, orders);
            fi;
         else
            return RECOG.VerifyOrders ("O^-", 2*m, p^e, orders);
         fi; 
      fi;  # m even
   elif [(m - 1) * e, (m + 3) * e] in combs then
      return RECOG.VerifyOrders ("O^+", 2 * m + 2, p^e, orders);
   elif [(m - 1) * e, (m + 1) * e] in combs then
      if p = 2 then 
         return RECOG.VerifyOrders ("S", 2 * m, 2^e, orders);
      fi;
      # p <> 2 case 
      return RECOG.DistinguishSpO (G, m, p, e, orders);
   else
      return RECOG.VerifyOrders ("O^-", 2 * m, p^e, orders);
   fi; 

   return "RO_undecided";
end;

FindHomMethodsProjective.LieTypeNonConstr := function(ri,G)
    local count,dim,f,i,ords,p,q,r,res;
    RECOG.SetPseudoRandomStamp(G,"LieTypeNonConstr");
    dim := ri!.dimension;
    f := ri!.field;
    q := Size(f);
    p := Characteristic(f);

    count := 0;
    ords := Set(ri!.simplesoclerando);
    while true do   # will be left by return
        r := RECOG.LieType(ri!.simplesocle,p,ords,30+10*dim);
        if not(IsString(r)) or r{[1..3]} <> "RO_" then
            # We found something:
            Info(InfoRecog,2,"LieTypeNonConstr: found ",r,
                 ", lookup up hints...");
            ri!.comment := Concatenation("_",r);
            res := LookupHintForSimple(ri,G,r);
            if res = true then return true; fi;
            Info(InfoRecog,2,"LieTypeNonConstr: giving up.");
            return fail;
        fi;
        count := count + 1;
        if count > 3 then
            Info(InfoRecog,2,"LieTypeNonConstr: giving up...");
            return fail;
        fi;
        Info(InfoRecog,2,"LieTypeNonConstr: need more element orders...");
        for i in [1..dim] do
            AddSet(ords,RandomElmOrd(ri,"LieTypeNonConstr",false).order);
        od;
    od;
end;

##
##  This program is free software: you can redistribute it and/or modify
##  it under the terms of the GNU General Public License as published by
##  the Free Software Foundation, either version 3 of the License, or
##  (at your option) any later version.
##
##  This program is distributed in the hope that it will be useful,
##  but WITHOUT ANY WARRANTY; without even the implied warranty of
##  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
##  GNU General Public License for more details.
##
##  You should have received a copy of the GNU General Public License
##  along with this program.  If not, see <http://www.gnu.org/licenses/>.
##

