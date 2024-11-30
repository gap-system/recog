#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This files's authors include Max Neunhöffer, Ákos Seress.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
##
##  A collection of find homomorphism methods for permutation groups.
##
#############################################################################

#! @BeginChunk MovesOnlySmallPoints
#! If a permutation group moves only small points
#! (currently, this means that its largest moved point is at most 10),
#! then this method computes a stabilizer chain for the group via
#! <Ref Subsect="StabChain" Style="Text"/>.
#! This is because the most convenient way of solving constructive membership
#! in such a group is via a stabilizer chain.
#! In this case, the calling node becomes a leaf node of the composition tree.
#!
#! If the input group moves a large point (currently, this means a point
#! larger than 10), then this method returns <K>NeverApplicable</K>.
#! @EndChunk
BindRecogMethod(FindHomMethodsPerm, "MovesOnlySmallPoints",
"calculate a stabilizer chain if only small points are moved",
rec(validatesOrAlwaysValidInput := true),
function(ri, G)
  if LargestMovedPoint(G) <= 10 then
      return FindHomMethodsPerm.StabChain(ri, G);
  fi;
  return NeverApplicable;
end);

#! @BeginChunk NonTransitive
#! If a permutation group <A>G</A> acts nontransitively then this method
#! computes a homomorphism to the action of <A>G</A> on the orbit of the
#! largest moved point. If <A>G</A> is transitive then the method returns
#! <K>NeverApplicable</K>.
#! @EndChunk
#! @BeginCode FindHomMethodsPerm.NonTransitive
BindRecogMethod(FindHomMethodsPerm, "NonTransitive",
"try to find non-transitivity and restrict to orbit",
rec(validatesOrAlwaysValidInput := true),
function(ri, G)
    local hom,la,o;

    # test whether we can do something:
    if IsTransitive(G) then
        return NeverApplicable;
    fi;

    # compute orbit of the largest moved point
    la := LargestMovedPoint(G);
    o := Orb(G,la,OnPoints);
    Enumerate(o);
    # compute homomorphism into Sym(o), i.e, restrict
    # the permutation action of G to the orbit o
    hom := OrbActionHomomorphism(G,o);
    # TODO: explanation
    Setvalidatehomominput(ri, {ri,p} -> ForAll(o, x -> (x^p in o)));
    # store the homomorphism into the recognition node
    SetHomom(ri,hom);

    # TODO: explanation
    Setimmediateverification(ri, true);

    # indicate success
    return Success;
end);
#! @EndCode

#! @BeginChunk Imprimitive
#! If the input group is not known to be transitive then this method
#! returns <K>NotEnoughInformation</K>. If the input group is known to be transitive
#! and primitive then the method returns <K>NeverApplicable</K>; otherwise, the method
#! tries to compute a nontrivial block system. If successful then a
#! homomorphism to the action on the blocks is defined; otherwise,
#! the method returns <K>NeverApplicable</K>.
#! 
#! If the method is successful then it also gives a hint for the children of
#! the node by determining whether the kernel of the action on the
#! block system is solvable. If the answer is yes then the default value 20
#! for the number of random generators in the kernel construction is increased
#! by the number of blocks.
#! @EndChunk
BindRecogMethod(FindHomMethodsPerm, "Imprimitive",
"for a imprimitive permutation group, restricts to block system",
rec(validatesOrAlwaysValidInput := true),
function(ri, G)
    local blocks,hom,pcgs,subgens;

    # Only look for primitivity once we know transitivity:
    # This ensures the right trying order even if the ranking is wrong.
    if not HasIsTransitive(G) then
        return NotEnoughInformation;
    fi;

    # We test for known non-primitivity:
    if HasIsPrimitive(G) and IsPrimitive(G) then
        return NeverApplicable;
    fi;

    RECOG.SetPseudoRandomStamp(G,"Imprimitive");

    # Now try to work:
    blocks := MaximalBlocks(G,MovedPoints(G));
    if Length(blocks) = 1 then
        SetIsPrimitive(G,true);
        return NeverApplicable;
    fi;

    # Find the homomorphism:
    hom := ActionHomomorphism(G,blocks,OnSets);
    Setvalidatehomominput(ri, {ri,p} -> OnSetsSets(blocks, p) = blocks);
    SetHomom(ri,hom);

    # Now we want to help recognising the kernel, we first check, whether
    # the restriction to one block is solvable, which would mean, that
    # the kernel is solvable and that a hint is in order:
    Setimmediateverification(ri,true);
    InitialDataForKernelRecogNode(ri).blocks := blocks;
    AddMethod(InitialDataForKernelRecogNode(ri).hints, FindHomMethodsPerm.PcgsForBlocks, 400);
    AddMethod(InitialDataForKernelRecogNode(ri).hints, FindHomMethodsPerm.BalTreeForBlocks, 200);
    findgensNmeth(ri).args[1] := 3 + BAL_CONST * Length(blocks);
    findgensNmeth(ri).args[2] := 5;
    return Success;
end);

#! @BeginChunk PcgsForBlocks
#! This method is called after a hint is set in
#! <C>FindHomMethodsPerm.</C><Ref Subsect="Imprimitive" Style="Text"/>.
#! Therefore, the group <A>G</A> preserves a non-trivial block system.
#! This method checks whether or not the restriction of <A>G</A> on one block
#! is solvable.
#! If so, then <C>FindHomMethodsPerm.</C><Ref Subsect="Pcgs" Style="Text"/> is
#! called, and otherwise <K>NeverApplicable</K> is returned.
#! @EndChunk
BindRecogMethod(FindHomMethodsPerm, "PcgsForBlocks",
"TODO",
function(ri, G)
  local blocks,pcgs,subgens;
  blocks := ri!.blocks;   # we know them from above!
  subgens := List(GeneratorsOfGroup(G),g->RestrictedPerm(g,blocks[1]));
  pcgs := Pcgs(Group(subgens));
  if pcgs <> fail then
      # We now know that the kernel is solvable, go directly to
      # the Pcgs method:
      return FindHomMethodsPerm.Pcgs(ri,G);
  fi;
  # We have failed, let others do the work...
  return NeverApplicable;
end);

#! @BeginChunk BalTreeForBlocks
#! This method creates a balanced composition tree for the kernel of an
#! imprimitive group. This is guaranteed as the method is just called
#! from <C>FindHomMethodsPerm.</C><Ref Subsect="Imprimitive" Style="Text"/>
#! and itself. The homomorphism for the split in the composition tree used is
#! induced by the action of <A>G</A> on
#! half of its blocks.
#! @EndChunk
BindRecogMethod(FindHomMethodsPerm, "BalTreeForBlocks",
"TODO",
function(ri, G)
  local blocks,cut,hom,lowerhalf,nrblocks,o,upperhalf,l,n,seto;

  blocks := ri!.blocks;

  # We do exactly the same as in the non-transitive case, however,
  # we restrict to about half the blocks and pass our knowledge on:
  nrblocks := Length(blocks);
  if nrblocks = 1 then
      # this might happen during the descent into the tree
      return NeverApplicable;
  fi;
  cut := QuoInt(nrblocks,2);  # this is now at least 1
  lowerhalf := blocks{[1..cut]};
  upperhalf := blocks{[cut+1..nrblocks]};
  o := Concatenation(upperhalf);
  # The order of 'o' in the homom must align with InitialDataForImageRecogNode(ri).blocks below
  hom := ActionHomomorphism(G,o);

  # Make a set so checking validatehomominput is faster
  seto := Immutable(Set(o));
  Setvalidatehomominput(ri, {ri,p} -> ForAll(o, x -> x^p in seto));
  SetHomom(ri,hom);
  Setimmediateverification(ri,true);
  findgensNmeth(ri).args[1] := 3 + BAL_CONST * cut;
  findgensNmeth(ri).args[2] := 5;
  if nrblocks - cut > 1 then
      l := Length(upperhalf[1]);
      n := Length(upperhalf);
      InitialDataForImageRecogNode(ri).blocks := List([1..n],i->[(i-1)*l+1..i*l]);
      AddMethod(InitialDataForImageRecogNode(ri).hints, FindHomMethodsPerm.BalTreeForBlocks, 200);
  fi;
  if cut > 1 then
      InitialDataForKernelRecogNode(ri).blocks := lowerhalf;
      AddMethod(InitialDataForKernelRecogNode(ri).hints, FindHomMethodsPerm.BalTreeForBlocks, 200);
  fi;
  return Success;
end);

# Now to the small base groups using stabilizer chains:

# The GAP manual suggests that the labels at each level of a stabiliser chain
# are identical GAP objects, but it does not promise this.
# This function tests whether the stabiliser chain has this property, and
# gives an error if not.
DoSafetyCheckStabChain := function(S)
  while IsBound(S.stabilizer) do
      if not IsIdenticalObj(S.labels, S.stabilizer.labels) then
          ErrorNoReturn("Alert! labels not identical on different levels!");
      fi;
      S := S.stabilizer;
  od;
end;

#! @BeginChunk StabChain
#! This is the randomized &GAP; library function for computing a stabiliser
#! chain. The method selection process ensures that this function is called
#! only with small-base inputs, where the method works efficiently.
#! @EndChunk
BindRecogMethod(FindHomMethodsPerm, "StabChain",
"for a permutation group using a stabilizer chain",
rec(validatesOrAlwaysValidInput := true),
function(ri, G)
     local Gmem,S,si;

     # We know transitivity and primitivity, because there are higher ranked
     # methods checking for them!

     # Calculate a stabilizer chain:
     Gmem := GroupWithMemory(G);
     if HasStabChainMutable(G) or HasStabChainImmutable(G) or HasSize(G) then
         si := Size(G);
         S := StabChainOp(Gmem,rec(random := 900,size := si));
     else
         S := StabChainOp(Gmem,rec(random := 900));
     fi;
     DoSafetyCheckStabChain(S);
     Setslptonice(ri,SLPOfElms(S.labels));
     StripStabChain(S);
     SetNiceGens(ri,S.labels);
     MakeImmutable(S);
     ri!.stabilizerchain := S;
     Setslpforelement(ri,SLPforElementFuncsPerm.StabChain);
     SetFilterObj(ri,IsLeaf);
     SetSize(G,SizeStabChain(S));
     SetSize(ri,SizeStabChain(S));
     ri!.Gnomem := G;
     return Success;
end);

SLPforElementFuncsPerm.StabilizerChainPerm := function(ri,x)
  local r;
  r := SiftGroupElementSLP(ri!.stabilizerchain,x);
  return r.slp;
end;

#! @BeginChunk StabilizerChainPerm
#! TODO
#! @EndChunk
# TODO: merge FindHomMethodsPerm.StabilizerChainPerm and  FindHomMethodsProjective.StabilizerChainProj ?
BindRecogMethod(FindHomMethodsPerm, "StabilizerChainPerm",
Concatenation(
    "for a permutation group using a stabilizer chain via the ",
    "<URL Text=\"genss package\">",
    "https://gap-packages.github.io/genss/",
    "</URL>"),
rec(validatesOrAlwaysValidInput := true),
function(ri, G)
  local Gm,S;
  Gm := Group(ri!.gensHmem);
  Gm!.pseudorandomfunc := [rec(
     func := function(ri) return RandomElm(ri,"StabilizerChainPerm",true).el; end,
     args := [ri])];
  S := StabilizerChain(Gm);
  SetSize(ri,Size(S));
  SetSize(Grp(ri),Size(S));
  ri!.stabilizerchain := S;
  Setslptonice(ri,SLPOfElms(StrongGenerators(S)));
  ForgetMemory(S);
  Setslpforelement(ri,SLPforElementFuncsPerm.StabilizerChainPerm);
  SetFilterObj(ri,IsLeaf);
  return Success;
end);

# creates recursively a word for <g> using the Schreier tree labels
# from the stabilizer chain <S>
WordinLabels := function(word,S,g)
  local i,point,start;
  if not (IsBound(S.orbit) and IsBound(S.orbit[1])) then
      return fail;
  fi;
  start := S.orbit[1];
  point := start^g;
  while point <> start do
      if not IsBound(S.translabels[point]) then
          return fail;
      fi;
      i := S.translabels[point];
      g := g * S.labels[i];
      point := point^S.labels[i];
      Add(word,i);
  od;
  # now g is in the first stabilizer
  if g <> S.identity then
      if not IsBound(S.stabilizer) then
          return fail;
      fi;
      return WordinLabels(word,S.stabilizer,g);
  fi;
  return word;
end;

# creates a straight line program for an element <g> using the
# Schreier tree labels from the stabilizer chain <S>
SLPinLabels := function(S,g)
  local i,j,l,line,word;
  word := WordinLabels([],S,g);
  if word = fail then
      return fail;
  fi;
  line := [];
  i := 1;
  while i <= Length(word) do
      # Find repeated labels:
      j := i+1;
      while j < Length(word) and word[j] = word[i] do
          j := j + 1;
      od;
      Add(line,word[i]);
      Add(line,j-i);
      i := j;
  od;
  l := Length(S!.labels);
  if Length(word) = 0 then
      return StraightLineProgramNC([[1, 0]], l);
  fi;
  return StraightLineProgramNC([line, [l + 1, -1]], l);
end;


SLPforElementFuncsPerm.StabChain :=
  function( ri, g )
    # we know that ri!.stabilizerchain is an immutable StabChain and
    # ri!.stronggensslp is bound to a slp that expresses the strong generators
    # in that StabChain in terms of the GeneratorsOfGroup(Grp(ri)).
    return SLPinLabels(ri!.stabilizerchain,g);
  end;

StoredPointsPerm := function(p)
  # Determines, as a permutation of how many points p is stored.
  local s;
  s := SIZE_OBJ(p) - GAPInfo.BytesPerVariable;
  if IsPerm4Rep(p) then
      return s/4;   # permutation stored with 4 bytes per point
  elif IsPerm2Rep(p) then
      return s/2;   # permutation stored with 2 bytes per point
  fi;
  ErrorNoReturn("StoredPointsPerm: input is not an internal permutation");
end;

#! @BeginChunk ThrowAwayFixedPoints
#! This method defines a homomorphism of a permutation group
#! <A>G</A> to the action on the moved points of <A>G</A> if
#! <A>G</A> has any fixed points, and is either known to be primitive or the
#! ratio of fixed points to moved points exceeds a certain threshold. If <A>G</A>
#! has fixed points but is not primitive, then it returns
#! <K>NotEnoughInformation</K> so that it may be called again at a later time.
#! In all other cases, it returns <K>NeverApplicable</K>.
#! <P/>
#!
#! In the current setup, the
#! homomorphism is defined if the number <M>n</M> of moved
#! points is at most <M>1/3</M> of the largest moved point of <A>G</A>,
#! or <M>n</M> is at most half of the number of points on which
#! <A>G</A> is stored internally by &GAP;.
#! <P/>
#!
#! The fact that this method returns <K>NotEnoughInformation</K> if <A>G</A>
#! has fixed points but does not know whether it is primitive, is important for
#! the efficient handling of large-base primitive groups by
#! <Ref Func="LargeBasePrimitive"/>.
#! @EndChunk
#
#  A technical explanation of why we use a threshold for the ratio of fixed
#  points to moved points, this is technical so it does not go into the manual:
#  The reason we do not just always discard fixed points is that it also incurs
#  a cost, so we only try to do it when it seems worthwhile to do so.
#
#  Suppose the group G is not known to be primitive. Then we still
#  apply this method if one of the following two criterion is met:
#  - the largest moved point of G is three or more times larger than the number
#    n of actually moved points
#  - there is a generator of G whose internal storage reserves space for a
#    number of moved points which is two or more times larger than n. Note that
#    even for a simple transposition (1,2), for technical reasons it can happen
#    that GAP internally stores it with the same size as a permutation moving a
#    million points; this is wasteful, and the second criterion tries to deal
#    with this.

BindRecogMethod(FindHomMethodsPerm, "ThrowAwayFixedPoints",
"try to find a huge amount of (possible internal) fixed points",
rec(validatesOrAlwaysValidInput := true),
function(ri, G)
      # Check, whether we can throw away fixed points
      local gens,nrStoredPoints,n,largest,isApplicable,o,hom;

      gens := GeneratorsOfGroup(G);
      nrStoredPoints := Maximum(List(gens,StoredPointsPerm));
      n := NrMovedPoints(G);
      largest := LargestMovedPoint(G);
      # If isApplicable is true, we definitely are applicable.
      isApplicable := 3*n <= largest or 2*n <= nrStoredPoints
        or (HasIsPrimitive(G) and IsPrimitive(G) and n < largest);
      # If isApplicable is false, we might become applicable if G figures out
      # that it is primitive.
      if not isApplicable then
          if not HasIsPrimitive(G) and n < largest then
              return NotEnoughInformation;
          else
              return NeverApplicable;
          fi;
      fi;
      o := MovedPoints(G);
      hom := ActionHomomorphism(G,o);
      SetHomom(ri,hom);
      Setvalidatehomominput(ri, {ri,p} -> IsSubset(o, MovedPoints(p)));

      # Initialize the rest of the record:
      findgensNmeth(ri).method := FindKernelDoNothing;

      return Success;
end);

#! @BeginChunk Pcgs
#! This is the &GAP; library function to compute a stabiliser chain for a
#! solvable permutation group. If the method is successful then the calling
#! node becomes a leaf node in the recursive scheme. If the input group is
#! not solvable then the method returns <K>NeverApplicable</K>.
#! @EndChunk
BindRecogMethod(FindHomMethodsPerm, "Pcgs",
"use a Pcgs to calculate a stabilizer chain",
rec(validatesOrAlwaysValidInput := true),
function(ri, G)
    local GM,S,pcgs;
    GM := Group(ri!.gensHmem);
    GM!.pseudorandomfunc := [rec(
       func := function(ri) return RandomElm(ri,"PCGS",true).el; end,
       args := [ri])];
    pcgs := Pcgs(GM);
    if pcgs = fail then
        return NeverApplicable;
    fi;
    S := StabChainMutable(GM);
    DoSafetyCheckStabChain(S);
    Setslptonice(ri,SLPOfElms(S.labels));
    StripStabChain(S);
    SetNiceGens(ri,S.labels);
    MakeImmutable(S);
    ri!.stabilizerchain := S;
    Setslpforelement(ri,SLPforElementFuncsPerm.StabChain);
    SetFilterObj(ri,IsLeaf);
    SetSize(G,SizeStabChain(S));
    SetSize(ri,SizeStabChain(S));
    ri!.Gnomem := G;
    return Success;
end);


# The following commands install the above methods into the database:
#! @BeginCode AddMethod_Perm_FindHomMethodsGeneric.TrivialGroup
AddMethod(FindHomDbPerm, FindHomMethodsGeneric.TrivialGroup, 300);
#! @EndCode

AddMethod(FindHomDbPerm, FindHomMethodsPerm.ThrowAwayFixedPoints, 100);

AddMethod(FindHomDbPerm, FindHomMethodsGeneric.FewGensAbelian, 99);

AddMethod(FindHomDbPerm, FindHomMethodsPerm.Pcgs, 97);

AddMethod(FindHomDbPerm, FindHomMethodsPerm.MovesOnlySmallPoints, 95);

#! @BeginCode AddMethod_Perm_FindHomMethodsPerm.NonTransitive
AddMethod(FindHomDbPerm, FindHomMethodsPerm.NonTransitive, 90);
#! @EndCode

AddMethod(FindHomDbPerm, FindHomMethodsPerm.Giant, 80);

AddMethod(FindHomDbPerm, FindHomMethodsPerm.Imprimitive, 70);

AddMethod(FindHomDbPerm, FindHomMethodsPerm.LargeBasePrimitive, 60);

AddMethod(FindHomDbPerm, FindHomMethodsPerm.StabilizerChainPerm, 55);

AddMethod(FindHomDbPerm, FindHomMethodsPerm.StabChain, 50);


# Note that the last one will always succeed!
