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
##  A collection of find homomorphism methods for projective groups.
##
#############################################################################

SLPforElementFuncsProjective.TrivialGroup_BlocksModScalars := function(ri,g)
    if not IsDiagonalMat(g) then
        return fail;
    fi;
    return StraightLineProgramNC( [ [1,0] ], 1 );
end;

#! @BeginChunk BlocksModScalars
#! This method is only called when hinted from above. In this method it is
#! understood that G should <E>neither</E>
#! be recognised as a matrix group <E>nor</E> as a projective group.
#! Rather, it treats all diagonal blocks modulo scalars which means that
#! two matrices are considered to be equal, if they differ only by a scalar
#! factor in <E>corresponding</E> diagonal blocks, and this scalar can
#! be different for each diagonal block. This means that the kernel of
#! the homomorphism mapping to a node which is recognised using this
#! method will have only scalar matrices in all diagonal blocks.
#!
#! This method does the balanced tree approach mapping to subsets of the
#! diagonal blocks and finally using projective recognition to recognise
#! single diagonal block groups.
#! @EndChunk
BindRecogMethod(FindHomMethodsProjective, "BlocksModScalars",
"TODO",
function(ri, G)
  # We assume that ri!.blocks is a list of ranges where the diagonal
  # blocks are. Note that their length does not have to sum up to
  # the dimension, because some blocks at the end might already be trivial.
  # Note further that in this method it is understood that G should *neither*
  # be recognised as a matrix group *nor* as a projective group. Rather,
  # all "block-scalars" shall be ignored. This method is only used when
  # used as a hint by FindHomMethodsMatrix.BlockDiagonal!
  local H,data,hom,middle,newgens,nrblocks,topblock;
  nrblocks := Length(ri!.blocks);  # this is always >= 1
  if ForAll(ri!.blocks,b->Length(b)=1) then
      # All blocks are projectively trivial, so nothing to do here:
      SetSize(ri,1);
      Setslpforelement(ri, SLPforElementFuncsProjective.TrivialGroup_BlocksModScalars);
      Setslptonice( ri, StraightLineProgramNC([[[1,0]]],
                                              Length(GeneratorsOfGroup(G))));
      SetFilterObj(ri,IsLeaf);
      ri!.comment := "BlocksDim=1";
      return Success;
  fi;

  if nrblocks = 1 then   # in this case the block is everything!
      # no hints for the image, will run into diagonal and notice scalar
      data := rec(poss := ri!.blocks[1]);
      newgens := List(GeneratorsOfGroup(G),x->RECOG.HomToDiagonalBlock(data,x));
      H := GroupWithGenerators(newgens);
      hom := GroupHomByFuncWithData(G,H,RECOG.HomToDiagonalBlock,data);
      SetHomom(ri,hom);
      # The following is already be set, but make it explicit here:
      Setmethodsforimage(ri,FindHomDbProjective);
      # no kernel:
      findgensNmeth(ri).method := FindKernelDoNothing;
      return Success;
  fi;
  # Otherwise more than one block, cut in half:
  middle := QuoInt(nrblocks,2)+1;   # the first one taken
  topblock := ri!.blocks[nrblocks];
  data := rec(poss := [ri!.blocks[middle][1]..topblock[Length(topblock)]]);
  newgens := List(GeneratorsOfGroup(G),x->RECOG.HomToDiagonalBlock(data,x));
  H := GroupWithGenerators(newgens);
  hom := GroupHomByFuncWithData(G,H,RECOG.HomToDiagonalBlock,data);
  SetHomom(ri,hom);

  # the image are the last few blocks:
  # The following is already be set, but make it explicit here:
  Setmethodsforimage(ri,FindHomDbProjective);
  if middle < nrblocks then   # more than one block in image:
      InitialDataForImageRecogNode(ri).blocks := List(ri!.blocks{[middle..nrblocks]},
                                   x->x - (ri!.blocks[middle][1]-1));
      AddMethod(InitialDataForImageRecogNode(ri).hints,
                FindHomMethodsProjective.BlocksModScalars,
                2000);
  fi; # Otherwise the image is to be recognised projectively as usual

  # the kernel is the first few blocks:
  findgensNmeth(ri).args[1] := 10 + nrblocks;
  findgensNmeth(ri).args[2] := 5 + middle - 1;
  # The following is already set, but make it explicit here:
  InitialDataForKernelRecogNode(ri).blocks := ri!.blocks{[1..middle-1]};
  AddMethod(InitialDataForKernelRecogNode(ri).hints, FindHomMethodsProjective.BlocksModScalars, 2000);
  Setimmediateverification(ri,true);
  return Success;
end);

SLPforElementFuncsProjective.StabilizerChainProj := function(ri,x)
  local r;
  r := SiftGroupElementSLP(ri!.stabilizerchain,x);
  return r.slp;
end;

#! @BeginChunk StabilizerChainProj
#! This method computes a stabiliser chain and a base and strong generating
#! set using projective actions. This is a last resort method since for
#! bigger examples no short orbits can be found in the natural action.
#! The strong generators are the nice generator in this case and expressing
#! group elements in terms of the nice generators ist just sifting along
#! the stabiliser chain.
#! @EndChunk
# TODO: merge FindHomMethodsPerm.StabilizerChainPerm and  FindHomMethodsProjective.StabilizerChainProj ?
BindRecogMethod(FindHomMethodsProjective, "StabilizerChainProj",
"last resort: compute a stabilizer chain (projectively)",
function(ri, G)
  local Gm,S,SS,d,f,fu,opt,perms,q;
  d := ri!.dimension;
  f := ri!.field;
  q := Size(f);
  fu := function() return RandomElm(ri,"StabilizerChainProj",true).el; end;
  opt := rec( Projective := true, RandomElmFunc := fu );
  Gm := GroupWithGenerators(ri!.gensHmem);
  S := StabilizerChain(Gm,opt);
  perms := ActionOnOrbit(S!.orb,ri!.gensHmem);
  SS := StabilizerChain(Group(perms));
  if Size(SS) = Size(S) then
      SetSize(ri,Size(S));
      ri!.stabilizerchain := S;
      Setslptonice(ri,SLPOfElms(StrongGenerators(S)));
      ForgetMemory(S);
      Unbind(S!.opt.RandomElmFunc);
      Setslpforelement(ri,SLPforElementFuncsProjective.StabilizerChainProj);
      SetFilterObj(ri,IsLeaf);
  else
      ForgetMemory(S);
      SetHomom(ri,OrbActionHomomorphism(G,S!.orb));
      Setmethodsforimage(ri,FindHomDbPerm);
  fi;
  return Success;
end);

RECOG.HomProjDet := function(data,m)
  local x;
  x := LogFFE(DeterminantMat(m),data.z);
  if x = fail then
      return fail;
  fi;
  return data.c ^ (x mod data.gcd);
end;

#! @BeginChunk ProjDeterminant
#! The method defines a homomorphism from a projective group <A>G</A><M> \le
#! PGL(d,q)</M> to the cyclic group <M>GF(q)^*/D</M>, where <M>D</M> is the set
#! of <M>d</M>th powers in <M>GF(q)^*</M>. The image of a group
#! element <M>g \in <A>G</A></M> is the determinant of a matrix representative of
#! <M>g</M>, modulo <M>D</M>.
#! @EndChunk
BindRecogMethod(FindHomMethodsProjective, "ProjDeterminant",
"find homomorphism to non-zero scalars mod d-th powers",
function(ri, G)
  local H,c,d,detsadd,f,gcd,hom,newgens,q,z;
  f := ri!.field;
  d := ri!.dimension;
  q := Size(f);
  gcd := GcdInt(q-1,d);
  if gcd = 1 then
      return NeverApplicable;
  fi;
  z := Z(q);
  detsadd := List(GeneratorsOfGroup(G),x->LogFFE(DeterminantMat(x),z) mod gcd);
  if IsZero(detsadd) then
      return NeverApplicable;
  fi;
  Info(InfoRecog,2,"ProjDeterminant: found non-trivial homomorphism.");
  c := PermList(Concatenation([2..gcd],[1]));
  newgens := List(detsadd,x->c^x);
  H := GroupWithGenerators(newgens);
  hom := GroupHomByFuncWithData(G,H,RECOG.HomProjDet,
                                rec(c := c, z := z, gcd := gcd));
  SetHomom(ri,hom);
  Setmethodsforimage(ri,FindHomDbPerm);
  findgensNmeth(ri).args[1] := 8;
  findgensNmeth(ri).args[2] := 5;
  Setimmediateverification(ri,true);
  return Success;
end);

RECOG.IsBlockScalarMatrix := function(blocks, x)
  local b, s;
  if not IsDiagonalMat(x) then
      return false;
  fi;
  for b in blocks do
      s := b[1];
      s := x[s,s];
      if not ForAll(b, pos -> x[pos,pos] = s) then
          return false;
      fi;
  od;
  return true;
end;

# scale the given block-scalar matrix x so that its last block
# is the identity matrix
RECOG.HomNormLastBlock := function(data, x)
  local blocks, pos, s;
  blocks := data!.blocks;
  if not RECOG.IsBlockScalarMatrix(blocks, x) then
      return fail;
  fi;
  pos := blocks[Length(blocks)][1];
  s := x[pos,pos];
  if not IsOne(s) then
      x := s^-1 * x;
  fi;
  return x;
end;

#! @BeginChunk BlockScalarProj
#! This method is only called by a hint. Alongside with the hint it gets
#! a block decomposition respected by the matrix group <A>G</A> to be recognised
#! and the promise that all diagonal blocks of all group elements
#! will only be scalar matrices. This method simply norms the last diagonal
#! block in all generators by multiplying with a scalar and then
#! delegates to <C>BlockScalar</C> (see <Ref Subsect="BlockScalar"/>)
#! and matrix group mode to do the recognition.
#! @EndChunk
BindRecogMethod(FindHomMethodsProjective, "BlockScalarProj",
"TODO",
function(ri, G)
  # We just norm the last block and go to matrix methods.
  local H,data,hom,newgens,g;
  data := rec( blocks := ri!.blocks );
  newgens := [];
  for g in GeneratorsOfGroup(G) do
      g := RECOG.HomNormLastBlock(data, g);
      if g = fail then
          return NeverApplicable;
      fi;
      Add(newgens, g);
  od;
  H := GroupWithGenerators(newgens);
  hom := GroupHomByFuncWithData(G,H,RECOG.HomNormLastBlock,data);
  SetHomom(ri,hom);

  findgensNmeth(ri).method := FindKernelDoNothing;  # This is an iso

  # Switch to matrix mode:
  Setmethodsforimage(ri,FindHomDbMatrix);
  AddMethod(InitialDataForImageRecogNode(ri).hints, FindHomMethodsMatrix.BlockScalar, 2000);
  InitialDataForImageRecogNode(ri).blocks := ri!.blocks{[1..Length(ri!.blocks)-1]};
  return Success;
end);

RECOG.MakeAlternatingMatrixReps := function(deg,f,tens)
  local a,b,gens,gens2,i,m,ogens,r;
  a := AlternatingGroup(deg);
  gens := List(GeneratorsOfGroup(a),x->PermutationMat(x,deg,f));
  ogens := ShallowCopy(gens);
  for i in [1..tens] do
      gens2 := [];
      for i in [1..Length(gens)] do
          Add(gens2,KroneckerProduct(gens[i],ogens[i]));
      od;
      gens := gens2;
  od;
  m := GModuleByMats(gens,f);
  r := MTX.CollectedFactors(m);
  return List(r,x->x[1].generators);
end;

RECOG.MakeSymmetricMatrixReps := function(deg,f,tens)
  local a,b,gens,gens2,i,m,ogens,r;
  a := SymmetricGroup(deg);
  gens := List(GeneratorsOfGroup(a),x->PermutationMat(x,deg,f));
  ogens := ShallowCopy(gens);
  for i in [1..tens] do
      gens2 := [];
      for i in [1..Length(gens)] do
          Add(gens2,KroneckerProduct(gens[i],ogens[i]));
      od;
      gens := gens2;
  od;
  m := GModuleByMats(gens,f);
  r := MTX.CollectedFactors(m);
  return List(r,x->x[1].generators);
end;

# The method installations:

#! @BeginCode AddMethod_Projective_FindHomMethodsGeneric.TrivialGroup
AddMethod(FindHomDbProjective, FindHomMethodsGeneric.TrivialGroup, 3000);
#! @EndCode

AddMethod(FindHomDbProjective, FindHomMethodsProjective.ProjDeterminant, 1300);

AddMethod(FindHomDbPerm, FindHomMethodsGeneric.FewGensAbelian, 1250);

# Note that we *can* in fact use the Matrix method here, because it
# will do the right thing when used in projective mode:
AddMethod(FindHomDbProjective, FindHomMethodsMatrix.ReducibleIso, 1200);

AddMethod(FindHomDbProjective, FindHomMethodsProjective.NotAbsolutelyIrred, 1100);

AddMethod(FindHomDbProjective, FindHomMethodsGeneric.SnAnSmallUnknownDegree, 1075);

AddMethod(FindHomDbProjective, FindHomMethodsGeneric.SnAnUnknownDegree, 1070);

AddMethod(FindHomDbProjective, FindHomMethodsProjective.ClassicalNatural, 1050);

AddMethod(FindHomDbProjective, FindHomMethodsProjective.Subfield, 1000);

AddMethod(FindHomDbProjective, FindHomMethodsProjective.C3C5, 900);

#AddMethod( FindHomDbProjective, FindHomMethodsProjective.Derived,
#   900, "Derived",
#        "restrict to derived subgroup" );
# Superseded by C3C5.

AddMethod(FindHomDbProjective, FindHomMethodsProjective.C6, 850);

AddMethod(FindHomDbProjective, FindHomMethodsProjective.D247, 840);

# # We can do the following early on since it will quickly fail for
# # non-sporadic groups:
# AddMethod(FindHomDbProjective, FindHomMethodsProjective.SporadicsByOrders, 820);

AddMethod(FindHomDbProjective, FindHomMethodsProjective.AltSymBBByDegree, 810);

AddMethod(FindHomDbProjective, FindHomMethodsProjective.TensorDecomposable, 800);

AddMethod(FindHomDbProjective, FindHomMethodsProjective.FindElmOfEvenNormal, 700);

AddMethod(FindHomDbProjective, FindHomMethodsProjective.LowIndex, 600);

AddMethod(FindHomDbProjective, FindHomMethodsProjective.NameSporadic, 580);

AddMethod(FindHomDbProjective, FindHomMethodsProjective.ComputeSimpleSocle, 550);

AddMethod(FindHomDbProjective, FindHomMethodsProjective.ThreeLargeElOrders, 500);

AddMethod(FindHomDbProjective, FindHomMethodsProjective.LieTypeNonConstr, 400);

AddMethod(FindHomDbProjective, FindHomMethodsProjective.StabilizerChainProj, 100);


# Old methods which are no longer used:

#AddMethod( FindHomDbProjective, FindHomMethodsProjective.FindEvenNormal,
#   825, "FindEvenNormal",
#        "find D2, D4 or D7 by finding reducible normal subgroup" );
#AddMethod( FindHomDbProjective, FindHomMethodsProjective.AlternatingBBByOrders,
#   580, "AlternatingBBByOrders",
#        "generate a few random elements and compute the proj. orders" );
