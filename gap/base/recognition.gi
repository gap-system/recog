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
##  The generic code for recognition, implementation part.
##
#############################################################################

BindGlobal("RECOG_FindKernelFastNormalClosureStandardArgumentValues",
           Immutable([6, 3]));
#BindConstant("RECOG_NrElementsInImmediateVerification", 10);
RECOG_NrElementsInImmediateVerification := 10;

# a nice view method:
RECOG_ViewObj := function( level, ri )
    local ms;
    if IsReady(ri) then
        Print("<recognition node ");
    else
        Print("<failed recognition node ");
    fi;
    if IsBound(ri!.projective) and ri!.projective then
        Print("(projective) ");
    fi;
    if Hasfhmethsel(ri) then
        ms := fhmethsel(ri);
        if IsRecord(ms) then
            if IsBound(ms.successMethod) then
                Print(ms.successMethod);
            else
                Print("NO STAMP");
            fi;
        elif IsString(ms) then
            Print(ms);
        fi;
        if IsBound(ri!.comment) then
            Print(" Comment=", ri!.comment);
        fi;
    fi;
    if HasIsRecogInfoForSimpleGroup(ri) and IsRecogInfoForSimpleGroup(ri) then
        Print(" Simple");
    elif HasIsRecogInfoForAlmostSimpleGroup(ri) and IsRecogInfoForAlmostSimpleGroup(ri) then
        Print(" AlmostSimple");
    fi;
    if ri!.crisisLevel > 0 then
    Print(" crisisLevel=", ri!.crisisLevel);
    fi;
    if HasSize(ri) then
        Print(" Size=",Size(ri));
    fi;
    if HasGrp(ri) and IsMatrixGroup(Grp(ri)) then
        Print(" Dim=",ri!.dimension);
        Print(" Field=",Size(ri!.field));
    fi;
    if not IsLeaf(ri) then
        Print("\n",String("",level)," F:");
        if HasImageRecogNode(ri) then
            RECOG_ViewObj(level+3, ImageRecogNode(ri));
        else
            Print("has no image");
        fi;
        Print("\n",String("",level), " K:");
        if HasKernelRecogNode(ri) then
            if KernelRecogNode(ri) = fail then
                Print("<trivial kernel");
            else
                RECOG_ViewObj(level+3, KernelRecogNode(ri));
            fi;
        else
            Print("has no kernel");
        fi;
    fi;
    Print(">");
  end;

InstallMethod( ViewObj, "for recognition nodes", [IsRecogNode],
  function(ri)
    RECOG_ViewObj(0, ri);
  end);


#############################################################################
# The main recursive function:
#############################################################################

InstallGlobalFunction( RecognisePermGroup,
  function(G)
    return RecogniseGeneric(G, FindHomDbPerm, "", rec(), fail, true);
  end);

InstallGlobalFunction( RecogniseMatrixGroup,
  function(G)
    return RecogniseGeneric(G, FindHomDbMatrix, "", rec(), fail, true);
  end);

InstallGlobalFunction( RecogniseProjectiveGroup,
  function(G)
    return RecogniseGeneric(G, FindHomDbProjective, "", rec(), fail, true);
  end);

InstallGlobalFunction( RecogniseGroup,
  function(G)
    if IsPermGroup(G) then
        return RecogniseGeneric(G, FindHomDbPerm, "", rec(), fail, true);
    elif IsMatrixGroup(G) then
        return RecogniseGeneric(G, FindHomDbMatrix, "", rec(), fail, true);
    else
        ErrorNoReturn("Only matrix and permutation groups are supported");
    fi;

# TODO: perhaps check if the result does not have IsReady set;
# in that case print a warning or error or ...?

    # Note: one cannot use "RecogniseGroup" to recognise projective groups
    #       as of now since "Projective groups" do not yet exist as GAP
    #       objects here!
  end);

# TODO: TryFindHomMethod is never called by anything
# in recog.
# Seems to be for user intervention and/or debugging?
# If so, document it accordingly. Otherwise remove it!
InstallGlobalFunction( TryFindHomMethod,
  function( g, method, projective )
    local result,ri;
    ri := RecogNode(g,projective);
    Unbind(g!.pseudorandomfunc);
    result := method(ri,g);
    if result in [TemporaryFailure, NeverApplicable] then
        return result;
    else
        SetFilterObj(ri,IsReady);
        Setfhmethsel(ri,"User");
        return ri;
    fi;
  end );

InstallMethod( RecogNode,
  "standard method",
  [ IsGroup, IsBool, IsRecord ],
  function(H,projective,r)
    local ri;
    ri := ShallowCopy(r);
    Objectify( RecogNodeType, ri );
    SetGrp(ri,H);
    # Used by RecogCrisis
    if not IsBound(ri!.crisisLevel) then
        ri!.crisisLevel := 0;
    fi;
    Setslpforelement(ri,SLPforElementGeneric);
    SetgensN(ri,[]);       # this will grow over time
    Setimmediateverification(ri,false);
    # this is eventually handed down to the kernel
    SetInitialDataForKernelRecogNode(
        ri,
        rec(hints := [], crisisLevel := ri!.crisisLevel)
    );
    # this is eventually handed down to the image
    SetInitialDataForImageRecogNode(
        ri,
        rec(hints := [], crisisLevel := ri!.crisisLevel)
    );
    if projective then
        Setisone(ri,IsOneProjective);
        Setisequal(ri,IsEqualProjective);
        SetOrderFunc(ri, RECOG.ProjectiveOrder);
    else
        Setisone(ri,IsOne);
        Setisequal(ri,\=);
        SetOrderFunc(ri, Order);
    fi;
    Setdocommute(ri, function(x,y)
      local a,b;
      a := StripMemory(x);
      b := StripMemory(y);
      return isequal(ri)(a*b, b*a);
    end);
    ri!.projective := projective;
    # FIXME: perhaps DON'T set a default for findgensNmeth, to ensure
    # people always set a value? Or at least find some way so that
    # methods must explicitly acknowledge that they want the default...
    SetfindgensNmeth(
        ri,
        rec(method := FindKernelFastNormalClosure,
            args := ShallowCopy(RECOG_FindKernelFastNormalClosureStandardArgumentValues))
    );
    if IsMatrixGroup(H) then
        ri!.field := FieldOfMatrixGroup(H);
        ri!.dimension := DimensionOfMatrixGroup(H);
    fi;
    ri!.pr := ProductReplacer(GeneratorsOfGroup(H));
    ri!.gensHmem := GeneratorsWithMemory(GeneratorsOfGroup(H));
    ri!.prodrep := ProductReplacer(ri!.gensHmem, rec( maxdepth := 400 ));
    # The purpose of the following components is to use the components randr
    # and rando as the central places where random elements and their orders
    # can be stored.
    #
    # randr stores the random elements computed by RandomElm and RandomElmOrd
    ri!.randr := EmptyPlist(100);
    # If the order of a random element is computed by RandomElmOrd or if the
    # order of an entry of randr is computed by GetElmOrd, then the order is
    # saved into rando.
    ri!.rando := EmptyPlist(100);
    # randrpt stores for each stamp how often it was used to generate a random
    # element.
    ri!.randrpt := rec();
    # randopt stores for each stamp how often it was used to generate a random
    # order.
    ri!.randopt := rec();
    ri!.randstore := true;
    # randp and randppt were used to store ppd elements. Currently unused.
    #ri!.randp := EmptyPlist(100);
    #ri!.randppt := rec();
    H!.pseudorandomfunc := [rec(func := function(ri,name,bool)
                                          return RandomElm(ri,name,bool).el;
                                        end,
                                args := [ri,"PseudoRandom",false])];
    return ri;
  end );

InstallOtherMethod( RecogNode,
  "for a group",
  [ IsGroup ],
  function(H)
    return RecogNode(H, false, rec());
  end );

InstallOtherMethod( RecogNode,
  "for a group and a boolean",
  [ IsGroup, IsBool ],
  function(H, projective)
    return RecogNode(H, projective, rec());
  end );


# Sets the stamp used by RandomElm, RandomElmOrd, and related functions.
RECOG.SetPseudoRandomStamp := function(g,st)
  if IsBound(g!.pseudorandomfunc) then
      g!.pseudorandomfunc[Length(g!.pseudorandomfunc)].args[2] := st;
  fi;
end;

# RandomElm and RandomElmOrd take a recog record, a string, and a
# bool as inputs.
# The string is used as a stamp to request a random element or order for a
# specific computation. RandomElm and RandomElmOrd will first try to reuse
# random elements and orders generated with different stamps.
# For example, if a computation which used stamp := "A" has already computed
# random elements or orders, then RandomElm and RandomElmOrd will reuse these
# if called with stamp := "B".
#
# The components of the recog record involved are explained in
# RecogNode.
#
# HACK: For recog records created by RecogNode the method
# RandomElm is by default stored in the component ri!.Grp!.pseudorandomfunc.
# A method for PseudoRandom is installed such that it calls
# RandomElm(ri, "PseudoRandom", false).
InstallMethod( RandomElm, "for a recognition node, a string and a bool",
  [ IsRecogNode, IsString, IsBool ],
  function(ri, stamp, mem)
    local pos, el, res;
    if ri!.randstore then
        if IsBound(ri!.randrpt.(stamp)) then
            ri!.randrpt.(stamp) := ri!.randrpt.(stamp) + 1;
        else
            ri!.randrpt.(stamp) := 1;
        fi;
        pos := ri!.randrpt.(stamp);
        if not IsBound(ri!.randr[pos]) then
            ri!.randr[pos] := Next(ri!.prodrep);
        fi;
        el := ri!.randr[pos];
    else
        el := Next(ri!.prodrep);
    fi;
    res := rec();
    if mem then
        res.el := el;
    else
        res.el := el!.el;
    fi;
    if ri!.randstore then
        res.nr := pos;
    fi;
    return res;
  end );

# For an explanation see RandomElm.
InstallMethod( RandomElmOrd,
  "for a recognition node, a string and a bool",
  [ IsRecogNode, IsString, IsBool ],
  function(ri, stamp, mem)
    local pos,res;
    if ri!.randstore then
        if IsBound(ri!.randopt.(stamp)) then
            ri!.randopt.(stamp) := ri!.randopt.(stamp) + 1;
        else
            ri!.randopt.(stamp) := 1;
        fi;
        pos := ri!.randopt.(stamp);
        if not IsBound(ri!.rando[pos]) then
            if not IsBound(ri!.randr[pos]) then
                ri!.randr[pos] := Next(ri!.prodrep);
            fi;
            ri!.rando[pos] := OrderFunc(ri)(ri!.randr[pos]!.el);
        fi;
        res := rec( order := ri!.rando[pos], projective := ri!.projective,
                    el := ri!.randr[pos] );
    else
        res := rec( el := Next(ri!.prodrep) );
        res.order := OrderFunc(ri)(res.el!.el);
        res.projective := ri!.projective;
        Add(ri!.rando,res.order);
    fi;
    if not mem then
        res.el := res.el!.el;
    fi;
    return res;
  end );

# GetElmOrd takes a recognition node and a record r. The record r
# typically is created by RandomElm and represents a random element of Grp(ri).
# If ri!.randstore is true this function tries to look up or computes and
# stores the order in ri.
InstallMethod( GetElmOrd, "for a recognition node and a record",
  [ IsRecogNode, IsRecord ],
  function( ri, r )
    local x;
    if ri!.randstore then
        if IsBound(ri!.rando[r.nr]) then
            r.order := ri!.rando[r.nr];
        else
            ri!.rando[r.nr] := OrderFunc(ri)(ri!.randr[r.nr]!.el);
            r.order := ri!.rando[r.nr];
        fi;
    else
        x := StripMemory(r.el);
        r.order := OrderFunc(ri)(x);
    fi;
  end );

# FIXME: unused?
# InstallMethod( RandomElmPpd,
#   "for a recognition node, a string and a bool",
#   [ IsRecogNode, IsString, IsBool ],
#   function(ri, s, mem)
#     local pos,res;
#     if ri!.randstore then
#         if not IsBound(ri!.randppt.(s)) then
#             ri!.randppt.(s) := 1;
#             pos := 1;
#         else
#             ri!.randppt.(s) := ri!.randppt.(s) + 1;
#             pos := ri!.randppt.(s);
#         fi;
#         if not IsBound(ri!.randp[pos]) then
#             if not IsBound(ri!.randr[pos]) then
#                 ri!.randr[pos] := Next(ri!.prodrep);
#             fi;
#             if not IsMatrix(ri!.randr[pos]) then
#                 ErrorNoReturn("ppd elements only make sense for matrices");
#             fi;
#             res := rec( el := ri!.randr[pos] );
#             res.charpoly := CharacteristicPolynomial(ri!.field,ri!.field,
#                                                      res.el!.el,1);
#             res.factors := Factors(PolynomialRing(ri!.field), res.charpoly);
#             res.degrees := List(res.factors,Degree);
#             res.degset := Set(res.degrees);
#             ri!.randp[pos] := ShallowCopy(res);
#             Unbind(ri!.randp[pos].el);
#         else
#             res := ShallowCopy(ri!.randp[pos]);
#             res.el := ri!.randr[pos];
#         fi;
#     else
#         res := rec( el := Next(ri!.prodrep) );
#         res.charpoly := CharacteristicPolynomial(ri!.field,ri!.field,
#                                                  res.el!.el,1);
#         res.factors := Factors(PolynomialRing(ri!.field), res.charpoly);
#         res.degrees := List(res.factors,Degree);
#         res.degset := Set(res.degrees);
#     fi;
#     if not mem then
#         res.el := res.el!.el;
#     fi;
#     return res;
#   end );

# FIXME: unused?
# InstallMethod( GetElmPpd, "for a recognition node and a record",
#   [ IsRecogNode, IsRecord ],
#   function( ri, r )
#     local x;
#     if IsObjWithMemory(r.el) then
#         x := r.el!.el;
#     else
#         x := r.el;
#     fi;
#     if ri!.randstore and r.nr > 0 then
#         if not IsBound(ri!.randp[r.nr]) then
#             r.charpoly := CharacteristicPolynomial(ri!.field,ri!.field,x,1);
#             r.factors := Factors(PolynomialRing(ri!.field), r.charpoly);
#             r.degrees := List(r.factors,Degree);
#             r.degset := Set(r.degrees);
#             ri!.randp[r.nr] := ShallowCopy(r);
#             Unbind(ri!.randp[r.nr].el);
#             Unbind(ri!.randp[r.nr].nr);
#         else
#             r.charpoly := ri!.randp[r.nr].charpoly;
#             r.factors := ri!.randp[r.nr].factors;
#             r.degrees := ri!.randp[r.nr].degrees;
#             r.degset := ri!.randp[r.nr].degset;
#         fi;
#     else
#         r.charpoly := CharacteristicPolynomial(ri!.field,ri!.field,x,1);
#         r.factors := Factors(PolynomialRing(ri!.field), r.charpoly);
#         r.degrees := List(r.factors,Degree);
#         r.degset := Set(r.degrees);
#     fi;
#   end );

InstallMethod( RandomOrdersSeen, "for a recognition node",
  [ IsRecogNode ],
  function(ri)
    return Compacted(ri!.rando);
  end );

# FIXME: unused?
# InstallMethod( StopStoringRandEls, "for a recognition node",
#   [ IsRecogNode ],
#   function(ri)
#     ri!.randstore := false;
#     Unbind(ri!.randr);
#     Unbind(ri!.randp);
#     Unbind(ri!.randrpt);
#     Unbind(ri!.randopt);
#     Unbind(ri!.randppt);
#     ri!.rando := Compacted(ri!.rando);
#     # Note that we keep the random element orders seen!
#   end );

InstallGlobalFunction( PrintTreePos,
  function(mark,depthString,H)
    if InfoLevel(InfoRecog) = 1 then
        if IsMatrixGroup(H) then
            Print(mark," dim=",String(DimensionOfMatrixGroup(H),4),
                  " field=",Size(FieldOfMatrixGroup(H))," ",
                  String(Length(depthString),2)," ",depthString,"   \r");
        elif IsPermGroup(H) then
            Print(mark," pts=",String(LargestMovedPoint(H),6)," ",
                  String(Length(depthString),2)," ",depthString,"   \r");
        else
            Print(mark," ",String(Length(depthString),2)," ",depthString,"   \r");
        fi;
    fi;
  end );

BindGlobal("TryToEnlargeKernelGeneratingSetAndUpdateSLPsDuringMandarinCrisis",
function(ri, crisis)
    local gensNWasEmpty, targetNrGensN, kernelGenerationSuccess;
    Print("Handling Mandarin Crisis!\n");
    gensNWasEmpty := IsEmpty(gensN(ri));
    if gensNWasEmpty then
        # The following value was chosen arbitrarily. It gets reduced during
        # each iteration to a minimal value of 1, to account for the case where
        # the kernel only has two elements. The findgensNmeth might discard
        # trivial or duplicate generators. In that case we can never find more
        # than one generator, if the kernel has size two.
        targetNrGensN := 5;
    else
        # The goal is to obtain twice as many generators as were in gensN. The
        # kernel generation methods write directly into gensN and don't provide
        # a means to specify how many generators should be created. Also, they
        # might not add a newly created generator, if that one already is in
        # gensN. If that happens when enlarging a kernel generating set for the
        # first time and we set the factor below to 2, we might call the
        # findgensNmeth a second time, tripling instead of doubling the size of
        # the generating set.
        targetNrGensN := Int(1.9 * Length(gensN(ri)));
    fi;
    Info(InfoRecog, 2,
         "Enlarging the kernel's generating set due to a mandarin crisis.");
    repeat
        # It might happen that we enlarge the wrong kernel. If in addition the
        # kernel is very small, we might never stop looking for new generators,
        # unless we successively reduce targetNrGensN.
        targetNrGensN := targetNrGensN - 1;
        # Create additional kernel generators with the stored method:
        # kernelGenerationSuccess is either true or fail.
        kernelGenerationSuccess :=
            CallFuncList(findgensNmeth(ri).method,
                         Concatenation([ri],findgensNmeth(ri).args));
        if kernelGenerationSuccess = fail then
            return false;
        fi;
    until Length(gensN(ri)) >= targetNrGensN;
    SetgensNslp(ri,SLPOfElms(gensN(ri)));
    SlotUsagePattern(gensNslp(ri));
    ri!.crisisLevel := crisis!.level;
    InitialDataForImageRecogNode(ri).crisisLevel := crisis!.level;
    InitialDataForKernelRecogNode(ri).crisisLevel := crisis!.level;
    return true;
end);

# Create an IsRecogCrisis object. The argument `ri` must have a
# ParentRecogNode. A crisis can have level 1 or level 2.
# The higher the level, the more we chop off of the tree.
# How is the level of a new crisis determined? If on the path to the root there
# is no node marked KernelGeneratorsAlreadyEnlargedByCrisis, then we throw a
# level 1 crisis. Otherwise we throw a level 2 crisis.
# Why is it sufficient to only check the path to the root? If we were too
# conservative by not backtracking all the way to the first IsSafeForMandarins
# node and instead only backtracked to a node X, then recognising X must again
# throw a crisis. Thus node X will be on the path to the root.
InstallMethod(RecogCrisis,
"for an IsRecogNode",
[IsRecogNode],
function(ri)
    local isKernelNode, unsafeKernelsOnPathToRoot, node, highLevel, lowLevel,
        isSmallCrisis, level, i, kernelToChop, result;
    # This is never called on the root:
    isKernelNode :=
        x -> HasKernelRecogNode(ParentRecogNode(x))
            and IsIdenticalObj(x, KernelRecogNode(ParentRecogNode(x)));
    # Find unsafe kernel nodes on the path to root
    unsafeKernelsOnPathToRoot := [];
    node := ri;
    repeat
        if isKernelNode(node) then
            Add(unsafeKernelsOnPathToRoot, node);
        fi;
        node := ParentRecogNode(node);
    # The root is always safe, so this loop terminates.
    until IsSafeForMandarins(node);
    # Now unsafeKernelsOnPathToRoot must be non-empty
    Print(List(unsafeKernelsOnPathToRoot, y -> ParentRecogNode(y)!.crisisLevel), "\n");
    # Determine whether to return a small crisis, that is whether to cut low.
    # If unsafeKernelsOnPathToRoot has length one, there is no difference
    # between a small and a big crisis, so we don't need to special case it.
    highLevel := unsafeKernelsOnPathToRoot[Length(unsafeKernelsOnPathToRoot)]!.crisisLevel;
    lowLevel := ri!.crisisLevel;
    isSmallCrisis := lowLevel = highLevel;
    # TODO: fix description how levels are determined.
    # We distinguish two types of crises. Either the level is one, or the level
    # is greater or equal than two. We call the crisis of the latter kind a big
    # crisis. In case of such a big crisis the recognition algorithm backtracks
    # all the way to the topmost unsafe kernel on the way to the root and
    # chopping it off. A level one crisis only backtracks part of the way and
    # thus chops off a smaller subtree than big crises.
    # TODO: describe that this level is propagated downwards to all *newly*
    # created nodes. but only on the kernel side of the marked node! Thus it
    # might be, that on a path to the root, the level is not strictly
    # increasing.
    # TODO TODO actually, I need to propagate it to everything? I had an
    # example run taking 135 s instead of 2 s. Also, if a node is marked, then
    # its kernel node is chopped off and that tree is recomputed, the tree
    # rooted in the image node must have been completely recognized.
    # TODO thus say above,
    # that each node is initialized with a "crisisLevelSeen". 
    # The parent of the kernel which is chopped off stores the crisis level.
    # Note that for a fixed node, these are strictly increasing.
    #   TODO: explain that
    # the crisis level of a node determines how often findgensNmeth is called,
    # namely 2 ^ crisisLevel many times.
    #   If no node on the way to the root was marked by a level one crisis, we
    # always throw a level one crisis. Otherwise we take the highest crisis
    # level seen by the topmost unsafe kernel and increase it by one. Note that
    # once a node is marked by a big crisis, the next crisis triggered in the
    # new subtree rooted in its newly constructed kernel node will again be a
    # level one crisis, since no node will have been marked by a level one
    # crisis yet.
    #   In a newly constructed subtree we always first spawn a level one
    # crisis, to conservatively chop off part of the recognition tree.
    # should small crises increase level?
    #0
    #1
    #2
    #
    #0 0 0 0
    #-> 1, low
    #
    #0 0 1 1
    #-> 1, high
    #
    #1 1 1 1
    #-> 2, low
    #
    #1 1 2 2
    #-> 2, high
    #
    #2 2 2 2
    level := highLevel + 1;
    Info(InfoRecog, 1, "Crisis level=", level, ", small=", isSmallCrisis, ".");
    # Determine kernelToChop
    if isSmallCrisis then
        i := Maximum(1, QuoInt(1 + Length(unsafeKernelsOnPathToRoot), 2));
    else
        i := Length(unsafeKernelsOnPathToRoot);
    fi;
    kernelToChop := unsafeKernelsOnPathToRoot[i];
    result := rec(kernelToChop := kernelToChop, level := level);
    Objectify(RecogCrisisType, result);
    return result;
end);

# This is a hack to handle the case where the kernel is trivial and thus
# instead of a RecogNode, a "fail" is put into the tree.
InstallOtherMethod(RecogCrisis,
"for a boolean and an IsRecogNode",
[IsBool, IsRecogNode],
function(trivialKernel, parent)
    local fakeNode, result;
    if not trivialKernel = fail then
        ErrorNoReturn("<trivialKernel> must be fail but is ", trivialKernel);
    fi;
    fakeNode := RecogNode(Group(()));
    SetParentRecogNode(fakeNode, parent);
    SetKernelRecogNode(parent, fakeNode);
    result := RecogCrisis(fakeNode);
    SetKernelRecogNode(parent, fail);
    if IsIdenticalObj(result!.kernelToChop, fakeNode) then
        result!.kernelToChop := fail;
    fi;
    return result;
end);

# TODO, disable this to run test suite.
InstallOtherMethod( RecogniseGeneric,
"compatibility method",
[ IsGroup, IsObject, IsString, IsRecord, IsObject, IsBool ],
function(H, methoddb, depthString, knowledge, mandarins, isSafeForMandarins)
    local ri;
    # RecogNode calls ProductReplacer, which needs to have at least one
    # generator.
    if Length(GeneratorsOfGroup(H)) = 0 then
        H := Group([One(H)]);
    fi;
    ri := RecogNode(
        H,
        IsIdenticalObj( methoddb, FindHomDbProjective ),
        knowledge
    );
    RecogniseGeneric(ri, methoddb, depthString,
                     mandarins, isSafeForMandarins);
    return ri;
end);

# TODO: Update docs: new return value: crisis or true
# TODO: Rename this into RecogniseRecogNode
# TODO: isSafeForMandarins could be put into the RecogNode call, then we can
# remove it here.
InstallMethod( RecogniseGeneric,
"TODO",
[ IsRecogNode, IsObject, IsString, IsObject, IsBool ],
function(ri, methoddb, depthString, mandarins, isSafeForMandarins)
    local depth, H, allmethods, mandarinSLPs, s, imageMandarins, y,
        counter_image, rifac, imageStatus, kernelGenerationSuccess, l, ll,
        kernelMandarins, crisis, kernelMandarinSuccess,
        immediateVerificationSuccess, N, riker, kernelStatus, x,
        nrNiceGensOfImageNode, i;
    # Assume all the generators have no memory!

    depth := Length(depthString);
    H := Grp(ri);

    PrintTreePos("E",depthString,H);
    Info(InfoRecog,4,"Recognising: ",H);

    if Length(GeneratorsOfGroup(H)) = 0 then
        # FIXME: shouldn't we just, like, finish here immediately?
        H := Group([One(H)]);
    fi;

    if mandarins = fail then
        Assert(0, depth = 0);
        # HACK: We don't want the mandarins to be reused by any computation.
        # Since PseudoRandom is hacked, it is important that we generate the
        # mandarins before calling RecogNode. Otherwise the mandarins would be
        # reused by RandomElm and RandomElmOrd.
        # TODO: enable passing NUM_MANDARINS as optional arg
        mandarins := List([1..NUM_MANDARINS_DEFAULT_VALUE], i -> PseudoRandom(H));
    fi;
    ri!.mandarins := mandarins;
    if isSafeForMandarins then
        SetFilterObj(ri, IsSafeForMandarins);
    fi;

    # was here earlier: Setcalcnicegens(ri,CalcNiceGensGeneric);

    Setmethodsforimage(ri,methoddb);

    # Combine database of find homomorphism methods with hints
    allmethods := methoddb;
    if IsBound(ri!.hints) then
        allmethods := Concatenation(allmethods, ri!.hints);
        SortBy(allmethods, a -> -a.rank);
    fi;
    # verify no rank occurs more than once
    Assert(0, Length(Set(allmethods, m->m.rank)) = Length(allmethods));

    # Find a possible homomorphism (or recognise this group as leaf)
    Setfhmethsel(ri, CallMethods( allmethods, 10, ri, H ));
    # TODO: extract the value 10 into a named constant, and / or make it
    #       an option parameter to the func

    # Reset the pseudo random stamp:
    RECOG.SetPseudoRandomStamp(Grp(ri),"PseudoRandom");

    # Handle the unfinished case:
    if fhmethsel(ri).result = TemporaryFailure then
        SetFilterObj(ri,IsLeaf);
        if InfoLevel(InfoRecog) = 1 and depth = 0 then Print("\n"); fi;
        Info(InfoRecog, 1,
             "RecogNode <ri> could not be recognised,",
             " IsReady(<ri>) is not set, recognition aborts");
        return true;
    fi;

    # Handle the leaf case:
    if IsLeaf(ri) then
        # If nobody has set how we produce preimages of the nicegens:
        if not Hascalcnicegens(ri) then
            Setcalcnicegens(ri,CalcNiceGensGeneric);
        fi;
        if Hasslptonice(ri) then
            SlotUsagePattern(slptonice(ri));
        fi;
        # Handle the case that nobody set nice generators:
        if not HasNiceGens(ri) then
            if Hasslptonice(ri) then
                SetNiceGens(ri,ResultOfStraightLineProgram(slptonice(ri),
                                            GeneratorsOfGroup(H)));
            else
                # FIXME: is this a good idea???
                # maybe an error would be better for debugging
                SetNiceGens(ri,GeneratorsOfGroup(H));
            fi;
        fi;

        # Check mandarins and compute their SLPs in the nice generators of ri.
        Info(InfoRecog, 3, "Check mandarins (leaf, depth=", depth,").");
        mandarinSLPs := [];
        for x in mandarins do
            s := SLPforElement(ri, x);
            if s = fail then
                Info(InfoRecog, 1,
                     "Enter mandarin crisis (leaf, depth=", depth, ").");
                return RecogCrisis(ri);
            fi;
            Add(mandarinSLPs, s);
        od;
        ri!.mandarinSLPs := mandarinSLPs;

        if InfoLevel(InfoRecog) = 1 and depth = 0 then Print("\n"); fi;
        # StopStoringRandEls(ri);
        SetFilterObj(ri,IsReady);
        return true;
    fi;

    # The non-leaf case:
    # In that case we know that ri now knows: homom plus additional data.

    if ForAny(GeneratorsOfGroup(H), x->not ValidateHomomInput(ri, x)) then
        # We just computed the homomorphism using exactly those generators.
        ErrorNoReturn("Can't map generators of <H> under the homomorphism",
                      " Homom(<ri>): ValidateHomomInput failed");
    fi;

    # Check that the mandarins can be mapped under the homomorphism. If this
    # fails, then somewhere higher up in the recognition tree, a kernel must
    # have been too small.
    if ForAny(mandarins, x->not ValidateHomomInput(ri, x)) then
        Info(InfoRecog, 1,
             "Enter mandarin crisis (depth=", depth, "), ",
             "ValidateHomomInput failed.");
        return RecogCrisis(ri);
    fi;
    # Compute the mandarins of the factor
    imageMandarins := [];
    for x in mandarins do
        y := ImageElm(Homom(ri), x);
        Assert(2, y <> fail);
        Add(imageMandarins, y);
    od;
    # TODO: sort (?) the imageMandarins and handle duplicates and trivials

    # Recognise the image and build the kernel.
    counter_image := 1;
    repeat
        if counter_image > 2 then
            # We enter here, if kernelGenerationSuccess was fail twice in
            # a row. The value of kernelGenerationSuccess is fail, if
            # writing of a random element of the image as an SLP in its nice
            # generators failed and thus somewhere below the image node rifac
            # there is a too small kernel, which the Mandarins didn't catch.
            # This should be super seldom.
            # Maybe this can happen more often when, deep in the tree, the
            # Mandarins are very few?
            if InfoLevel(InfoRecog) = 1 and depth = 0 then Print("\n"); fi;
            Info(InfoRecog, 1,
                 "Kernel generation for RecogNode <ri> failed ",
                 counter_image, " times, ",
                 " IsReady(<ri>) is not set, recognition aborts");
            return true;
        fi;

        if IsMatrixGroup(Image(Homom(ri))) then
            Info(InfoRecog,2,"Going to the image (depth=",depth,", try=",
              counter_image,", dim=",DimensionOfMatrixGroup(Image(Homom(ri))),
              ", field=",Size(FieldOfMatrixGroup(Image(Homom(ri)))),").");
        else
            Info(InfoRecog,2,"Going to the image (depth=",depth,", try=",
              counter_image,").");
        fi;

        rifac := RecogNode(
                  Group(List(GeneratorsOfGroup(H), x->ImageElm(Homom(ri),x))),
                  IsIdenticalObj(methodsforimage(ri), FindHomDbProjective),
                  InitialDataForImageRecogNode(ri));
        SetImageRecogNode(ri,rifac);
        SetParentRecogNode(rifac,ri);
        Add(depthString,'F');
        # TODO Change return value
        imageStatus := RecogniseGeneric(
                  rifac,
                  methodsforimage(ri),
                  depthString,
                  imageMandarins,
                  IsSafeForMandarins(ri));
        Remove(depthString);
        PrintTreePos("F",depthString,H);
        if IsRecogCrisis(imageStatus) then
            # According to the mandarins, somewhere higher up in the recognition
            # tree, a kernel must have been too small.
            Info(InfoRecog, 2,
                 "Backtrack to the last safe node (depth=", depth, ").");
            return imageStatus;
        fi;
        if not IsReady(rifac) then
            # IsReady was not set, thus abort the whole computation.
            if InfoLevel(InfoRecog) = 1 and depth = 0 then Print("\n"); fi;
            return true;
        fi;

        if IsMatrixGroup(H) then
            Info(InfoRecog,2,"Back from image (depth=",depth,
                 ", dim=",ri!.dimension,", field=",
                 Size(ri!.field),").");
        else
            Info(InfoRecog,2,"Back from image (depth=",depth,").");
        fi;

        # Now we want to have preimages of the new generators in the image:
        Info(InfoRecog,2,"Calculating preimages of nice generators.");
        ri!.pregensfacwithmem := CalcNiceGens(rifac, ri!.gensHmem);
        Setpregensfac(ri, StripMemory(ri!.pregensfacwithmem));

        # Now create the kernel generators with the stored method:
        # The value of kernelGenerationSuccess is either true or fail.
        # A non-zero crisisLevel means that somewhere above us a kernel
        # had to be chopped off due to a crisis. Thus we create more kernel
        # generators.
        # We tested running findgensNmeth 2 ^ ri!.crisisLevel times on
        # the "big imprimitive wreath product" test case (TODO explain what
        # that is).
        # Using 2 ^ level was inferior to using 2 * level.
        # TODO, drop the 2 *: Using 2 ^ level was inferior to using level.
        # TODO: test running findgensNmeth 2 ^ ri!.crisisLevel times
        # with improved findgensNmeth args. 
        # TODO: why doesn't this throw a crisis?
        kernelGenerationSuccess := true;
        for i in [1 .. 1 + ri!.crisisLevel] do
            kernelGenerationSuccess := kernelGenerationSuccess
                and (true = CallFuncList(findgensNmeth(ri).method,
                                         Concatenation([ri],findgensNmeth(ri).args)));
        od;
    until kernelGenerationSuccess = true;

    # If nobody has set how we produce preimages of the nicegens:
    if not Hascalcnicegens(ri) then
        Setcalcnicegens(ri,CalcNiceGensHomNode);
    fi;

    # Do a little bit of preparation for the generators of N:
    if not IsBound(ri!.leavegensNuntouched) then
        l := gensN(ri);
        Sort(l,SortFunctionWithMemory);   # this favours "shorter" memories!
        # FIXME: For projective groups different matrices might stand
        #        for the same element, we might overlook this here!
        # remove duplicates and trivial entries:
        ll := [];
        for i in [1..Length(l)] do
            if not isone(ri)(l[i]) and
               (i = 1 or not isequal(ri)(l[i],l[i-1])) then
                Add(ll,l[i]);
            fi;
        od;
        SetgensN(ri,ll);
    fi;

    # Build kernel mandarins
    kernelMandarins := List(
        [1..Length(mandarins)],
        i -> mandarins[i]
            # Divide by a preimage of its image under Homom(ri).
            / ResultOfStraightLineProgram(rifac!.mandarinSLPs[i], pregensfac(ri))
    );
    # TODO: sort(?) the kernelMandarins and handle duplicates and trivials

    if IsEmpty(gensN(ri)) and immediateverification(ri) then
        # Special case, for an explanation see the source of the called function.
        RECOG_HandleSpecialCaseKernelTrivialAndMarkedForImmediateVerification(ri);
    fi;
    # If no kernel generators were found, check that the mandarins agree that
    # the kernel is trivial.
    if IsEmpty(gensN(ri))
            # HACK: something is suuper iffy about the method BlocksModScalars,
            # see the comment at the "check mandarins" part of the non-leaf case.
            and not fhmethsel(ri).successMethod in ["BlocksModScalars", "BlockScalar"]
            and ForAny(kernelMandarins, x -> not ri!.isone(x)) then
        Info(InfoRecog, 1,
             "Enter mandarin crisis (depth=", depth, "), ",
             "kernel can't be trivial.");
        # We handle this in the same way as if recognition of the
        # kernel threw a crisis.
        crisis := RecogCrisis(fail, ri);
        if crisis!.kernelToChop <> fail then
            return crisis;
        else
            Info(InfoRecog, 2,
                 "Handle the mandarin crisis (depth=", depth, ").");
            if not TryToEnlargeKernelGeneratingSetAndUpdateSLPsDuringMandarinCrisis(ri, crisis) then
                # TODO: discard and re-recognise the image.
                ErrorNoReturn("TODO");
            fi;
        fi;
    fi;
    if IsEmpty(gensN(ri)) then
        # We only enter this case, if the mandarins agreed that the kernel is
        # trivial. Set the kernel to fail to indicate that it is trivial.
        Info(InfoRecog,2,"Found trivial kernel (depth=",depth,").");
        SetKernelRecogNode(ri,fail);
        # We have to learn from the image, what our nice generators are:
        SetNiceGens(ri,pregensfac(ri));
        # Since the kernel is trivial, evaluating the image's mandarinSLPs in
        # pregensfac(ri) must yield the mandarins of the current node.
        # Since the mandarins agree that the kernel is trivial, the current
        # node can't be IsSafeForMandarins and we can ignore that case.
        ri!.mandarinSLPs := ShallowCopy(rifac!.mandarinSLPs);
        for i in [1..Length(mandarins)] do
            x := mandarins[i];
            s := ri!.mandarinSLPs[i];
            if not isequal(ri)(x, ResultOfStraightLineProgram(s, NiceGens(ri)))
                    # HACK: something is suuper iffy about the method BlocksModScalars,
                    # see the comment at the "check mandarins" part of the non-leaf case.
                    and fhmethsel(ri).successMethod <> "BlocksModScalars" then
                # TODO remove
                return MANDARIN_CRISIS;
            fi;
        od;
        if InfoLevel(InfoRecog) = 1 and depth = 0 then Print("\n"); fi;
        # StopStoringRandEls(ri);
        SetFilterObj(ri,IsReady);
        return true;
    fi;

    # Due to mandarins or immediate verification we may have to enlarge gensN
    # and then recognise the kernel again.
    repeat
        kernelMandarinSuccess := false;
        immediateVerificationSuccess := false;

        SetgensNslp(ri,SLPOfElms(gensN(ri)));
        SlotUsagePattern(gensNslp(ri));

        # This is now in terms of the generators of H!
        N := Group(StripMemory(gensN(ri)));

        Info(InfoRecog,2,"Going to the kernel (depth=",depth,").");
        riker := RecogNode(N,
                           # TODO!! safeguard this against changed method dbs
                           # TODO custom_decide_whether_db_is_projectiv
                           IsIdenticalObj(methoddb, FindHomDbProjective),
                           InitialDataForKernelRecogNode(ri));
        SetKernelRecogNode(ri,riker);
        SetParentRecogNode(riker,ri);
        Add(depthString,'K');
        kernelStatus := RecogniseGeneric( riker, methoddb, depthString,
                                   kernelMandarins,
                                   # TODO: extend this such that riker can also
                                   # be IsSafeForMandarins, if the responsible
                                   # findgensNmeth is guaranteed to find the
                                   # generators for the whole kernel.
                                   false);
        Remove(depthString);
        PrintTreePos("K",depthString,H);
        if IsRecogCrisis(kernelStatus) then
            # According to the mandarins, there was an error in the kernel
            # generation of the current node or higher up in the recognition
            # tree.
            if not IsIdenticalObj(kernelStatus!.kernelToChop, riker) then
                Info(InfoRecog, 2,
                     "Backtrack further (depth=", depth, ").");
                return kernelStatus;
            fi;
            Info(InfoRecog, 2,
                 "Handle the mandarin crisis (depth=", depth, ").");
            # We are the first safe node on the way to the root and thus need to
            # handle the crisis ourselves.
            if not TryToEnlargeKernelGeneratingSetAndUpdateSLPsDuringMandarinCrisis(ri, kernelStatus) then
                # TODO: discard and re-recognise the image.
                ErrorNoReturn("TODO");
            fi;
            # This restarts the loop, since kernelMandarinSuccess is false.
            continue;
        fi;
        kernelMandarinSuccess := true;
        Info(InfoRecog,2,"Back from kernel (depth=",depth,").");

        if not IsReady(riker) then
            # IsReady is not set, thus the whole computation aborts.
            return true;
        fi;
        if not immediateverification(ri) then
            immediateVerificationSuccess := true;
        else
            Info(InfoRecog,3,"Doing immediate verification (depth=",
                 depth,").");
            immediateVerificationSuccess := ImmediateVerification(ri);
        fi;
    until kernelMandarinSuccess and immediateVerificationSuccess;

    SetNiceGens(ri,Concatenation(pregensfac(ri), NiceGens(riker)));

    Info(InfoRecog, 3, "Check mandarins (depth=", depth,").");
    mandarinSLPs := [];
    for i in [1..Length(mandarins)] do
        x := mandarins[i];
        # Build an SLP for the mandarin x and check that it evaluates to x.
        # We get that SLP by multiplying the results of the corresponding
        # kernel and image node SLPs. We also need to adjust for the fact that
        # the nice generators of our node are the concatenation of the image
        # and kernel node nice generators.
        # Note that the case with trivial kernel was handled above.
        nrNiceGensOfImageNode := Length(NiceGens(rifac));
        s := NewProductOfStraightLinePrograms(riker!.mandarinSLPs[i], [nrNiceGensOfImageNode + 1 .. Length(NiceGens(ri))],
                                              rifac!.mandarinSLPs[i], [1..nrNiceGensOfImageNode],
                                              Length(NiceGens(ri)));
        # Now check that the SLP evaluates to x. But first we need to do a
        # hack: something is suuper iffy about the method BlocksModScalars,
        # which is called by BlockDiagonal. Groups recognized by
        # BlocksModScalars are to be understood neither as a projective nor as
        # a matrix group, but rather as a "all block-scalars being trivial"
        # group. To be able to check the mandarins we would thus need special
        # functions handling isone and isequal, but these do not exist.
        # Note that this also poses a problem for immediate verification, which
        # we circumvent by hacking SLPforElementGeneric.
        if not isequal(ri)(x, ResultOfStraightLineProgram(s, NiceGens(ri)))
                and fhmethsel(ri).successMethod <> "BlocksModScalars" then
            # TODO: with the master branch rewriting the gens as slps never
            # fails. at least we never enter a second iteration of the
            # "recognise image" loop.
            Info(InfoRecog, 2,
                 "Enter Mandarin crisis (non-leaf, depth=", depth, ").");
                # TODO remove
            return MANDARIN_CRISIS;
        fi;
        Add(mandarinSLPs, s);
    od;
    ri!.mandarinSLPs := mandarinSLPs;

    if InfoLevel(InfoRecog) = 1 and depth = 0 then Print("\n"); fi;
    # StopStoringRandEls(ri);
    SetFilterObj(ri,IsReady);
    return true;
  end);

InstallGlobalFunction( ValidateHomomInput,
  function(ri,x)
    if Hasvalidatehomominput(ri) then
        return validatehomominput(ri)(ri,x);
    else
        return true;
    fi;
  end );

InstallGlobalFunction( CalcNiceGens,
  function(ri,origgens)
    return calcnicegens(ri)(ri,origgens);
  end );

InstallGlobalFunction( CalcNiceGensGeneric,
  # generic function using an slp:
  function(ri,origgens)
    if Hasslptonice(ri) then
        return ResultOfStraightLineProgram(slptonice(ri),origgens);
    else
        return origgens;
    fi;
  end );

InstallGlobalFunction( CalcNiceGensHomNode,
  # function for the situation on a homomorphism node (non-Leaf):
  function(ri, origgens)
    local nicegens, kernelgens;
    # compute preimages of the nicegens of the image group
    nicegens := CalcNiceGens(ImageRecogNode(ri), origgens);
    # Is there a non-trivial kernel? then add its nicegens
    if HasKernelRecogNode(ri) and KernelRecogNode(ri) <> fail then
        # we cannot just use gensN(KernelRecogNode(ri)) here, as those values are defined
        # relative to the original generators we used during recognition; but
        # the origgens passed to this function might differ
        kernelgens := ResultOfStraightLineProgram(gensNslp(ri), origgens);
        Append(nicegens, CalcNiceGens(KernelRecogNode(ri), kernelgens));
    fi;
    return nicegens;
  end );

InstallGlobalFunction( SLPforElement,
  function(ri,x)
    local slp;
    slp := slpforelement(ri)(ri,x);
    if slp <> fail then
        SlotUsagePattern(slp);
    fi;
    return slp;
  end );

InstallGlobalFunction( SLPforElementGeneric,
  # generic method for a non-leaf node
  function(ri,g)
    local gg,n,rifac,riker,s,s1,s2,y,nr1,nr2;
    rifac := ImageRecogNode(ri);
    riker := KernelRecogNode(ri);   # note: might be fail

    if not ValidateHomomInput(ri, g) then
        return fail;
    fi;

    gg := ImageElm(Homom(ri),g);
    if gg = fail then
        return fail;
    fi;
    s1 := SLPforElement(rifac,gg);
    if s1 = fail then
        return fail;
    fi;
    # The corresponding kernel element:
    y := ResultOfStraightLineProgram(s1,pregensfac(ri));
    n := g*y^-1;
    # If the kernel is trivial, we check whether n is the identity in ri.
    # This is necessary during immediate verification, since the kernel might
    # have incorrectly been recognised as trivial.
    if riker = fail then
        if not ri!.isone(n)
                # Big ugly hack. If the successMethod is BlocksModScalars, then
                # we can't use ri!.isone, see the documentation of
                # BlocksModScalars. 
                and not ri!.fhmethsel.successMethod = "BlocksModScalars" then
            return fail;
        fi;
        return s1;
    fi;
    s2 := SLPforElement(riker,n);
    if s2 = fail then
        return fail;
    fi;
    nr2 := NrInputsOfStraightLineProgram(s2);
    nr1 := NrInputsOfStraightLineProgram(s1);
    s := NewProductOfStraightLinePrograms(s2,[nr1+1..nr1+nr2],
                                          s1,[1..nr1],
                                          nr1+nr2);
    return s;
  end);

# Some helper functions for generic code:

InstallOtherMethod( Size, "for a recognition node",
  [IsRecogNode and IsReady],
  function(ri)
    local size;
    if IsLeaf(ri) then
        # Note: A leaf in projective recognition *has* to set the size
        #       of the recognition node!
        return Size(Grp(ri));
    else
        size := Size(ImageRecogNode(ri));
        if KernelRecogNode(ri) <> fail then
            return Size(KernelRecogNode(ri)) * size;
        else
            return size;   # trivial kernel
        fi;
    fi;
  end);

InstallOtherMethod( Size, "for a failed recognition node",
  [IsRecogNode],
  function(ri)
    ErrorNoReturn("Can't compute size since <ri> is not ready (see IsReady)");
  end);

InstallOtherMethod( \in, "for a group element and a recognition node",
  [IsObject, IsRecogNode and IsReady],
  function( el, ri )
    local gens,slp;
    slp := SLPforElement(ri,el);
    if slp = fail then
        return false;
    else
        gens := NiceGens(ri);
        if IsObjWithMemory(gens[1]) then
            gens := StripMemory(gens);
        fi;
        return isequal(ri)(el,ResultOfStraightLineProgram(slp,gens));
    fi;
  end);

InstallOtherMethod( \in, "for a group element and a recognition node",
  [IsObject, IsRecogNode],
  function( el, ri )
    ErrorNoReturn("Can't decide membership since <ri> is not ready (see IsReady)");
  end);

InstallGlobalFunction( "DisplayCompositionFactors", function(arg)
  local c,depth,f,i,j,ri,homs,ksize;
  if Length(arg) = 1 then
      ri := arg[1];
      depth := 0;
      homs := 0;
      ksize := 1;
  else
      ri := arg[1];
      depth := arg[2];
      homs := arg[3];
      ksize := arg[4];
  fi;
  if not IsReady(ri) then
      for j in [1..homs] do Print("-> "); od;
      Print("Recognition failed\n");
      return;
  fi;
  if IsLeaf(ri) then
      c := CompositionSeries(Grp(ri));
      for i in [1..Length(c)-1] do
          if homs > 0 then
              Print("Group with Size ",ksize*Size(c[i]));
              for j in [1..homs] do Print(" ->"); od;
              Print(" ");
          fi;
          Print("Group ",GroupString(c[i],""),"\n | ");
          f := Image( NaturalHomomorphismByNormalSubgroup( c[i], c[i+1] ) );
          Print(IsomorphismTypeInfoFiniteSimpleGroup( f ).name, "\n" );
      od;
  else
      if HasKernelRecogNode(ri) and KernelRecogNode(ri) <> fail then
          DisplayCompositionFactors(ImageRecogNode(ri),depth+1,homs+1,
                                    ksize*Size(KernelRecogNode(ri)));
          DisplayCompositionFactors(KernelRecogNode(ri),depth+1,homs,ksize);
      else
          DisplayCompositionFactors(ImageRecogNode(ri),depth+1,homs+1,ksize);
      fi;
  fi;
  if depth = 0 then
      Print("1\n");
  fi;
end );

InstallGlobalFunction( "SLPforNiceGens", function(ri)
  local l,ll,s;
  l := List( [1..Length(GeneratorsOfGroup(Grp(ri)))], x->() );
  l := GeneratorsWithMemory(l);
  ll := CalcNiceGens(ri,l);
  s := SLPOfElms(ll);
  if s <> fail then
      SlotUsagePattern(s);
  fi;
  return s;
end );

# For user debugging purposes. Takes a string consisting of lower- or
# upper-case "f" and "k". Returns the node one arrives at by descending through
# the tree, going to the factor for each "f" and to the kernel for each "k".
InstallGlobalFunction( "GetCompositionTreeNode",
  function( ri, what )
    local r,c;
    r := ri;
    for c in what do
      if c in "fF" then r := ImageRecogNode(r);
      elif c in "kK" then r := KernelRecogNode(r); fi;
    od;
    return r;
  end );

# Testing:

RECOG.TestGroupOptions := rec(
      # Number of times to test whether the recognized size is right
      sizeTests := 3,

      # Number of random elements in group to check
      # This is used both for the number of elements in the
      # group to check, and the number of random elements of
      # a supergroup to check
      inTests := 30,

      # The following options are off by default as they fail on
      # many examples at present

      # if the following is set to true, then we test what happens if  SLPforElement
      # is called with elements outside the group
      tryNonGroupElements := false
  );


# Test recognition of a group 'g' with known size 'size'.
# 'proj' denotes if the group is projective
# 'optionlist' is an optional list of options overriding
# RECOG.TestGroupOptions
RECOG.TestGroup := function(g,proj,size, optionlist...)
  local l,r,ri,s,x,count,lvl,seedMT,seedRS,gens,supergroup, options;
  count := 0;
  
  options := ShallowCopy(RECOG.TestGroupOptions);

  if Length(optionlist) > 0 then
    for r in RecNames(optionlist[1]) do
        if not IsBound(options.(r)) then
            ErrorNoReturn("Invalid option to TestGroup: ", r);
        fi;
        options.(r) := optionlist[1].(r);
    od;
  fi;

  lvl:=InfoLevel(InfoRecog);
  SetInfoLevel(InfoRecog, 0);
  repeat
      count := count + 1;
      #r := Runtime();
      seedMT := State(GlobalMersenneTwister);
      seedRS := State(GlobalRandomSource);
      if proj then
          ri := RecogniseProjectiveGroup(g);
      else
          ri := RecogniseGroup(g);
      fi;
      #Print("Time for recognition: ",Runtime()-r,"\n");
      if Size(ri) <> size then
          Print("ALARM: set count to -1 to skip test!\n");
          Print("group := ", g, ";\n");
          Print("recogsize := ", Size(ri), ";\n");
          Print("truesize := ", size, ";\n");
          Print("proj := ", proj, ";\n");
          Print("seedMT := ", seedMT, ";\n");
          Print("seedRS := ", seedRS, ";\n");
          Error("Alarm: Size not correct!\n");
          if count = -1 then
              return fail;
          fi;
      else
          #Print("Test was OK!\n");
          count := 3;   # worked!
      fi;
  until count >= 3;
  #View(ri);
  #Print("\n");
  count := 0;
  gens := GeneratorsOfGroup(g);
  # Handle groups where GeneratorsOfGroup returns empty list
  if IsEmpty(gens) then
    gens := [One(g)];
  fi;
  l := CalcNiceGens(ri,gens);
  repeat
      count := count + 1;
      #Print(".\c");
      x := PseudoRandom(g);
      s := SLPforElement(ri,x);
      if s = fail or not isequal(ri)(ResultOfStraightLineProgram(s,l),x) then
          Print("ALARM: set count to -1 to skip test!\n");
          Print("group := ", g, ";\n");
          Print("recogsize := ", Size(ri), ";\n");
          Print("proj := ", proj, ";\n");
          Print("x := ", x, ";\n");
          Print("s := ", s, ";\n");
          if s <> fail then
            Print("result := ", ResultOfStraightLineProgram(s,l), ";\n");
          fi;
          Error("Alarm: SLPforElement did not work!\n");
          
          if count = -1 then
              return fail;
          fi;
      fi;
  until count >= options.inTests;

  if IsPermGroup(g) then
    supergroup := SymmetricGroup(LargestMovedPoint(g) + 2);
  elif IsMatrixGroup(g) then
    supergroup := GL(DimensionOfMatrixGroup(g), DefaultFieldOfMatrixGroup(g));
  else
    supergroup := fail;
  fi;

  if supergroup <> fail and options.tryNonGroupElements then
    count := 0;
    repeat
        count := count + 1;
        #Print(".\c");
        x := PseudoRandom(supergroup);
        s := SLPforElement(ri,x);
        if s <> fail and not isequal(ri)(ResultOfStraightLineProgram(s,l),x) then
            Print("ALARM: set count to -1 to skip test!\n");
            Print("group := ", g, ";\n");
            Print("recogsize := ", Size(ri), ";\n");
            Print("proj := ", proj, ";\n");
            Print("x := ", x, ";\n");
            Print("s := ", s, ";\n");
            if s <> fail then
                Print("result := ", ResultOfStraightLineProgram(s,l), ";\n");
            fi;

            Error("Alarm: SLPforElement did not work on (possibly) non-group element!\n");
            if count = -1 then
                return fail;
            fi;
        fi;
    until count >= options.inTests;
  fi;

  #Print("\n30 random elements successfully sifted!\n");
  SetInfoLevel(InfoRecog, lvl);
  return ri;
end;

# Call RECOG.TestGroup on all maximal subgroups of a named atlas group.
# under all known representations which are permutation groups or
# matrices over finite fields.
# Optionally give 'options' to pass options to RECOG.TestGroup
RECOG.testAllMaximalSubgroupsOfAtlasGroup := function(name, options...)
    local reps, rep, maximal, exhaustList;

    # The following function makes it easy to extract
    # all results of a function which returns 'fail'
    # when given too large a value
    exhaustList := function(F)
        local l, i, val;
        l := [];
        for i in PositiveIntegers do
            val := F(i);
            if val = fail then
                return l;
            fi;
            Add(l, val);
        od;
    end;

    reps := exhaustList(x -> AtlasGenerators(name, x));

    # Only interested in permutations or finite fields
    reps := Filtered(reps, x -> (not IsBound(x.ring)) or (IsFinite(x.ring) and IsField(x.ring)));
    Print("Testing ", Size(reps), " representations\n");
    for rep in reps do
        for maximal in exhaustList(x -> AtlasSubgroup(rep, x)) do
            CallFuncList(RECOG.TestGroup, Concatenation([maximal, false, Size(maximal)], options));
            Print(".");
        od;
        Print("\n");
    od;
end;

# Call RECOG.TestGroup on all subgroups up to conjugacy of a group.
# Optionally give 'options' to pass options to RECOG.TestGroup
RECOG.testAllSubgroups := function(g, options...)
    local list, sub;
    list := List(ConjugacyClassesSubgroups(g), Representative);
    for sub in list do
        CallFuncList(RECOG.TestGroup, Concatenation([sub, false, Size(sub)],options));
    od;
end;
