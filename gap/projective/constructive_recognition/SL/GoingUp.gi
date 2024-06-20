#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This files's authors include Daniel Rademacher.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
#############################################################################



#############################################################################
#############################################################################
######## GoingUp method for special linear groups ###########################
#############################################################################
#############################################################################



RECOG.SLn_UpStep := function(w)
# w has components:
#   d       : size of big SL
#   n       : size of small SL
#   slnstdf : fakegens for SL_n standard generators
#   bas     : current base change, first n vectors are where SL_n acts
#             rest of vecs are invariant under SL_n
#   basi    : current inverse of bas
#   sld     : original group with memory generators, PseudoRandom
#             delivers random elements
#   sldf    : fake generators to keep track of what we are doing
#   f       : field
# The following are filled in automatically if not already there:
#   p       : characteristic
#   ext     : q=p^ext
#   One     : One(slnstdf[1])
#   can     : CanonicalBasis(f)
#   canb    : BasisVectors(can)
#   transh  : fakegens for the "horizontal" transvections n,i for 1<=i<=n-1
#             entries can be unbound in which case they are made from slnstdf
#   transv  : fakegens for the "vertical" transvections i,n for 1<=i<=n-1
#             entries can be unbound in which case they are made from slnstdf
#
# We keep the following invariants (going from n -> n':=2n-1)
#   bas, basi is a base change to the target base
#   slnstdf are SLPs to reach standard generators of SL_n from the
#       generators of sld
local DoColOp_n,DoRowOp_n,FixSLn,Fixc,MB,Vn,Vnc,aimdim,c,c1,c1f,cf,cfi,
    ci,cii,coeffs,flag,i,id,int1,int3,j,k,lambda,list,mat,newbas,newbasf,
    newbasfi,newbasi,newdim,newpart,perm,pivots,pivots2,pos,pow,s,sf,
    slp,std,sum1,tf,trans,transd,transr,v,vals,zerovec,counter;

    Info(InfoRecog,3,"Going up: ",w.n," (",w.d,")...");

    # Before we begin, we upgrade the data structure with a few internal
    # things:

    if not(IsBound(w.can)) then w.can := CanonicalBasis(w.f); fi;
    if not(IsBound(w.canb)) then w.canb := BasisVectors(w.can); fi;
    if not(IsBound(w.One)) then w.One := One(w.slnstdf[1]); fi;
    if not(IsBound(w.transh)) then w.transh := []; fi;
    if not(IsBound(w.transv)) then w.transv := []; fi;
    # Update our cache of *,n and n,* transvections because we need them
    # all over the place:
    std := RECOG.InitSLstd(w.f,w.n,
                            w.slnstdf{[1..w.ext]},
                            w.slnstdf{[w.ext+1..2*w.ext]},
                            w.slnstdf[2*w.ext+1],
                            w.slnstdf[2*w.ext+2]);
    for i in [1..w.n-1] do
        for k in [1..w.ext] do
            pos := (i-1)*w.ext + k;
            if not(IsBound(w.transh[pos])) then
                RECOG.ResetSLstd(std);
                RECOG.DoColOp_SL(false,w.n,i,w.canb[k],std);
                w.transh[pos] := std.right;
            fi;
            if not(IsBound(w.transv[pos])) then
                RECOG.ResetSLstd(std);
                RECOG.DoRowOp_SL(false,i,w.n,w.canb[k],std);
                w.transv[pos] := std.left;
            fi;
        od;
    od;

    Unbind(std);

    # Now we can define two helper functions:
    DoColOp_n := function(el,i,j,lambda,w)
    # This adds lambda times the i-th column to the j-th column.
    # Note that either i or j must be equal to n!
    local coeffs,k;
    coeffs := IntVecFFE(Coefficients(w.can,lambda));
    if i = w.n then
        for k in [1..w.ext] do
            if not(IsZero(coeffs[k])) then
                if IsOne(coeffs[k]) then
                    el := el * w.transh[(j-1)*w.ext+k];
                elif not(IsZero(coeffs[k])) then
                    el := el * w.transh[(j-1)*w.ext+k]^coeffs[k];
                fi;
            fi;
        od;
    elif j = w.n then
        for k in [1..w.ext] do
            if not(IsZero(coeffs[k])) then
                if IsOne(coeffs[k]) then
                    el := el * w.transv[(i-1)*w.ext+k];
                else
                    el := el * w.transv[(i-1)*w.ext+k]^coeffs[k];
                fi;
            fi;
        od;
    else
        Error("either i or j must be equal to n");
    fi;
    return el;
    end;
    DoRowOp_n := function(el,i,j,lambda,w)
    # This adds lambda times the j-th row to the i-th row.
    # Note that either i or j must be equal to n!
    local coeffs,k;
    coeffs := IntVecFFE(Coefficients(w.can,lambda));
    if j = w.n then
        for k in [1..w.ext] do
            if not(IsZero(coeffs[k])) then
                if IsOne(coeffs[k]) then
                    el := w.transv[(i-1)*w.ext+k] * el;
                else
                    el := w.transv[(i-1)*w.ext+k]^coeffs[k] * el;
                fi;
            fi;
        od;
    elif i = w.n then
        for k in [1..w.ext] do
            if not(IsZero(coeffs[k])) then
                if IsOne(coeffs[k]) then
                    el := w.transh[(j-1)*w.ext+k] * el;
                else
                    el := w.transh[(j-1)*w.ext+k]^coeffs[k] * el;
                fi;
            fi;
        od;
    else
        Error("either i or j must be equal to n");
    fi;
    return el;
    end;

    # Here everything starts, some more preparations:

    # We compute exclusively in our basis, so we occasionally need an
    # identity matrix:
    id := IdentityMat(w.d,w.f);
    FixSLn := VectorSpace(w.f,id{[w.n+1..w.d]});
    Vn := VectorSpace(w.f,id{[1..w.n]});

    Info(InfoRecog,2,"Current dimension: " );
    Info(InfoRecog,2,w.n);
    Info(InfoRecog,2,"\n");
    Info(InfoRecog,2,"New dimension: ");
    Info(InfoRecog,2,Minimum(2*w.n-1,w.GoalDim));
    Info(InfoRecog,2,"\n");

    Info(InfoRecog,2,"Preparation done.");

    ##
    ## Step 1
    ##

    # First pick an element in SL_n with fixed space of dimension d-n+1:
    # We already have an SLP for an n-1-cycle: it is one of the std gens.
    # For n=2 we use a transvection for this purpose.
    if w.n > 2 then
        if IsOddInt(w.n) then
            if w.p > 2 then
            s := id{Concatenation([1,w.n],[2..w.n-1],[w.n+1..w.d])};
            ConvertToMatrixRepNC(s,w.f);
            if IsOddInt(w.n) then s[2] := -s[2]; fi;
            sf := w.slnstdf[2*w.ext+2];
            else   # in even characteristic we take the n-cycle:
            s := id{Concatenation([w.n],[1..w.n-1],[w.n+1..w.d])};
            ConvertToMatrixRepNC(s,w.f);
            sf := w.slnstdf[2*w.ext+1];
            fi;
        else
            Error("this program only works for odd n or n=2");
        fi;
    else
        # In this case the n-1-cycle is the identity, so we take a transvection:
        s := MutableCopyMat(id);
        s[1,2] := One(w.f);
        sf := w.slnstdf[1];
    fi;

    Info(InfoRecog,2,"Step 1 done.");

    # Find a good random element:
    w.count := 0;
    aimdim := Minimum(2*w.n-1,w.GoalDim);
    newdim := aimdim - w.n;
    counter := 0;
    while true do   # will be left by break

        ##
        ## Step 2
        ##
        v := fail;
        repeat
            counter := counter + 1;
            if InfoLevel(InfoRecog) >= 3 then Print(".\c"); fi;
            w.count := w.count + 1;
            c1 := PseudoRandom(w.sld);
            
            # Do the base change into our basis:
            #c1 := w.bas * c1 * w.basi;
            c := s^(w.bas * c1 * w.basi);
            
            # Check how these elements look like. Where is the SLP and what elements do we really use
            
            # Now check that Vn + Vn*s^c1 has dimension 2n-1:
            sum1 := SumIntersectionMat(id{[1..w.n]}, c{[1..w.n]});
            if Size(sum1[1]) = aimdim then
                # intersect Fix(c) = Nullspace(c-id) with V_n in order to
                # find a suitable vector which we can later to our basis
                int1 := SumIntersectionMat(RECOG.FixspaceMat(c),id{[1..w.n]})[2];
                v := First(int1, v -> not IsZero(v[w.n]));
                if v = fail then
                    Info(InfoRecog,2,"Ooops: Component n was zero!");
                fi;
            fi;
        until v <> fail;

        v := v / v[w.n];   # normalize to 1 in position n
        Assert(1,v*c=v);

        # now that we have our c and c1, compute some associated
        # values for later use
        ci := c^-1;
        slp := SLPOfElm(c1);
        c1f := ResultOfStraightLineProgram(slp,w.sldf);
        cf := sf^c1f;
        cfi := cf^-1;
        
        Info(InfoRecog,2,"Step 2 done.");

        ##
        ## Steps 3 and 4
        ##

        # Now we found our aimdim-dimensional space W. Since SL_n
        # has a d-n-dimensional fixed space W_{d-n} and W contains a complement
        # of that fixed space, the intersection of W and W_{d-n} has dimension
        # newdim.

        # Change basis:
        newpart := ExtractSubMatrix(c,[1..(w.n-1)],[1..(w.d)]);
        # Clean out the first n entries to go to the fixed space of SL_n:
        zerovec := Zero(newpart[1]);
        for i in [1..(w.n-1)] do
            CopySubVector(zerovec,newpart[i],[1..w.n],[1..w.n]);
        od;
        MB := MutableBasis(w.f,[],zerovec);
        i := 1;
        pivots := EmptyPlist(newdim);
        while i <= Length(newpart) and NrBasisVectors(MB) < newdim do
            if not(IsContainedInSpan(MB,newpart[i])) then
                Add(pivots,i);
                CloseMutableBasis(MB,newpart[i]);
            fi;
            i := i + 1;
        od;
        newpart := newpart{pivots};
        newbas := Concatenation(id{[1..w.n-1]},[v],newpart);
        if 2*w.n-1 < w.d then
            
            # intersect Fix(c) with F_{d-n}
            int3 := SumIntersectionMat(RECOG.FixspaceMat(c),id{[w.n+1..w.d]})[2];
            if Size(int3) <> w.d - aimdim then
                Info(InfoRecog,2,"Ooops, FixSLn \cap Fixc wrong dimension");
                continue;
            fi;
            Append(newbas,int3);
        fi;
        ConvertToMatrixRep(newbas,Size(w.f));
        newbasi := newbas^-1;
        if newbasi = fail then
            Info(InfoRecog,2,"Ooops, Fixc intersected too much, we try again");
            continue;
        fi;
        
        ci := newbas * ci * newbasi;
        cii := ExtractSubMatrix(ci,[w.n+1..aimdim],[1..w.n-1]);
        ConvertToMatrixRep(cii,Size(w.f));
        cii := TransposedMat(cii);
        # The rows of cii are now what used to be the columns,
        # their length is newdim, we need to span the full newdim-dimensional
        # row space and need to remember how:
        zerovec := Zero(cii[1]);
        MB := MutableBasis(w.f,[],zerovec);
        i := 1;
        pivots2 := EmptyPlist(newdim);
        while i <= Length(cii) and NrBasisVectors(MB) < newdim do
            if not(IsContainedInSpan(MB,cii[i])) then
                Add(pivots2,i);
                CloseMutableBasis(MB,cii[i]);
            fi;
            i := i + 1;
        od;
        if Length(pivots2) = newdim then
            break;
        fi;
        Info(InfoRecog,2,"Ooops, no nice bottom...");
        # Otherwise simply try again
    od;

    cii := cii{pivots2}^-1;
    ConvertToMatrixRep(cii,w.f);
    c := newbas * c * newbasi;
    w.bas := newbas * w.bas;
    w.basi := w.basi * newbasi;


    Info(InfoRecog,2," found c1 and c.");
    # Now SL_n has to be repaired according to the base change newbas:

    # Now write this matrix newbas as an SLP in the standard generators
    # of our SL_n. Then we know which generators to take for our new
    # standard generators, namely newbas^-1 * std * newbas.

    newbasf := w.One;
    for i in [1..w.n-1] do
        if not(IsZero(v[i])) then
            newbasf := DoColOp_n(newbasf,w.n,i,v[i],w);
        fi;
    od;
    newbasfi := newbasf^-1;
    w.slnstdf := List(w.slnstdf,x->newbasfi * x * newbasf);
    # Now update caches:
    w.transh := List(w.transh,x->newbasfi * x * newbasf);
    w.transv := List(w.transv,x->newbasfi * x * newbasf);

    Info(InfoRecog,2,"Step 3 and 4 done");

    ##
    ## Step 5
    ##

    # Now consider the transvections t_i:
    # t_i : w.bas[j] -> w.bas[j]        for j <> i and
    # t_i : w.bas[i] -> w.bas[i] + ww
    # We want to modify (t_i)^c such that it fixes w.bas{[1..w.n]}:
    trans := [];
    for i in pivots2 do
        # This does t_i
        for lambda in w.canb do
            # This does t_i : v_j -> v_j + lambda * v_n
            tf := w.One;
            tf := DoRowOp_n(tf,i,w.n,lambda,w);
            # Now conjugate with c:
            tf := cfi*tf*cf;
            # Now cleanup in column n above row n, the entries there
            # are lambda times the stuff in column i of ci:
            for j in [1..w.n-1] do
                tf := DoRowOp_n(tf,j,w.n,-ci[j,i]*lambda,w);
            od;
            Add(trans,tf);
        od;
    od;

    # Now put together the clean ones by our knowledge of c^-1:
    transd := [];
    for i in [1..Length(pivots2)] do
        for lambda in w.canb do
            tf := w.One;
            vals := BlownUpVector(w.can,cii[i]*lambda);
            for j in [1..w.ext * newdim] do
                pow := IntFFE(vals[j]);
                if not(IsZero(pow)) then
                    if IsOne(pow) then
                        tf := tf * trans[j];
                    else
                        tf := tf * trans[j]^pow;
                    fi;
                fi;
            od;
            Add(transd,tf);
        od;
    od;
    Unbind(trans);

    Info(InfoRecog,2,"Step 5 done");

    ##
    ## Step 6
    ##

    # Now to the "horizontal" transvections, first create them as SLPs:
    transr := [];
    for i in pivots do
        # This does u_i : v_i -> v_i + v_n
        tf := w.One;
        tf := DoColOp_n(tf,w.n,i,One(w.f),w);
        # Now conjugate with c:
        tf := cfi*tf*cf;
        # Now cleanup in rows above row n:
        for j in [1..w.n-1] do
            tf := DoRowOp_n(tf,j,w.n,-ci[j,w.n],w);
        od;
        # Now cleanup in rows below row n:
        for j in [1..newdim] do
            coeffs := IntVecFFE(Coefficients(w.can,-ci[w.n+j,w.n]));
            for k in [1..w.ext] do
                if not(IsZero(coeffs[k])) then
                    if IsOne(coeffs[k]) then
                        tf := transd[(j-1)*w.ext + k] * tf;
                    else
                        tf := transd[(j-1)*w.ext + k]^coeffs[k] * tf;
                    fi;
                fi;
            od;
        od;
        
        # Now cleanup column n above row n:
        for j in [1..w.n-1] do
            tf := DoColOp_n(tf,j,w.n,ci[j,w.n],w);
        od;
        
        # Now cleanup row n left of column n:
        for j in [1..w.n-1] do
            tf := DoRowOp_n(tf,w.n,j,-c[i,j],w);
        od;
        
        # Now cleanup column n below row n:
        for j in [1..newdim] do
            coeffs := IntVecFFE(Coefficients(w.can,ci[w.n+j,w.n]));
            for k in [1..w.ext] do
                if not(IsZero(coeffs[k])) then
                    if IsOne(coeffs[k]) then
                        tf := tf * transd[(j-1)*w.ext + k];
                    else
                        tf := tf * transd[(j-1)*w.ext + k]^coeffs[k];
                    fi;
                fi;
            od;
        od;
        Add(transr,tf);
    od;

    Info(InfoRecog,2,"Step 6 done");

    ##
    ## Step 7
    ##

    # From here on we distinguish three cases:
    #   * w.n = 2
    #   * we finish off the constructive recognition
    #   * we have to do another step as the next thing
    if w.n = 2 then
        w.slnstdf[2*w.ext+2] := transd[1]*transr[1]^-1*transd[1];
        w.slnstdf[2*w.ext+1] := w.transh[1]*w.transv[1]^-1*w.transh[1]
                                *w.slnstdf[2*w.ext+2];
        Unbind(w.transh);
        Unbind(w.transv);
        w.n := 3;
        Info(InfoRecog,2,"Step 7 done");
        return w;
    fi;
    # We can finish off:
    if aimdim = w.GoalDim then
        # In this case we just finish off and do not bother with
        # the transvections, we will only need the standard gens:
        # Now put together the (newdim+1)-cycle:
        # n+newdim -> n+newdim-1 -> ... -> n+1 -> n -> n+newdim
        flag := false;
        s := w.One;
        for i in [1..newdim] do
            if flag then
                # Make [[0,-1],[1,0]] in coordinates w.n and w.n+i:
                tf:=transd[(i-1)*w.ext+1]*transr[i]^-1*transd[(i-1)*w.ext+1];
            else
                # Make [[0,1],[-1,0]] in coordinates w.n and w.n+i:
                tf:=transd[(i-1)*w.ext+1]^-1*transr[i]*transd[(i-1)*w.ext+1]^-1;
            fi;
            s := s * tf;
            flag := not(flag);
        od;

        # Finally put together the new 2n-1-cycle and 2n-2-cycle:
        s := s^-1;
        w.slnstdf[2*w.ext+1] := w.slnstdf[2*w.ext+1] * s;
        w.slnstdf[2*w.ext+2] := w.slnstdf[2*w.ext+2] * s;
        Unbind(w.transv);
        Unbind(w.transh);
        w.n := aimdim;
        Info(InfoRecog,2,"Step 7 done");
        return w;
    fi;

    # Otherwise we do want to go on as the next thing, so we want to
    # keep our transvections. This is easily done if we change the
    # basis one more time. Note that we know that n is odd here!

    # Put together the n-cycle:
    # 2n-1 -> 2n-2 -> ... -> n+1 -> n -> 2n-1
    flag := false;
    s := w.One;
    for i in [w.n-1,w.n-2..1] do
        if flag then
            # Make [[0,-1],[1,0]] in coordinates w.n and w.n+i:
            tf := transd[(i-1)*w.ext+1]*transr[i]^-1*transd[(i-1)*w.ext+1];
        else
            # Make [[0,1],[-1,0]] in coordinates w.n and w.n+i:
            tf := transd[(i-1)*w.ext+1]^-1*transr[i]*transd[(i-1)*w.ext+1]^-1;
        fi;
        s := s * tf;
        flag := not(flag);
    od;

    # Finally put together the new 2n-1-cycle and 2n-2-cycle:
    w.slnstdf[2*w.ext+1] := s * w.slnstdf[2*w.ext+1];
    w.slnstdf[2*w.ext+2] := s * w.slnstdf[2*w.ext+2];

    list := Concatenation([1..w.n-1],[w.n+1..2*w.n-1],[w.n],[2*w.n..w.d]);
    perm := PermList(list);
    mat := PermutationMat(perm^-1,w.d,w.f);
    ConvertToMatrixRep(mat,w.f);
    w.bas := w.bas{list};
    ConvertToMatrixRep(w.bas,w.f);
    w.basi := w.basi*mat;

    # Now add the new transvections:
    for i in [1..w.n-1] do
        w.transh[w.ext*(w.n-1)+w.ext*(i-1)+1] := transr[i];
    od;
    Append(w.transv,transd);
    w.n := 2*w.n-1;

    Info(InfoRecog,2,"Step 7 done");
    return w;
end;
