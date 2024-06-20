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



###################################################################################################
###################################################################################################
######## Constructive recognition SL(2,q) in natural representation ###############################
###################################################################################################
###################################################################################################



# TODO: Add MSLPs to these algorithms
# This algorithm is an implementation of the paper
# "Fast Recognition of Classical Groups over Large Fields"
# by Marston Conder and Charles Leedham-Green
RECOG.ConstructiveRecognitionSL2NaturalRepresentation := function(G, q, epsilon)
local F, factors, counter, one, factor, foundEle, passed, max, eigenvalues, eigenvalues2, eigenvectors, eigenvectors2, A, B, rand, foundConjugate, test, BDiag, C, basechange, v, d, CC, check, i, j, D, DD, T, S, o, t1, t2, zero, slp;

    factors := PrimeDivisors(q-1);
    counter := 1;
    F := GF(q);

    if not(IsObjWithMemory(GeneratorsOfGroup(G)[1])) then
        G := GroupWithMemory(G);
    fi;

    one := One(G);
    zero := Zero(F);
    max := Int(1/epsilon);
    while counter < max do

        # Step 1: Find random element of order q-1
        # foundEle := false;
        # while not(foundEle) do
        #    A := PseudoRandom(G);
        #    if A^(q-1) = one then
        #        passed := true;
        #        for factor in factors do
        #            if A^((q-1)/factor) = one then
        #                passed := false;
        #                break;
        #            fi;
        #        od;
        #        if passed then
        #            foundEle := true;
        #        else
        #            counter := counter + 1;
        #        fi;
        #    else
        #        counter := counter +1;
        #    fi;
        #    if counter >= max then
        #        return fail;
        #    fi;
        #od;

        # Step 1: Find random element of order q-1 (first improvement based on magma code)
        foundEle := false;
        while not(foundEle) do
            A := PseudoRandom(G);
            o := Order (A);
            if (o mod (q - 1) = 0) then
                A := A^(o/(q - 1));
                foundEle := true;
            else
                counter := counter +1;
            fi;
            if counter >= max then
                return fail;
            fi;
        od;

        # Step 2: Eigenvectors and eigenvalues
        eigenvalues := RootsOfPolynomial(CharacteristicPolynomial(A));
        # Note eigenvalues[1] = eigenvalues[2]^(-1)
        eigenvectors := [1,2];
        eigenvectors[1] := RECOG.EigenspaceMat(StripMemory(A), eigenvalues[1]);
        eigenvectors[2] := RECOG.EigenspaceMat(StripMemory(A), eigenvalues[2]);

        # Step 3: Conjugate of A that does not intersect with A's eigenspaces
        foundConjugate := false;
        eigenvectors2 := [1,2];
        while not(foundConjugate) do
            rand := PseudoRandom(G);
            B := A^rand;
            eigenvectors2[1] := RECOG.EigenspaceMat(StripMemory(B), eigenvalues[1]);
            eigenvectors2[2] := RECOG.EigenspaceMat(StripMemory(B), eigenvalues[2]);
            test := [];
            Append(test,eigenvectors[1]);
            Append(test,eigenvectors2[1]);
            if NullspaceMat(test) = [] then
                test := [];
                Append(test,eigenvectors[2]);
                Append(test,eigenvectors2[2]);
                if NullspaceMat(test) = [] then
                    basechange := [eigenvectors2[1,1],eigenvectors2[2,1]];
                    t1 := eigenvectors[1,1] * basechange^(-1);
                    t2 := eigenvectors[2,1] * basechange^(-1);
                    if (t1[1] <> zero) and (t1[2] <> zero) and (t2[1] <> zero) and (t2[2] <> zero) then
                        foundConjugate := true;
                    else
                        counter := counter + 1;
                    fi;
                else
                    counter := counter + 1;
                fi;
            else
                counter := counter + 1;
            fi;

            if counter >= max then
                return fail;
            fi;
        od;

        # Step 4: Find suitable C
        BDiag := IdentityMat(2,GF(q));
        BDiag[1,1] := eigenvalues[1];
        BDiag[2,2] := eigenvalues[2];
        v := eigenvectors[1,1] * basechange^(-1);
        d := v[2] * v[1]^-1;

        S := IdentityMat(2,F);
        while S = one do
            foundEle := false;
            while not(foundEle) do
                C := PseudoRandom(G);
                CC := basechange * C * basechange^(-1);
                if ((CC[1,2]-d*CC[1,1])) <> zero and ((d^2*CC[2,1] - d * CC[2,2]) <> zero) then
                    check := (d^2*CC[2,1] - d * CC[2,2])/(CC[1,2]-d*CC[1,1]);
                    if not(Zero(F) = check) and IsSquareFFE(F,check) then
                        i := LogFFE(check,eigenvalues[1])/2;
                        foundEle := true;
                    else
                        counter := counter + 1;
                    fi;
                else
                    counter := counter + 1;
                fi;

                if counter >= max then
                    return fail;
                fi;
            od;
            S := A^(-1) * (B^i*C)^(-1) * A * (B^i*C);
        od;

        # Step 5: Find suitable D
        v := eigenvectors[2,1] * basechange^(-1);
        d := v[2] * v[1]^-1;

        T := IdentityMat(2,F);
        while T = one do
            foundEle := false;
            while not(foundEle) do
                D := PseudoRandom(G);
                DD := basechange * D * basechange^(-1);
                if ((DD[1,2]-d*DD[1,1]) <> zero) and ((d^2*DD[2,1] - d * DD[2,2]) <> zero) then
                    check := (d^2*DD[2,1] - d * DD[2,2])/(DD[1,2]-d*DD[1,1]);
                    if not(Zero(F) = check) and IsSquareFFE(F,check) then
                        j := LogFFE(check,eigenvalues[1])/2;
                        foundEle := true;
                    else
                        counter := counter + 1;
                    fi;
                else
                    counter := counter + 1;
                fi;

                if counter >= max then
                    return fail;
                fi;
            od;
            T := A^(-1) * (B^j*D)^(-1) * A * (B^j*D);
        od;

        basechange := [eigenvectors[1,1],eigenvectors[2,1]];
        basechange[2] := basechange[2] * Determinant(basechange)^(-1);

        slp := SLPOfElms([A,S,T]);

        A := basechange * A * basechange^(-1);
        S := basechange * S * basechange^(-1);
        T := basechange * T * basechange^(-1);

        return [[A,S,T],basechange,slp];
    od;

    return fail;

end;



# Note that we use the discrete logarithm to normalise the primitive element at position [1,1]. But this is not necessarly as the entry at position [1,1] is primitive.
# Hence, this function can be adapted to larger fields by avoiding the normalisation step
RECOG.ConstructiveRecognitionSL2NaturalRepresentationCompleteBasis := function(list,F,q,p,f)
local w, k, Diag, coeffs, coeff, cong, t, s, SC, i, res, res2, A, S, T, upper, lower, basis, slp;

    list := GeneratorsWithMemory(list);

    A := list[1];
    S := list[2];
    T := list[3];

    # Normalisation step
    w := PrimitiveElement(F);
    k := LogFFE(w,A[1,1]);
    Diag := A^k;

    t := T[1,2];
    basis := [1..f];
    for i in [0..f-1] do
        basis[i+1] := w^(2*i);
    od;
    basis := Basis(F,basis);
    coeffs := Coefficients(basis,t^(-1));

    # standard basis element [1, 1, 0, 1]
    res := A^0;
    for i in [0..f-1] do
        coeff := Int(coeffs[i+1]);
        cong := Diag^(-i);
        res := res * ((T^(cong))^coeff);
    od;
    upper := [1..f];
    upper[1] := res;

    # set up complete basis for upper triangular matrices
    #UB := [GL(2, E) ! [1, x^(2 * i), 0, 1]: i in [0..e - 1]];
    #wUB := [wUS^(wD^-i): i in [0..e - 1]];
    for i in [1..f-1] do
        upper[i+1] := res^(Diag^(-i));
    od;

    s := S[2,1];
    coeffs := Coefficients(basis,s^(-1));

    # standard basis element [1, 0, 1, 1]
    res2 := A^0;
    for i in [0..f-1] do
        coeff := Int(coeffs[i+1]);
        cong := Diag^(i);
        res2 := res2 * ((S^(cong))^coeff);
    od;
    lower := [1..f];
    lower[1] := res2;

    # set up complete basis for lower triangular matrices
    for i in [1..f-1] do
        lower[i+1] := res2^(Diag^(i));
    od;

    slp := SLPOfElms(Concatenation([Diag],upper,lower));

    return [[Diag,upper,lower],slp];

end;


###################################################################################################
###################################################################################################
######## Rewriting SL(2,q) ########################################################################
###################################################################################################
###################################################################################################


# Note that we use the discrete logarithm to normalise the primitive element at position [1,1]. But this is not necessarly as the entry at position [1,1] is primitive.
# Hence, this function can be adapted to larger fields by avoiding the normalisation step
RECOG.RewritingSL2 := function(gens,F,q,p,f,ele)
local list, re, ell, mat, base, i, coeff, wMat, l1, l2, stdgens;

    stdgens := StripMemory(gens);
    stdgens := Concatenation([stdgens[1]],stdgens[2],stdgens[3]);
    stdgens := GeneratorsWithMemory(stdgens);
    l1 := stdgens{[2..f+1]};
    l2 := stdgens{[f+2..Size(stdgens)]};
    stdgens := [stdgens[1],l1,l2];

    base := [1..f];
    for i in [1..f] do 
        base[i] := (stdgens[2,i])[1,2];
    od;
    base := Basis(F,base);
    re := stdgens[1]^0;

    if ele[1,2] = Zero(F) then
        re := re*stdgens[2,1];
        mat := IdentityMat(2,F);
        mat[1,2] := One(F);
        ele := ele*mat;
    fi;

    if not(ele[1,1] = One(F)) then
        ell := (1-ele[1,1])*ele[1,2]^(-1);
        mat := IdentityMat(2,F);
        mat[2,1] := ell;
        ele := ele*mat;
        coeff := Coefficients(base,ell);
        wMat := stdgens[1]^0;
        for i in [1..f] do
            wMat := wMat*(stdgens[3,i])^Int(coeff[i]);
        od;
        re := re*wMat;
    fi;

    ell := -1*ele[1,2];
    mat := IdentityMat(2,F);
    mat[1,2] := ell;
    ele := ele*mat;
    coeff := Coefficients(base,ell);
    wMat := stdgens[1]^0;
    for i in [1..f] do
        wMat := wMat*(stdgens[2,i])^Int(coeff[i]);
    od;
    re := re*wMat;

    if not(ele[2,1] = Zero(F)) then
        ell := -1 * ele[2,1];
        mat := IdentityMat(2,F);
        mat[2,1] := ell;
        ele := mat*ele;
        coeff := Coefficients(base,ell);
        wMat := stdgens[1]^0;
        for i in [1..f] do
            wMat := wMat*(stdgens[3,i])^Int(coeff[i]);
        od;
        re := re*wMat;
    fi;

    return SLPOfElm(re^(-1));
end;



###################################################################################################
###################################################################################################
######## Constructive Recognition of SL(4,q) (Leedham-Green and O'Brien algorithm) ################
###################################################################################################
###################################################################################################



# Input: X where <X> is isomorphic to SL(4,q), F where X are dxd matrices over F_q = F (q = p^f prime power)
RECOG.OneEvenSL4 := function(X,F)
    local d, G, g, h, foundStrongInvoluation, order, gensCentraliser, EPlus;
    
    d := 4;
    G := GroupByGenerators(X);
    foundStrongInvoluation := false;
    while not(foundStrongInvoluation) do
        g := PseudoRandom(G);
        order := Order(g);
        if (order mod 2 = 0) then
            h := g^(order/2);
            EPlus := RECOG.FixspaceMat(h);
            if Size(EPlus) = 2 then
                foundStrongInvoluation := true;
            fi;
        fi;
    od;
    
    gensCentraliser := RECOG.InvolutionCentraliser(G,h,100);
    # TODO: Compute generating set for OmegaX(E) (see paper from LGO)

    #TODO: CONTINUE HERE

end;;



# Input: h an involuation in a BB group G, natural number N > 0
RECOG.InvolutionCentraliser := function(G, h, N)
    local C, i, g;

    C := [1..N];
    for i in [1..N] do
        g := PseudoRandom(G);
        C[i] := RECOG.ChFromg(h,g);
    od;

    return DuplicateFreeList(C);
end;;



# Input: h and g group elements of the same group. Returns an element as in Bray's Lemma
RECOG.ChFromg := function(h,g)
    local order, com;

    com := h^(-1)*g^(-1)*h*g;
    order := Order(com);
    
    if (order mod 2 = 0) then
        return com^(order/2);
    else
        return com^((order+1)/2)*g^(-1);
    fi;
end;;



###################################################################################################
###################################################################################################
######## Older algorithms #########################################################################
###################################################################################################
###################################################################################################



RECOG.RecogniseSL2NaturalOddCharUsingBSGS := function(g,f)
  local ext,p,q,res,slp,std;
  p := Characteristic(f);
  ext := DegreeOverPrimeField(f);
  q := Size(f);
  std := RECOG.MakeSL_StdGens(p,ext,2,2);
  slp := RECOG.FindStdGensUsingBSGS(g,std.all,false,true);
  if slp = fail then return fail; fi;
  res := rec( g := g, one := One(f), One := One(g), f := f, q := q,
              p := p, ext := ext, d := 2, bas := IdentityMat(2,f),
              basi := IdentityMat(2,f) );
  res.all := ResultOfStraightLineProgram(slp,GeneratorsOfGroup(g));
  res.s := res.all{[1..ext]};
  res.t := res.all{[ext+1..2*ext]};
  res.a := res.all[2*ext+1];
  res.b := res.all[2*ext+2];
  return res;
end;



RECOG.FindStdGensUsingBSGS := function(g,stdgens,projective,large)
  # stdgens generators for the matrix group g
  # returns an SLP expressing stdgens in the generators of g
  # set projective to true for projective mode
  # set large to true if we should not bother finding nice base points!
  local S,dim,gens,gm,i,l,strong;
  dim := DimensionOfMatrixGroup(g);
  if IsObjWithMemory(GeneratorsOfGroup(g)[1]) then
      gm := GroupWithMemory(StripMemory(GeneratorsOfGroup(g)));
  else
      gm := GroupWithMemory(g);
  fi;
  if HasSize(g) then SetSize(gm,Size(g)); fi;
  if large then
      S := StabilizerChain(gm,rec( Projective := projective,
        Cand := rec( points := One(g),
                     ops := ListWithIdenticalEntries(dim, OnLines) ) ) );
  else
      S := StabilizerChain(gm,rec( Projective := projective ) );
  fi;
  strong := ShallowCopy(StrongGenerators(S));
  ForgetMemory(S);
  l := List(stdgens,x->SiftGroupElementSLP(S,x));
  gens := EmptyPlist(Length(stdgens));
  for i in [1..Length(stdgens)] do
      if not l[i].isone then
          return fail;
      fi;
      Add(gens,ResultOfStraightLineProgram(l[i].slp,strong));
  od;
  return SLPOfElms(gens);
end;
