#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This files's authors include Daniel Rademacher, Max Neunhöffer, Ákos Seress.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
#############################################################################



#############################################################################
#############################################################################
######## General utils ######################################################
#############################################################################
#############################################################################



InstallMethod( CharacteristicPolynomial, "for a memory element matrix",
  [ IsMatrix and IsObjWithMemory ],
  function(m)
    return CharacteristicPolynomial(m!.el);
  end );



InstallOtherMethod( \-, "for two memory elements",
  [ IsMatrix and IsObjWithMemory, IsMatrix and IsObjWithMemory ],
  function(m,n)
    return m!.el - n!.el;
  end );



InstallMethod( Eigenspaces, "for a field and a memory element matrix",
  [ IsField, IsMatrix and IsObjWithMemory ],
  function( f, m )
    return Eigenspaces(f,m!.el);
  end );


# compute the eigenspace of `mat` for the given eigenvalue lambda`
RECOG.EigenspaceMat := function(mat, lambda)
    local i;
    mat := MutableCopyMat( mat );
    # since mat is a copy, we can efficiently "subtract an identity matrix"
    for i in [1..NrRows(mat)] do
        mat[i,i] := mat[i,i] - lambda;
    od;
    # since mat is a copy we can use NullspaceMatDestructive instead of NullspaceMat
    return NullspaceMatDestructive(mat);
end;

# compute fixed space of mat, i.e. eigenspace for eigenvalue 1
RECOG.FixspaceMat := function(mat)
    return RECOG.EigenspaceMat(mat, 1);
end;



#############################################################################
#############################################################################
######## CheckStingrayGroup #################################################
#############################################################################
#############################################################################


RECOG.CheckNewStingrayGroup := function(g1,base1,g2,base2,q)
local baseSum, module;

    baseSum := Concatenation(base1,base2);
    baseSum := TriangulizedMat(baseSum);
    if IsZero(Last(baseSum)) then
        return false;
    fi;

    g1 := TransposedMat(StripMemory(g1));
    g2 := TransposedMat(StripMemory(g2));
    module := GModuleByMats( [g1,g2], GF(q) );
    module := MTX.InducedActionSubmoduleNB( module, baseSum );
    return MTX.IsIrreducible(module);
end;



#############################################################################
#############################################################################
######## ConstructSmallSub ##################################################
#############################################################################
#############################################################################



RECOG.ConstructSmallSub := function(r1, r2, product, newbasis, detectFun)
    local gens, pseudoorderlist, Hsub, productEle, ele, ele2, H, cord1, cord2;

    gens := [];
    pseudoorderlist := [];
    Hsub := [];
    repeat
        productEle := PseudoRandom(product);
        Add(Hsub, productEle);
        ele := (productEle)^(newbasis^(-1));
        ele2 := ele{r2}{r2};
        ele := ele{r1}{r1};
        Add(pseudoorderlist, RECOG.EstimateOrder(ele2)[1]);
        Add(gens,ele);
    until Size(gens) = 2;
    H := GroupByGenerators(gens);
    if detectFun(H) = true then
        cord1 := Order(gens[1]);
        cord2 := Order(gens[2]);
        if (Gcd(cord1,pseudoorderlist[1]) <> pseudoorderlist[1]) and (Gcd(cord2,pseudoorderlist[2]) <> pseudoorderlist[2]) then
            gens[1] := gens[1]^pseudoorderlist[1];
            gens[2] := gens[2]^pseudoorderlist[2];
            H := GroupByGenerators(gens);
            if detectFun(H) = true then
                Hsub[1] := Hsub[1]^pseudoorderlist[1];
                Hsub[2] := Hsub[2]^pseudoorderlist[2];
                return [Hsub,H,newbasis];
            fi;
        fi;
    fi;
    return fail;
end;



#############################################################################
#############################################################################
######## constructppdTwoStingray ############################################
#############################################################################
#############################################################################



RECOG.constructppdTwoStingray := function(g,dim,q,type,form)
  local out, list, out2, currentdim, aimdim, godown;

  if type = "SL" then
    aimdim:=-1;
  elif type = "O" then
    aimdim:=8;
  elif type = "Sp" then
    aimdim:=8;
  elif type = "SU" then
    if IsEvenInt(q) then
      aimdim := 10;
    else
      aimdim := 6;
    fi;
  else
    Error("unsupported type ", type);
  fi;

  Info(InfoRecog,2,"Current Dimension: ", dim, " for type ", type);
  Info(InfoRecog,2,"\n");

  list:=[g,dim,q,fail,form];
  currentdim := dim;
  repeat
     out:=RECOG.godownStingray(list,type);
     if out=fail or IsOne(out[1]^2) then
        Info(InfoRecog,2,"Restart. \n");
        Info(InfoRecog,2,"Current Dimension: ");
        Info(InfoRecog,2,dim);
        Info(InfoRecog,2,"\n");
        list:=[g,dim,q,fail,form];
        out:=fail;
     else
        if type = "SL" and out[2] = 2 then
          return out[1];
        fi;
        Assert(0, out[1] >= 2);
        repeat
             out2:=RECOG.godownStingray(list,type);
             if out2=fail or out2[1]*out2[1]=One(out2[1]) then
                 if InfoLevel(InfoRecog) >= 3 then Print("B\c"); fi;
                 list:=[g,dim,q,fail,form];
                 out2:=fail;
             fi;
        until out2<>fail and out2[2] >= 2;
        if type = "SL" and out2[2] = 2 then
            return out2[1];
        fi;
        if RECOG.CheckNewStingrayGroup(out[1],out[3],out2[1],out2[3],q) then
             list:=[Group(out[1],out2[1]),out[2]+out2[2],q,fail,form];
             currentdim := list[2];

             Info(InfoRecog,2,"Debug Info:\n");
             Info(InfoRecog,2,"Dimension FirstElement: ");
             Info(InfoRecog,2,out[2]);
             Info(InfoRecog,2,"\n");
             Info(InfoRecog,2,"Dimension SecondElement: ");
             Info(InfoRecog,2,out2[2]);
             Info(InfoRecog,2,"\n");
             Info(InfoRecog,2,"End Debug Info. \n");
           
             Info(InfoRecog,2,"New Dimension: ");
             Info(InfoRecog,2,out[2]+out2[2]);
             Info(InfoRecog,2,"\n");
        else
             if InfoLevel(InfoRecog) >= 3 then Print("B\c"); fi;
             Info(InfoRecog,2,"Restart. \n");
             Info(InfoRecog,2,"Current Dimension: ");
             Info(InfoRecog,2,dim);
             Info(InfoRecog,2,"\n");
             list:=[g,dim,q,fail,form];
             out:=fail;
        fi;
     fi;
  until currentdim=aimdim;

  return list[1];

end;



#############################################################################
#############################################################################
######## godownStingray #####################################################
#############################################################################
#############################################################################



# finds first element of a list that is relative prime to all others
# input: list=[Sp(d,q), d, q, Sp(n,q)] acting as a subgroup of some big Sp(n,q)
# output: list=[rr, dd] for a ppd(2*dd;q)-element rr
RECOG.godownStingray := function(list,type)
local d, firstSL, firstSU, q, p, g, i, r, pol, factors, degrees, newdim, power, rr, ss, max,
newgroup, colldegrees, exp, count, check, ocount, beta, NiList, Maxi, qFactors, 
irrfact, invbase, form, CheckOtherFactors, CheckFactors, fld, restricted, b, j;

    CheckOtherFactors := function(i, deg, fact)
    local j;
    for j in [1..Length(deg)] do
        if not(j = i) then
            if RECOG.CheckPolynomialForSelfConjugate(fact[j]) then
                if (deg[j] mod deg[i] = 0) then
                    return false;
                fi;
            else
                if (deg[j] mod Int(deg[i]/2) = 0) then
                    return false;
                fi;
            fi;
        fi;
    od;
    return true;
    end;

    CheckFactors := function(deg, fact)
    local i;
        for i in [1..Length(deg)] do
            if ((deg[i] mod 2) = 0) and RECOG.CheckPolynomialForSelfConjugate(fact[i]) and CheckOtherFactors(i,deg,fact) then
            return i;
            fi;
        od;
        return fail;
    end;

    firstSU := function(list)
    local i, j, goodElement;
        for i in [1..Length(list)] do
            if list[i]>1 and (list[i] mod 2 = 1) then
                if Gcd(list[i],Product(list)/list[i]) < list[i] then
                    return i;
                else
                    goodElement := true;
                    for j in [1..Length(list)] do
                        if not(j = i) and Gcd(list[i],list[j]) = list[i] then
                            goodElement := false;
                            break;
                        fi;
                    od;
                    if goodElement then
                        return i;
                    fi;
                fi;
            fi;
        od;
        return fail;
    end;

    firstSL := function(list)
    local i, j, goodElement;
        for i in [1..Length(list)] do
            if list[i]>1 then
                if Gcd(list[i],Product(list)/list[i]) < list[i] then
                    return i;
                else
                    goodElement := true;
                    for j in [1..Length(list)] do
                        if not(j = i) and Gcd(list[i],list[j]) = list[i] then
                            goodElement := false;
                            break;
                        fi;
                    od;
                    if goodElement then
                        return i;
                    fi;
                fi;
            fi;
        od;
        return fail;
    end;

    g:=list[1];
    d:=list[2];
    q:=list[3];
    qFactors:=Factors(q);
    p := qFactors[1];
    form := list[5];
    fld := GF(q);

    if type = "SL" then
        max := Maximum([Log2Int(d),3]);
    elif type = "Sp" then
        max := Maximum([2*Log2Int(d),3]);
    elif type = "SU" then
        max := Maximum([2*Log2Int(d),3]);
    elif type = "O" then
        max := Maximum([2*Log2Int(d),3]);
    else
        Error("type not supported");
    fi;

    # Overall count. Replace by formula and unequality
    ocount := 0;
    while ocount < 100 do

        Info(InfoRecog,2,"Dimension: ",d);
        #find an element with irreducible action of relative prime dimension to
        #all other invariant subspaces
        #count is just safety, if things go very bad
        count:=0;

        repeat
            count:=count+1;
            r:=PseudoRandom(g);
            pol:=CharacteristicPolynomial(r);
            factors:=Factors(pol);
            degrees:=List(factors,Degree);
            if type = "SL" then
                newdim:= firstSL(degrees);
            elif type = "SU" then
                newdim:= firstSU(degrees); 
            elif type = "O" or type = "Sp" then
                newdim := CheckFactors(degrees, factors);
            else
                Error("type not supported");
            fi;
        until (count>100) or (newdim <> fail and (degrees[newdim] < max));
        # Be careful if Log2Int(d) = 2! In this case we search for stingray elements with k < 2. Hence use newdim < Maximum([Log2Int(d),3])

        if count>100 then
            return fail;
        fi;
        
        # Split result from first:
        irrfact := factors[newdim];
        newdim := degrees[newdim];

        if newdim = 2 and type = "SL" then
            check := true;
        else
            # Check whether the stingray candidate is a ppd-stingray element
            check := RECOG.IsPpdStingrayElement(p,Length(qFactors),newdim,irrfact);
        fi;

        if check then
        
            # raise r to a power so that acting trivially outside one invariant irreducible subspace
            NiList := Collected(degrees);
            NiList := Filtered(NiList,x->not(x[1] = newdim));
            colldegrees := List(NiList,x->x[1]);
            NiList := List(NiList,x->x[2]);
            Maxi := Maximum(NiList);
            beta := LogInt(Maxi,p);
            if not(p^beta = Maxi) then
                beta := beta + 1;
            fi;
            
            # power further to cancel q-part of element order
            power := Lcm(List(colldegrees, x->q^x-1))*p^beta;
            rr:=r^power;

            invbase := NullspaceMat(TransposedMat(RECOG.FixspaceMat(StripMemory(rr))));

            if newdim = 2 and type = "SL" then
                if Size(invbase) = 2 then
                    return [rr,newdim,invbase];
                fi;
            else

                #if (type = "SL") or (IsEvenInt(q) and type = "SU") then
                #    return [rr,newdim,invbase];
                #fi;
                
                #b := Basis(VectorSpace(fld,invbase),invbase);
                #restricted := IdentityMat(newdim,fld);
                #for i in [1..newdim] do
                #    for j in [1..newdim] do
                #        restricted[i,j] := b[i]*form*b[j];
                #    od;
                #od;
                
                #if IsEmpty(NullspaceMat(restricted)) then
                    return [rr,newdim,invbase];
                #else
                #    Error("here");
                #fi;
            fi;
        fi;
        
        ocount := ocount + 1;
    od;

    return fail;

end;



#############################################################################
#############################################################################
######## PPD Check ##########################################################
#############################################################################
#############################################################################



RECOG.CheckPPDdqe := function(m,d,q,e)
local factors, i, ele, good, ord;
    
    factors := Factors(q^e-1);
    ord := Order(m);
    for ele in factors do
        good := true;
        for i in [1..(e-1)] do
            if ((q^i-1) mod ele) = 0 then
                good := false;
                break;
            fi;
        od;
        if good then
            if (ord mod ele) = 0 then
                return true;
            fi;
        fi;
    od;
    
    return false;
end;



#############################################################################
#############################################################################
######## Coefficients Primitive Element #####################################
#############################################################################
#############################################################################



# The following function has been written by Thomas Breuer.
# It expresses an element alpha in a field fld as
# a linear combination of a Primitive Element.

# Input: fld: A field,
#        alpha : An element of fld

# Output: Coefficients: A vector c sth for omega primitive element
#            alpha = sum c[i] omega^(i-1)

RECOG.CoefficientsPrimitiveElement := function ( fld, alpha )

    if Size( fld ) <= MAXSIZE_GF_INTERNAL then

        return Coefficients( CanonicalBasis( fld ), alpha );
    else

        alpha := FFECONWAY.WriteOverLargerField( alpha, DegreeOverPrimeField( fld ) );

        if IsCoeffsModConwayPolRep( alpha ) then
            return alpha![1];
      elif IsModulusRep(alpha) then
        return [alpha];
        else
            Error( "this should not happen" );
        fi;
    fi;

end;



#############################################################################
#############################################################################
######## Check PPD-Property and tests #######################################
#############################################################################
#############################################################################



##  This function takes as input:
##
##  <F>  field
##  <f>  a characteristic polynomial
##  <d>  degree of <m>
##  <p>  a prime power
##  <a>  an integer
##  <irrfact> an irreducible factor of <f> and of degree a

RECOG.IsPpdStingrayElement := function( p, f, k, irrfact )
    local c, e,  R,  pm,  g, islarge, F;

    F := GF(p^f);
    c := irrfact;
    R := PolynomialRing(F);

    e  := k;
    ## find the noppds and ppds parts
    pm := PrimitivePrimeDivisors( f*e, p );
    ## pm contains two fields, noppds and ppds.
    ## ppds is the product of all ppds of p^(ae)-1
    ## and noppds is p^(ae)-1/ppds.

    ## get rid of the non-ppd part
    ## g will be x^noppds in F[x]/<c>
    g := PowerMod( Indeterminate(F), pm.noppds, c );

    ## now we know that <m> is a ppd-element

    ## if g is one there is no ppd involved
    if IsOne(g) then
        return false;
    else
        return true;
    fi;

    #if IsOne(g)  then
    #    ## (e+1) is the only ppd dividing |<m>| and only once
    #    islarge := false;
    #    return [ e, islarge ];
    #else
    #    ## Either another ppd also divides |<m>| and this one is large or
    #    ## (e+1)^2 divides |<m>| and hence still large
    #    islarge := true;
    #    return [ e, islarge  ];
    #fi;


end;



RECOG.ComparePPDFunction := function(m,d,q,e,irrfact)
    local f,p,factors;
    
    factors := Factors(q);
    p := factors[1];
    f := Length(factors);

    if not(RECOG.CheckPPDdqe(m,d,q,e) = RECOG.IsPpdStingrayElement(p,f,e,irrfact[1])) then
        Error("PPD error");
    fi;
    
end;



#############################################################################
#############################################################################
######## Linear action representation #######################################
#############################################################################
#############################################################################



RECOG.LinearAction := function(bas,field,el)
  local mat,vecs;
  if IsGroup(el) then
      return Group(List(GeneratorsOfGroup(el),
                        x->RECOG.LinearAction(bas,field,x)));
  fi;
  if IsBasis(bas) then
      vecs := BasisVectors(bas);
  else
      vecs := bas;
      bas := Basis(VectorSpace(field,bas),bas);
  fi;
  mat := List(vecs,v->Coefficients(bas,v*el));
  ConvertToMatrixRep(mat,field);
  return mat;
end;



RECOG.LinearActionRepresentation := function(G)
local OldGens, newGens, i, base, fld, d, EleBase, fixbase, B, action, ele, V;
    
    OldGens := ShallowCopy(GeneratorsOfGroup(G));
    for i in [1..Length(OldGens)] do
        if IsObjWithMemory(OldGens[i]) then
            OldGens[i] := StripMemory(OldGens[i]);
        fi;
    od;
    
    fld := FieldOfMatrixList(OldGens);
    d := Size(OldGens[1]);
    base := [];
    for i in [1..Length(OldGens)] do
        ele := OldGens[i];
        fixbase := RECOG.FixspaceMat(TransposedMat(ele));
        if fixbase = [] then
            return fail;
        fi;
        EleBase := NullspaceMat(TransposedMat(fixbase));
        Append(base,EleBase);
    od;
    
    V := VectorSpace(fld,base);
    B := Basis(V);
    base := BasisVectors(B);
    newGens := [];
    for i in [1..Length(OldGens)] do
        ele := OldGens[i];
        action := List(base,v->Coefficients(B,v*ele));
        Add(newGens,action);
    od;
    
    return GroupByGenerators(newGens);
end;



RECOG.LinearActionRepresentationSmallerMatrices := function(G)
local OldGens, newGens, i, base, fld, d, EleBase, fixbase, B, action, ele, V, baseCopy;
    
    OldGens := ShallowCopy(GeneratorsOfGroup(G));
    for i in [1..Length(OldGens)] do
        if IsObjWithMemory(OldGens[i]) then
            OldGens[i] := StripMemory(OldGens[i]);
        fi;
    od;
    # Einfach StripMemory OldGens := StripMemory(GeneratorsOfGroup(G))
    
    fld := FieldOfMatrixList(OldGens);
    d := NumberRows(OldGens[1]);
    base := [];
    for i in [1..Length(OldGens)] do
        ele := OldGens[i];
        fixbase := RECOG.FixspaceMat(TransposedMat(ele));
        EleBase := NullspaceMat(TransposedMat(fixbase));
        Append(base,EleBase);
    od;
    baseCopy := base;
    
    V := VectorSpace(fld,base);
    B := Basis(V);
    base := BasisVectors(B);
    newGens := [];
    for i in [1..Length(OldGens)] do
        ele := OldGens[i];
        action := List(base,v->Coefficients(B,v*ele));

        # DR: Change here so that we still operate from the same side
        Add(newGens,action);
    od;
    
    return [GroupByGenerators(newGens),Size(B),baseCopy];
end;



RECOG.LinearActionRepresentationSmallerMatricesVersion2 := function(G)
local OldGens, newGens, i, base, fld, d, EleBase, fixbase, B, action, ele, V;
    
    OldGens := ShallowCopy(GeneratorsOfGroup(G));
    for i in [1..Length(OldGens)] do
        if IsObjWithMemory(OldGens[i]) then
            OldGens[i] := StripMemory(OldGens[i]);
        fi;
    od;
    # Einfach StripMemory OldGens := StripMemory(GeneratorsOfGroup(G))
    
    fld := FieldOfMatrixList(OldGens);
    d := NumberRows(OldGens[1]);
    base := [];
    for i in [1..Length(OldGens)] do
        ele := OldGens[i];
        fixbase := RECOG.FixspaceMat(TransposedMat(ele));
        EleBase := NullspaceMat(TransposedMat(fixbase));
        Append(base,EleBase);
    od;
    
    V := VectorSpace(fld,base);
    B := Basis(V);
    base := BasisVectors(B);
    newGens := [];
    for i in [1..Length(OldGens)] do
        ele := OldGens[i];
        action := List(base,v->Coefficients(B,v*ele));

        # DR: Change here so that we still operate from the same side
        Add(newGens,action);
    od;
    
    return [GroupByGenerators(newGens),Size(B),BasisVectors(B)];
end;



#############################################################################
#############################################################################
######## Self-conjugate polynomial check ####################################
#############################################################################
#############################################################################



RECOG.CheckPolynomialForSelfConjugate := function (f)
local ind, coeff, aZero, i, fld, deg, pol;

    fld := FieldOfPolynomial(f);
    ind := IndeterminateOfLaurentPolynomial(f);
    coeff := CoefficientsOfLaurentPolynomial(f)[1];
    deg := Length(coeff);
    aZero := coeff[1];
    
    pol := ind^0 * Zero(fld);
    for i in [1..deg] do
        pol := pol + ind^(deg-i)*coeff[i];
    od;
    
    pol := aZero * pol;

    if pol = f then
        return true;
    else
        return false;
    fi;
end;



#############################################################################
#############################################################################
######## Extract and rescale block matrices #################################
#############################################################################
#############################################################################



RECOG.ComputeBlockBaseChangeMatrix := function(list,d,q)
local fixbase, elebase, basis, matrix, fix, moved, currentmove, currentfix, k, newbase, OldGens, i;

    OldGens := ShallowCopy(list);
    for i in [1..Length(OldGens)] do
        if IsObjWithMemory(OldGens[i]) then
            OldGens[i] := StripMemory(OldGens[i]);
        fi;
    od;
    list := OldGens;

    fix := [];
    moved := [];

    for matrix in list do;
        fixbase := RECOG.FixspaceMat(TransposedMat(matrix));
        elebase := NullspaceMat(TransposedMat(fixbase));
        Add(moved, elebase);

        fixbase := RECOG.FixspaceMat(matrix);
        Add(fix,fixbase);
    od;

    if Size(moved) = 1 then
        newbase := MutableCopyMat(moved[1]);
        Append(newbase,fix[1]);
        return newbase;
    else
        currentmove := MutableCopyMat(moved[1]);
        currentfix := MutableCopyMat(fix[1]);
        k := 1;
        while k < Size(moved) do
            currentmove := SumIntersectionMat(currentmove,moved[k+1])[1];
            currentfix := SumIntersectionMat(currentfix,fix[k+1])[2];
            k := k + 1;
        od;
        Append(currentmove,currentfix);
        return currentmove;
    fi;

end;



RECOG.ExtractSmallerGroup := function(list,basechange,size)
local gens, ele, block, OldGens, i;

    OldGens := ShallowCopy(list);
    for i in [1..Length(OldGens)] do
        if IsObjWithMemory(OldGens[i]) then
            OldGens[i] := StripMemory(OldGens[i]);
        fi;
    od;
    list := OldGens;

    gens := [];
    for ele in list do
        block := (ele^(basechange^(-1)));
        block := block{[1..size]}{[1..size]};
        Add(gens,block);
    od;

    return [GroupByGenerators(gens),gens];
end;



RECOG.LiftGroup := function(list,size,q,d)
local gens, ele, block, OldGens, i;

    OldGens := ShallowCopy(list);
    for i in [1..Length(OldGens)] do
        if IsObjWithMemory(OldGens[i]) then
            OldGens[i] := StripMemory(OldGens[i]);
        fi;
    od;
    list := OldGens;

    gens := [];
    for ele in list do
        block := IdentityMat(d,GF(q));
        block{[1..size]}{[1..size]} := ele;
        Add(gens,block);
    od;

    return [GroupByGenerators(gens),gens];
end;



#############################################################################
#############################################################################
######## Membership test in groups preserving a form ########################
#############################################################################
#############################################################################


# given a matrix `mat`, test if it is contained in G, which must be Omega(e,n,fld)
#
# TODO: add unit tests
#
# e:=+1; d:=8; q:=8;
# G:=Omega(e,d,q);
# H:=SO(e,d,q,InvariantQuadraticForm(G).matrix);
# ForAll(GeneratorsOfGroup(G), g -> g in H);
# ForAll(GeneratorsOfGroup(G), g -> IsInOmega(G, g));
# ForAll(GeneratorsOfGroup(H), g -> IsInOmega(G, g));
#
RECOG.IsInOmega:=function(G,mat)
  local d, Q, form, fld;
  d := DimensionOfMatrixGroup(G);
  fld := FieldOfMatrixGroup(G);
  Assert(0, NrRows(mat) = d);

  # first verify the quadratic form is preserved
  Q := InvariantQuadraticForm(G).matrix;
  if not RespectsQuadraticForm(Q, mat) then
    return false;
  fi;

  if Characteristic(fld) <> 2 then
    form := InvariantBilinearForm(G).matrix;
    return IsOne(SpinorNorm(form, fld, mat));
  elif IsOddInt(d) then
    # Omega(0,2n+1,2^k) = SO(0,2n+1,2^k) = GO(0,2n+1,2^k)
    return true;
  else
    # the following is based on Lemma 3.5(2) in Holt, Roney-Dougal:
    # "Constructing maximal subgroups of orthogonal groups"
    return IsEvenInt(RankMat(mat + One(G)));
  fi;
end;



#############################################################################
#############################################################################
# Code from ClassicalMaximal to check BilinearForm ##########################
# https://github.com/gap-packages/ClassicalMaximals/blob/main/gap/Forms.gi ##
#############################################################################
#############################################################################



RECOG.MatrixByEntries := function(field, nrRows, nrCols, entries)
    local i, m, o;
    o := One(field);
    m := NullMat(nrRows, nrCols, field);
    for i in entries do
        m[i[1],i[2]] := i[3]*o;
    od;
    return ImmutableMatrix(field, m);
end;



RECOG.AntidiagonalMat := function(entries, field)
    local d, m, i;
    if IsInt(entries) then
        d := entries;
        entries := ListWithIdenticalEntries(d, One(field));
    else
        d := Length(entries);
    fi;
    m := NullMat(d, d, field);
    for i in [1..d] do
        m[i, d - i + 1] := entries[i];
    od;
    return ImmutableMatrix(field, m);
end;



# Solving the congruence a ^ 2 + b ^ 2 = c in F_q by trial and error.
#
# A solution always exists by a simple counting argument using the pigeonhole
# principle and the fact that there are (q + 1) / 2 > q / 2 squares in F_q (for
# q odd; the case q even is trivial). The trial and error approach taken here 
# should in principle almost always terminate quickly: Assuming that - 1 - a ^ 2 
# is evenly distributed in GF(q), the chance to hit a quadratic residue is about 
# 1 / 2 in each trial.
RECOG.SolveQuadraticCongruence := function(c, q)
    local F, a, b;
    F := GF(q);
    for a in F do
        b := RootFFE(F, (c - a ^ 2) * Z(q) ^ 0, 2);
        if not b = fail then
            break;
        fi;
    od;
    return rec(a := a, b := b);
end;



RECOG.ApplyFunctionToEntries := function(M, func)
    local numberRows, numberColumns, i, j, result;
    if not IsMatrix(M) or Length(M) = 0 then
        ErrorNoReturn("<M> must be a matrix but <M> = ", M);
    fi;

    numberRows := NrRows(M);
    numberColumns := NrCols(M);
    result := NullMat(numberRows, numberColumns, DefaultFieldOfMatrix(M));
    for i in [1..numberRows] do
        for j in [1..numberColumns] do
            result[i, j] := func(M[i, j]);
        od;
    od;

    return result;
end;



RECOG.HermitianConjugate := function(M, q)
    return TransposedMat(RECOG.ApplyFunctionToEntries(M, x -> x ^ q));
end;



# If type = "S" then find a beta in GF(q ^ 2) with beta + beta ^ q = alpha.
# If type = "P" then find a beta in GF(q ^ 2) with gamma * gamma ^ q = alpha.
# In both cases, alpha is an element of GF(q).
# Construction as in Lemma 2.2 of [HR05]
RECOG.SolveFrobeniusEquation := function(type, alpha, q)
    local F, R, S, x, delta, polynomial, result;

    F := GF(q);
    if not alpha in F then
        ErrorNoReturn("<alpha> must be an element of GF(<q>) but <alpha> = ",
                      alpha, " and <q> = ", q);
    fi;
    if not type in ["S", "P"] then
        ErrorNoReturn("<type> must be one of 'S' or 'P' but <type> = ", type);
    fi;
    # We have to make an exception for this case since the construction below
    # does not work here: x ^ 2 + delta is never irreducible over GF(q) since
    # all elements of GF(q) are squares for q even.
    if type = "S" and alpha = 0 and IsEvenInt(q) then
        return Z(q) ^ 0;
    fi;

    R := PolynomialRing(F, ["x"]);
    S := PolynomialRing(GF(q ^ 2), ["x"]);
    x := Indeterminate(F, "x");

    # A quick argument using the quadratic formula for q odd or some
    # algebraic manipulations and the non-surjectivity of the Artin-Schreier
    # map x -> x ^ 2 + x for q odd and alpha <> 0 shows that the construction
    # below always works.
    if type = "S" then
        for delta in F do
            polynomial := x ^ 2 - alpha * x + delta;
            if IsIrreducibleRingElement(R, polynomial) then
                result := -CoefficientsOfUnivariatePolynomial(Factors(S, polynomial)[1])[1];
                return result;
            fi;
        od;
    # A similar argument to the one used for type "S" works here as well. Note,
    # however, that the argument for q odd via the quadratic formula now
    # additionally needs that the squares in GF(q) do not form an arithmetic
    # progression (which is "closed", i.e. not only a_i+1 = a_i + d, but also
    # a_n + d = a_1), which can be proved in the following way: If they did,
    # then they would be given by -kd, ..., -d, 0, d, 2d, ..., ((q - 1) / 2 - k) * d
    # for some 0 <= k <= (q - 1) / 2; since they form a multiplicative
    # subgroup, we can divide by -d or d, respectively, and see that 
    # -+k, ..., -+1, 0, +-1, +-2, ..., +-((q - 1) / 2 - k) are also all the
    # squares in GF(q). Most notably they all are in GF(p) and thus there are
    # at most p squares in GF(q), which is < (q + 1) / 2 if q >= p ^ 2 - a
    # contradiction. Now we can restrict ourselves to q = p and reach a
    # contradiction for p >= 7 (we leave out the details); this leaves p = 3
    # and p = 5, which can easily be checked manually.
    elif type = "P" then
        for delta in F do
            polynomial := x ^ 2 + delta * x + alpha;
            if IsIrreducibleRingElement(R, polynomial) then
                result := -CoefficientsOfUnivariatePolynomial(Factors(S, polynomial)[1])[1];
                return result;
            fi;
        od;
    fi;
end;



# An n x n - matrix of zeroes with a 1 in position (row, column)
RECOG.SquareSingleEntryMatrix := function(field, n, row, column)
    return RECOG.MatrixByEntries(field, n, n, [[row, column, 1]]);
end;



# Compute Ceil(m / n) for two integers m, n
RECOG.QuoCeil := function(m, n)
    if m mod n = 0 then
        return QuoInt(m, n);
    else
        return QuoInt(m, n) + 1;
    fi;
end;



# Compute the size of Sp(n, q) according to Theorem 1.6.22 in [BHR13]
RECOG.SizeSp := function(n, q)
    local m, result, powerOfq, i;
    if IsOddInt(n) then
        ErrorNoReturn("Dimension <n> must be even but ", n, " was given.");
    fi;
    m := QuoInt(n, 2);
    result := q ^ (m * m);
    powerOfq := 1;
    for i in [1..m] do
        powerOfq := powerOfq * q * q;
        result := result * (powerOfq - 1);
    od;
    return result;
end;



# Compute the size of PSp(n, q) according to Table 1.3 in [BHR13],
RECOG.SizePSp := function(n, q)
    return QuoInt(RECOG.SizeSp(n, q), Gcd(2, q - 1));
end;



# Compute the size of SU(n, q) according to Theorem 1.6.22 in [BHR13]
# using the formula for GU(n, q) but starting with i = 2
# because Table 1.3 gives [GU(n, q):SU(n, q)] = q + 1.
RECOG.SizeSU := function(n, q)
    local result, powerOfq, sign, i;
    result := q ^ QuoInt(n * (n - 1), 2);
    powerOfq := q;
    sign := 1;
    for i in [2..n] do
        powerOfq := powerOfq * q;
        sign := -sign;
        result := result * (powerOfq + sign);
    od;
    return result;
end;



# Compute the size of PSU(n, q) according to Table 1.3 in [BHR13]
# Namely, we have | G / Z(G) : S / Z(S) | = | G : S | * |Z(S)| / |Z(G)| so due
# to | G : S | = q + 1, |Z(G)| = q + 1 and | G / Z(G) : S / Z(S) | = (q + 1, n), 
# which are given in said table, this gives |Z(S)| = (q + 1, n). 
RECOG.SizePSU := function(n, q)
    return RECOG.SizeSU(n, q) / Gcd(n, q + 1);
end;



# Compute the size of GU(n, q) according to Table 1.3 in [BHR13]
RECOG.SizeGU := function(n, q)
    return (q + 1) * RECOG.SizeSU(n, q);
end;



# Compute the size of GO(epsilon, n, q) according to Theorem 1.6.22 in [BHR13]
RECOG.SizeGO := function(epsilon, n, q)
    local m, result, powerOfq, i;
    if epsilon = 0 then

        if IsEvenInt(n) then
            ErrorNoReturn("for <epsilon> = ", epsilon, " the dimension <n> must be odd but ", n, " was given.");
        fi;

        if IsEvenInt(q) then
            return RECOG.SizeSp(n - 1, q);
        fi;

        m := QuoInt(n - 1, 2);
        result := 2 * q ^ (m * m);

    elif epsilon in [-1, 1] then

        if IsOddInt(n) then
            ErrorNoReturn("for <epsilon> = ", epsilon, " the dimension <n> must be even but ", n, " was given.");
        fi;

        m := QuoInt(n, 2);
        result := 2 * q ^ (m * (m - 1)) * (q ^ m - epsilon);
        m := m - 1;
    else
        ErrorNoReturn("<epsilon> must be in [-1, 0, 1] but ", epsilon, " was given.");
    fi;

    powerOfq := 1;
    for i in [1..m] do
        powerOfq := powerOfq * q * q;
        result := result * (powerOfq - 1);
    od;

    return result;
end;



# Compute the size of SO(epsilon, n, q) according to Table 1.3 in [BHR13]
RECOG.SizeSO := function(epsilon, n, q)
    return QuoInt(RECOG.SizeGO(epsilon, n, q), Gcd(2, q - 1));
end;



RECOG.ReflectionMatrix := function(n, q, gramMatrix, v)
    local F, reflectionMatrix, i, basisVector, reflectBasisVector, beta;
    F := GF(q);
    reflectionMatrix := NullMat(n, n, F);
    beta := BilinearFormByMatrix(gramMatrix);
    if IsZero(EvaluateForm(beta, v, v)) then
        ErrorNoReturn("The vector <v> must have non-zero norm with respect to",
                      " the bilinear form given by <gramMatrix>");
    fi;
    for i in [1..n] do
        basisVector := List([1..n], j -> Zero(F));
        basisVector[i] := Z(q) ^ 0;
        reflectBasisVector := basisVector 
                              - 2 * EvaluateForm(beta, v, basisVector) 
                              / EvaluateForm(beta, v, v) * v;
        reflectionMatrix[i]{[1..n]} := reflectBasisVector;
    od;
    return reflectionMatrix;
end;



# Construct generators for the orthogonal groups with the properties listed in
# Lemma 2.4 of [HR05].
# Construction as in: C. M. Roney-Dougal. "Conjugacy of Subgroups of the
# General Linear Group." Experimental Mathematics, vol. 13 no. 2, 2004, pp.
# 151-163. Lemma 2.4.
# We take the notation from [HR05].
RECOG.GeneratorsOfOrthogonalGroup := function(epsilon, n, q)
    local F, gramMatrix, generatorsOfSO, vectorOfSquareNorm, D, E, zeta, a, b,
    solutionOfQuadraticCongruence;
    if IsEvenInt(q) then
        ErrorNoReturn("This function was only designed for <q> odd but <n> = ", 
                      n, "and <q> = ", q);
    fi;

    F := GF(q);
    zeta := PrimitiveElement(F);
    if IsOddInt(n) then
            gramMatrix := IdentityMat(n, F);
            generatorsOfSO := GeneratorsOfGroup(RECOG.ConjugateToSesquilinearForm(SO(epsilon, n, q),
                                                                            "O",
                                                                            gramMatrix));
            D := - IdentityMat(n, F);
            E := zeta * IdentityMat(n, F);
    else 
        if epsilon = 1 then
            gramMatrix := RECOG.AntidiagonalMat(n, F);
            generatorsOfSO := GeneratorsOfGroup(RECOG.ConjugateToSesquilinearForm(SO(epsilon, n, q),
                                                                            "O",
                                                                            gramMatrix));
            # Our standard bilinear form is given by the Gram matrix 
            # Antidiag(1, ..., 1). The norm of [1, 0, ..., 0, 2] under this
            # bilinear form is 4, i.e. a square. (Recall q odd, so this is not zero!)
            vectorOfSquareNorm := zeta ^ 0 * Concatenation([1], 
                                                           List([1..n - 2], i -> 0), 
                                                           [2]);
            D := RECOG.ReflectionMatrix(n, q, gramMatrix, vectorOfSquareNorm);
            E := DiagonalMat(Concatenation(List([1..n / 2], i -> zeta), 
                                           List([1..n / 2], i -> zeta ^ 0)));
        elif epsilon = -1 then

            # Get a, b in GF(q) with a ^ 2 + b ^ 2 = zeta
            solutionOfQuadraticCongruence := RECOG.SolveQuadraticCongruence(zeta, q);
            a := solutionOfQuadraticCongruence.a;
            b := solutionOfQuadraticCongruence.b;

            if IsOddInt(n * (q - 1) / 4) then
                gramMatrix := IdentityMat(n, F);
                generatorsOfSO := GeneratorsOfGroup(RECOG.ConjugateToSesquilinearForm(SO(epsilon, n, q),
                                                                                "O",
                                                                                gramMatrix));
                # Our standard bilinear form is given by the Gram matrix 
                # Diag(1, ..., 1). The norm of [1, 0, ..., 0] under this bilinear
                # form is 1, i.e. a square.
                vectorOfSquareNorm := zeta ^ 0 * Concatenation([1], 
                                                               List([1..n - 1], i -> 0));
                D := RECOG.ReflectionMatrix(n, q, gramMatrix, vectorOfSquareNorm);
                # Block diagonal matrix consisting of n / 2 blocks of the form 
                # [[a, b], [b, -a]].
                E := RECOG.MatrixByEntries(F, n, n, 
                                     Concatenation(List([1..n], i -> [i, i, (-1) ^ (i + 1) * a]), 
                                                   List([1..n], i -> [i, i + (-1) ^ (i + 1), b])));
            else
                gramMatrix := Z(q) ^ 0 * DiagonalMat(Concatenation([zeta],
                                                                   List([1..n - 1], i -> 1)));
                generatorsOfSO := GeneratorsOfGroup(RECOG.ConjugateToSesquilinearForm(SO(epsilon, n, q),
                                                                                "O",
                                                                                gramMatrix));
                # Our standard bilinear form is given by the Gram matrix 
                # Diag(zeta, 1, ..., 1). The norm of [0, ..., 0, 1] under this
                # bilinear form is 1, i.e. a square.
                vectorOfSquareNorm := zeta ^ 0 * Concatenation(List([1..n - 1], i -> 0), 
                                                               [1]);
                D := RECOG.ReflectionMatrix(n, q, gramMatrix, vectorOfSquareNorm);
                # Block diagonal matrix consisting of one block [[0, zeta], [1, 0]]
                # and n / 2 - 1 blocks of the form [[a, b], [b, -a]].
                E := RECOG.MatrixByEntries(F, n, n, 
                                     Concatenation([[1, 2, zeta], [2, 1, zeta ^ 0]],
                                                   List([3..n], i -> [i, i, (-1) ^ (i + 1) * a]), 
                                                   List([3..n], i -> [i, i + (-1) ^ (i + 1), b])));
            fi;
        fi;
    fi;
    
    return rec(generatorsOfSO := generatorsOfSO, D := D, E := E);
end;
 


RECOG.MatrixGroup := function(F, gens)
    if IsEmpty(gens) then
        ErrorNoReturn("<gens> cannot be empty"); 
    elif not IsField(F) then
        ErrorNoReturn("<F> must be a field");
    fi;
    return Group(List(gens, g -> ImmutableMatrix(F, g)));
end;



RECOG.MatrixGroupWithSize := function(F, gens, size)
    local result;
    result := RECOG.MatrixGroup(F, gens);
    SetSize(result, size);
    return result;
end;



# Assuming that the group G acts absolutely irreducibly, try to find a
#   * symplectic form (if <type> = S) or a
#   * symmetric bilinear form (if <type> = O)
# which is G-invariant or prove that no such form exists.
#
# We use this function instead of PreservedBilinearForms form the Forms package
# since PreservedBilinearForms seems to be buggy and unreliable (see also
# comment above UnitaryForm).
#
# In general, this function should only be used if one can be sure that <G>
# preserves a bilinear form (but one does not know which one).
RECOG.BilinearForm := function(G, type)
    local F, M, inverseTransposeM, counter, formMatrix, condition;

    if not type in ["S", "O"] then
        ErrorNoReturn("<type> must be one of 'S', 'O'");
    fi;
    # Set the condition the Gram matrix needs to satisfy for each of the
    # possible types.
    if type = "S" then
        condition := x -> (x = - TransposedMat(x));
    elif type = "O" then
        condition := x -> (x = TransposedMat(x));
    fi;

    F := DefaultFieldOfMatrixGroup(G);

    # Return stored bilinear form if it exists and is symplectic / symmetric
    if HasInvariantBilinearForm(G) then
        formMatrix := InvariantBilinearForm(G).matrix;
        if condition(formMatrix) then
            return ImmutableMatrix(F, formMatrix);
        fi;
    fi;
    
    M := GModuleByMats(GeneratorsOfGroup(G), F);

    if not MTX.IsIrreducible(M) then
        ErrorNoReturn("BilinearForm failed - group is not irreducible");
    fi;

    # An element A of G acts as A ^ (-T) in MTX.DualModule(M)
    inverseTransposeM := MTX.DualModule(M);

    counter := 0;
    # As the MeatAxe is randomised, we might have to make some more trials to
    # find a preserved symplectic / symmetric bilinear form if there is one;
    # breaking after 1000 trials is just a "safety net" in case a group <G>
    # that does not preserve a symplectic / symmetric bilinear form is input.
    while counter < 1000 do
        counter := counter + 1;

        # If f: M -> inverseTransposeM is an isomorphism, it must respect
        # multiplication by group elements, i.e. for A in G
        #       f(x * A) = f(x) * A ^ (-T)
        # Let f be given by the matrix F, i.e. f: x -> x * F. Then we have
        #       (x * A) * F = x * F * A ^ (-T)
        # Putting these results together for all vectors x gives
        #       A * F = F * A ^ (-T)
        # <==>  A * F * A ^ T = F,
        # which is what we need.
        formMatrix := MTX.IsomorphismModules(M, inverseTransposeM);

        if formMatrix <> fail then
            # check if formMatrix is antisymmetric
            if condition(formMatrix) then
                return ImmutableMatrix(F, formMatrix);
            fi;
            if not MTX.IsAbsolutelyIrreducible(M) then
                ErrorNoReturn("BilinearForm failed - group is not absolutely irreducible");
            fi;
        fi;
    od;

    return fail;
end;



RECOG.SymplecticForm := function(G)
    return RECOG.BilinearForm(G, "S");
end;



RECOG.SymmetricBilinearForm := function(G)
    return RECOG.BilinearForm(G, "O");
end;



RECOG.QuadraticForm := function(G)
    local d, F, formMatrix, polarFormMatrix, i, g, RightSideForLinSys,
    MatrixForLinSys, x;

    d := DimensionOfMatrixGroup(G);
    F := DefaultFieldOfMatrixGroup(G);
    if not IsFinite(F) then
        ErrorNoReturn("The base field of <G> must be finite");
    fi;

    if HasInvariantQuadraticForm(G) then
        formMatrix := InvariantQuadraticForm(G).matrix;
        return ImmutableMatrix(F, formMatrix);
    fi;

    # We first look for an invariant symmetric bilinear form of G, which will
    # be the polar form of the desired quadratic form
    polarFormMatrix := RECOG.SymmetricBilinearForm(G);
    # The Gram matrix formMatrix of the quadratic form is upper triangular and
    # polarFormMatrix = formMatrix + formMatrix ^ T, so the entries above the
    # main diagonal of polarFormMatrix and formMatrix must be the same
    formMatrix := List([1..d], i -> Concatenation(ListWithIdenticalEntries(i, Zero(F)),
                                                  polarFormMatrix[i]{[i + 1..d]}));
    if Characteristic(F) <> 2 then
        # In this case, the polar form determines the quadratic form completely
        formMatrix := formMatrix + 1 / 2 * DiagonalMat(DiagonalOfMatrix(polarFormMatrix));
    else
        # We are left to determine the diagonal entries of formMatrix. Let them
        # be x1, ..., xd and X = diag(x1, ..., xd); furthermore, let U be the
        # part of polarFormMatrix above the main diagonal (i.e. the current
        # value of formMatrix). Then for the quadratic form X + U to be
        # preserved, we need g * (X + U) * g ^ T to have the same diagonal
        # entries as X + U, i.e. as X, for each generator g of G.
        #
        # Hence, we need xi = (g * U * g ^ T)_ii + (x1 * g[i, 1] ^ 2 + ... + xd * g[i, d] ^ 2)
        # This leads to a linear system for the xi, which we solve.

        RightSideForLinSys := Concatenation(List(GeneratorsOfGroup(G),
                                                 g -> DiagonalOfMatrix(g * formMatrix * TransposedMat(g))));
        MatrixForLinSys := Concatenation(List(GeneratorsOfGroup(G),
                                              g -> List([1..d],
                                                        i -> DiagonalOfMatrix(TransposedMat([g[i]{[1..d]}]) * [g[i]{[1..d]}]))
                                                    + IdentityMat(d, F)));
        x := SolutionMat(TransposedMat(MatrixForLinSys), RightSideForLinSys);

        if x = fail then
            return fail;
        fi;

        formMatrix := formMatrix + DiagonalMat(x);
    fi;

    return formMatrix;
end;



# Compute the Gram matrix of the quadratic form corresponding to the bilinear
# form described by <gramMatrix> in odd characteristic.
RECOG.BilinearToQuadraticForm := function(gramMatrix)
    local F, n, i, Q;

    F := DefaultFieldOfMatrix(gramMatrix);

    if Characteristic(F) = 2 then
        ErrorNoReturn("Characteristic must be odd");
    fi;

    n := NrRows(gramMatrix);
    Q := List(gramMatrix, ShallowCopy);
    for i in [1..n] do
        Q{[i + 1..n]}{[i]} := NullMat(n - i, 1, F);
        Q[i, i] := gramMatrix[i, i] / 2;
    od;

    return Q;
end;

# One needs to ensure that the attribute DefaultFieldOfMatrixGroup is set
# correctly for <group>; this can be done, for example, by making the
# generators used during construction of the group immutable matrices over the
# appropriate field.
RECOG.ConjugateToSesquilinearForm := function(group, type, gramMatrix)
    local gapForm, newForm, gapToCanonical, canonicalToNew, field, formMatrix,
        result, d, q, broadType;
    if not type in ["S", "O-B", "O-Q", "U"] then
        ErrorNoReturn("<type> must be one of 'S', 'U', 'O-B', 'O-Q'");
    fi;
    d := DimensionOfMatrixGroup(group);
    field := DefaultFieldOfMatrixGroup(group);
    if type = "S" or type = "O-B" then
        if type = "S" then
            broadType := type;
        else
            broadType := "O";
        fi;
        formMatrix := RECOG.BilinearForm(group, broadType);
        if formMatrix = fail then
            if type = "S" then
                ErrorNoReturn("No preserved symplectic form found for <group>");
            else
                ErrorNoReturn("No preserved symmetric bilinear form found for",
                              " <group>");
            fi;
        fi;
        gapForm := BilinearFormByMatrix(formMatrix, field);
        newForm := BilinearFormByMatrix(gramMatrix, field);
    elif type = "U" then
        if IsOddInt(DegreeOverPrimeField(field)) then
            q := Size(field);
            field := GF(q ^ 2);
        fi;
        formMatrix := RECOG.UnitaryForm(group);
        if formMatrix = fail then
            ErrorNoReturn("No preserved unitary form found for <group>");
        fi;
        gapForm := HermitianFormByMatrix(formMatrix, field);
        newForm := HermitianFormByMatrix(gramMatrix, field);
    else
        # This is the case type = "O-Q"
        formMatrix := RECOG.QuadraticForm(group);
        if formMatrix = fail then
            ErrorNoReturn("No preserved quadratic form found for <group>");
        fi;
        gapForm := QuadraticFormByMatrix(formMatrix, field);
        newForm := QuadraticFormByMatrix(gramMatrix, field);
    fi;
    if gapForm = newForm then
        # nothing to be done
        result := group;
    # The Forms package has a bug for d = 1 so we need to make this exception
    elif d <> 1 then
        # the following if condition can only ever be fulfilled if <group> is an
        # orthogonal group; there the case of even dimension is problematic since,
        # in that case, there are two similarity classes of bilinear forms
        if not WittIndex(gapForm) = WittIndex(newForm) then
            ErrorNoReturn("The form preserved by <group> must be similar to the form ",
                          "described by the Gram matrix <gramMatrix>.");
        fi;
        gapToCanonical := BaseChangeHomomorphism(BaseChangeToCanonical(gapForm),
                                                 field);
        canonicalToNew := BaseChangeHomomorphism(BaseChangeToCanonical(newForm) ^ (-1),
                                                 field);
        result := RECOG.MatrixGroup(field, canonicalToNew(gapToCanonical(GeneratorsOfGroup(group))));
    
        # Set useful attributes
        UseIsomorphismRelation(group, result);
    else
        # replaces the Witt index check above
        if IsZero(gramMatrix) <> IsZero(formMatrix) then
            ErrorNoReturn("The form preserved by <group> must be similar to the",
                          " form described by the Gram matrix <gramMatrix>.");
        fi;
        result := group;
    fi;

    if type = "S" then
        SetInvariantBilinearForm(result, rec(matrix := gramMatrix));
    elif type = "O-B" then
        SetInvariantQuadraticFormFromMatrix(result, RECOG.BilinearToQuadraticForm(gramMatrix));
    elif type = "U" then
        SetInvariantSesquilinearForm(result, rec(matrix := gramMatrix));
    else
        SetInvariantQuadraticFormFromMatrix(result, gramMatrix);
    fi;

    return result;
end;

# If <group> preserves a sesquilinear form of type <type> (one of "S", "U", "O"
# (in odd dimension), "O+" or "O-" (both in even dimension), return a group
# conjugate to <group> preserving the standard form of that type.
#
# Also, one need to ensure that the attribute DefaultFieldOfMatrixGroup is set
# correctly for <group>; this can be done, for example, by making the
# generators used during construction of the group immutable matrices over the
# appropriate field.
RECOG.ConjugateToStandardForm := function(group, type)
    local d, F, q, gapForm, broadType;

    # determining d (dimension of matrix group), F (base field) and q (order of
    # F) plus some sanity checks
    if not type in ["S", "O+", "O-", "O", "U"] then
        ErrorNoReturn("<type> must be one of 'S', 'U', 'O+', 'O-', 'O'");
    fi;
    F := DefaultFieldOfMatrixGroup(group);
    d := DimensionOfMatrixGroup(group);
    if type = "O" and IsEvenInt(d) then
        ErrorNoReturn("<type> cannot be 'O' if the dimension of <group> is even");
    elif type in ["O+", "O-"] and IsOddInt(d) then
        ErrorNoReturn("<type> cannot be 'O+' or 'O-' if the dimension of",
                      " <group> is odd");
    elif IsEvenInt(Size(F)) and IsOddInt(d) and type in ["O+", "O-", "O"] then
        ErrorNoReturn("If <type> is 'O+', 'O-' or 'O' and the size of <F> is",
                      " even, <d> must be even");
    fi;
    if type in ["S", "O", "O+", "O-"] then
        q := Size(F);
    else
        if IsSquareInt(Size(F)) then
            q := RootInt(Size(F));
        else
            # It might be that G is to be understood as a matrix group over
            # GF(q ^ 2), but the matrices can actually be represented over a
            # smaller field, which causes DefaultFieldOfMatrixGroup to return GF(q)
            # instead of GF(q ^ 2) - we have to remedy this somehow ...
            q := Size(F);
        fi;
    fi;
    
    # get standard GAP form
    if type = "S" then
        gapForm := InvariantBilinearForm(Sp(d, q)).matrix;
    elif type = "U" then
        gapForm := InvariantSesquilinearForm(GU(d, q)).matrix;
    elif type = "O" then
        gapForm := InvariantBilinearForm(Omega(d, q)).matrix;
    elif type = "O+" then
        if Characteristic(F) = 2 then
            gapForm := InvariantQuadraticForm(Omega(1, d, q)).matrix;
        else
            gapForm := InvariantBilinearForm(Omega(1, d, q)).matrix;
        fi;
    elif type = "O-" then
        if Characteristic(F) = 2 then
            gapForm := InvariantQuadraticForm(Omega(-1, d, q)).matrix;
        else
            gapForm := InvariantBilinearForm(Omega(-1, d, q)).matrix;
        fi;
    fi;

    if type in ["O", "O+", "O-"] then
        if Characteristic(F) = 2 then
            broadType := "O-Q";
        else
            broadType := "O-B";
        fi;
    else
        broadType := type;
    fi;

    return RECOG.ConjugateToSesquilinearForm(group, broadType, gapForm);
end;

# Let <forms> = [f1, f2, ..., ft] be a list of sesquilinear forms on the vector
# spaces F ^ d1, F ^ d2, ..., F ^ dt. Then we can lift these to a sesquilinear
# form f on the tensor product F ^ d1 x F ^ d2 x ... x F ^ dt by defining
# f(v1 x v2 x ... x vt, w1 x w2 x ... x wt) = f1(v1, w1)f2(v2, w2)...ft(vt, wt).
#
# Return the Gram matrix of f; the forms f1, f2, ..., ft must be given as their
# respective Gram matrices.
RECOG.LiftFormsToTensorProduct := function(forms, F)
    local dims, d, t, newForm, i, j, iteri, iterj, indicesi, indicesj;

    dims := List(forms, NrRows);
    d := Product(dims);
    t := Length(dims);
    newForm := NullMat(d, d, F);
    dims := List(dims,d->[1..d]);

    iteri := IteratorOfCartesianProduct(dims);
    for i in [1..d] do
        indicesi := NextIterator(iteri);
        iterj := IteratorOfCartesianProduct(dims);
        for j in [1..d] do
            indicesj := NextIterator(iterj);
            newForm[i, j] := Product([1..t], k -> (forms[k])[indicesi[k], indicesj[k]]);
        od;
    od;

    return newForm;
end;

# Return the standard orthogonal and corresponding bilinear form as used for
# constructions in [HR10], cf. section 3.1 loc. cit.
RECOG.StandardOrthogonalForm := function(epsilon, d, q)
    local field, m, F, Q, gamma, xi;
    
    if not epsilon in [-1, 0, 1] then
        ErrorNoReturn("<epsilon> must be one of -1, 0, 1");
    fi;
    if epsilon = 0 and IsEvenInt(d) then
        ErrorNoReturn("<epsilon> must be one of -1 or 1 if <d> is even");
    fi;
    if epsilon <> 0 and IsOddInt(d) then
        ErrorNoReturn("<epsilon> must be 0 if <d> is odd");
    fi;
    if IsEvenInt(q) and IsOddInt(d) then
        ErrorNoReturn("<d> must be even if <q> is even");
    fi;

    field := GF(q);
    m := QuoInt(d, 2);
    F := RECOG.AntidiagonalMat(d, field);

    if IsOddInt(d * q) then
        Q := RECOG.AntidiagonalMat(One(field) * Concatenation(ListWithIdenticalEntries(m, 1),
                                                        [1 / 2],
                                                        ListWithIdenticalEntries(m, 0)),
                             field);
    else
        Q := RECOG.AntidiagonalMat(One(field) * Concatenation(ListWithIdenticalEntries(m, 1),
                                                        ListWithIdenticalEntries(m, 0)),
                             field);
        if epsilon = -1 then
            if IsEvenInt(q) then
                gamma := RECOG.FindGamma(q);
            else
                xi := PrimitiveElement(GF(q ^ 2));
                gamma := xi ^ (q + 1) * (xi + xi ^ q) ^ (-2);
            fi;

            F[m, m] := 2 * gamma ^ 0;
            F[m + 1, m + 1] := 2 * gamma;
            Q[m, m] := gamma ^ 0;
            Q[m + 1, m + 1] := gamma;
        fi;
    fi;

    return rec(Q := Q, F := F);
end;

RECOG.ConjugateModule := function(M, q)
  return GModuleByMats(List(MTX.Generators(M), A -> RECOG.ApplyFunctionToEntries(A, x -> x ^ q)),
                       MTX.Field(M));
end;

# Assuming that the group G acts absolutely irreducibly, try to find a unitary
# form which is G-invariant or prove that no such form exists.
#
# We use this function instead of PreservedSesquilinearForms from the Forms
# package since PreservedSesquilinearForms seems to be buggy and unreliable.
# As an example, take the group generated by
#     [   1    0    0  ]         [ z^39 z^9  z^24 ]
#     [ z^33 z^14 z^26 ]   and   [ z^25 z^16 z^6  ]
#     [ z^19 z^31 z^5  ]         [ z^7  z^32 z^28 ]
# where z = Z(49), which does preserve a unitary form, but this is not
# recognised by PreservedSesquilinearForms, even after some 1000 calls of the
# function.
#
# In general, this function should only be used if one can be sure that <G>
# preserves a unitary form (but one does not know which one).
RECOG.UnitaryForm := function(G)
    local d, F, q, M, inverseHermitianConjugateM, formMatrix, row, col, x,
    scalar, counter;

    d := DimensionOfMatrixGroup(G);
    F := DefaultFieldOfMatrixGroup(G);
    if not IsFinite(F) then
        ErrorNoReturn("The base field of <G> must be finite");
    fi;
    if not IsEvenInt(DegreeOverPrimeField(F)) then
        # It might be that G is to be understood as a matrix group over
        # GF(q ^ 2), but the matrices can actually be represented over a
        # smaller field, which causes DefaultFieldOfMatrixGroup to return GF(q)
        # instead of GF(q ^ 2) - we have to remedy this somehow ...
        q := Size(F);
    else
        q := RootInt(Size(F));
    fi;

    # Return stored sesquilinear form if it exists and is hermitian
    if HasInvariantSesquilinearForm(G) then
        formMatrix := InvariantSesquilinearForm(G).matrix;
        if formMatrix = RECOG.HermitianConjugate(formMatrix, q) then
            return ImmutableMatrix(F, formMatrix);
        fi;
    fi;

    M := GModuleByMats(GeneratorsOfGroup(G), F);
    # An element A of G acts as A ^ (-T) in MTX.DualModule(M) and hence as
    # HermitianConjugate(A, q) ^ (-1) in inverseHermitianConjugateM
    inverseHermitianConjugateM := RECOG.ConjugateModule(MTX.DualModule(M), q);

    counter := 0;
    scalar := fail;
    # As the MeatAxe is randomised, we might have to make some more trials to
    # find a preserved unitary form if there is one; breaking after 1000 trials
    # is just a "safety net" in case a group <G> that does not preserve a
    # unitary form is input.
    while scalar = fail and counter < 1000 do
        counter := counter + 1;

        # If f: M -> inverseHermitianConjugateM is an isomorphism, it must respect
        # multiplication by group elements, i.e. for A in G
        #       f(x * A) = f(x) * HermitianConjugate(A, q) ^ (-1).
        # Let f be given by the matrix F, i.e. f: x -> x * F. Then we have
        #       (x * A) * F = x * F * HermitianConjugate(A, q) ^ (-1).
        # Putting these results together for all vectors x gives
        #       A * F = F * HermitianConjugate(A, q) ^ (-1)
        # <==>  A * F * HermitianConjugate(A, q) = F,
        # which is what we need.
        formMatrix := MTX.IsomorphismModules(M, inverseHermitianConjugateM);

        # We now need to ensure that formMatrix is actually the matrix of a
        # unitary form, which can be achieved by multiplying it by a scalar
        if formMatrix <> fail then
            if formMatrix <> RECOG.HermitianConjugate(formMatrix, q) then
                # find a non-zero entry of formMatrix
                row := First([1..d], x -> not IsZero(formMatrix[x]));
                col := First([1..d], x -> not IsZero(formMatrix[row][x]));
                if not IsZero(formMatrix[col, row]) then
                    # this must be 1 for formMatrix to be hermitian
                    x := formMatrix[row, col] * formMatrix[col, row] ^ (-q);
                    # multiplying formMatrix by scalar will ensure that x = 1, i.e. that
                    # formMatrix is hermitian
                    scalar := RootFFE(x, q - 1);
                fi;

                if IsZero(formMatrix[col, row]) or scalar = fail then
                    if not MTX.IsAbsolutelyIrreducible(M) then
                        ErrorNoReturn("UnitaryForm failed - group is not absolutely irreducible");
                    fi;
                    continue;
                fi;

                # make formMatrix hermitian
                formMatrix := scalar * formMatrix;
            fi;

            if formMatrix <> RECOG.HermitianConjugate(formMatrix, q) and not MTX.IsAbsolutelyIrreducible(M) then
                ErrorNoReturn("UnitaryForm failed - group is not absolutely irreducible");
            fi;

            return ImmutableMatrix(F, formMatrix);
        fi;
    od;

    return fail;
end;

# Assuming that the group G acts absolutely irreducibly, try to find a
#   * symplectic form (if <type> = S) or a
#   * symmetric bilinear form (if <type> = O)
# which is G-invariant or prove that no such form exists.
#
# We use this function instead of PreservedBilinearForms form the Forms package
# since PreservedBilinearForms seems to be buggy and unreliable (see also
# comment above UnitaryForm).
#
# In general, this function should only be used if one can be sure that <G>
# preserves a bilinear form (but one does not know which one).
RECOG.BilinearForm := function(G, type)
    local F, M, inverseTransposeM, counter, formMatrix, condition;

    if not type in ["S", "O"] then
        ErrorNoReturn("<type> must be one of 'S', 'O'");
    fi;
    # Set the condition the Gram matrix needs to satisfy for each of the
    # possible types.
    if type = "S" then
        condition := x -> (x = - TransposedMat(x));
    elif type = "O" then
        condition := x -> (x = TransposedMat(x));
    fi;

    F := DefaultFieldOfMatrixGroup(G);

    # Return stored bilinear form if it exists and is symplectic / symmetric
    if HasInvariantBilinearForm(G) then
        formMatrix := InvariantBilinearForm(G).matrix;
        if condition(formMatrix) then
            return ImmutableMatrix(F, formMatrix);
        fi;
    fi;
    
    M := GModuleByMats(GeneratorsOfGroup(G), F);

    if not MTX.IsIrreducible(M) then
        ErrorNoReturn("BilinearForm failed - group is not irreducible");
    fi;

    # An element A of G acts as A ^ (-T) in MTX.DualModule(M)
    inverseTransposeM := MTX.DualModule(M);

    counter := 0;
    # As the MeatAxe is randomised, we might have to make some more trials to
    # find a preserved symplectic / symmetric bilinear form if there is one;
    # breaking after 1000 trials is just a "safety net" in case a group <G>
    # that does not preserve a symplectic / symmetric bilinear form is input.
    while counter < 1000 do
        counter := counter + 1;

        # If f: M -> inverseTransposeM is an isomorphism, it must respect
        # multiplication by group elements, i.e. for A in G
        #       f(x * A) = f(x) * A ^ (-T)
        # Let f be given by the matrix F, i.e. f: x -> x * F. Then we have
        #       (x * A) * F = x * F * A ^ (-T)
        # Putting these results together for all vectors x gives
        #       A * F = F * A ^ (-T)
        # <==>  A * F * A ^ T = F,
        # which is what we need.
        formMatrix := MTX.IsomorphismModules(M, inverseTransposeM);

        if formMatrix <> fail then
            # check if formMatrix is antisymmetric
            if condition(formMatrix) then
                return ImmutableMatrix(F, formMatrix);
            fi;
            if not MTX.IsAbsolutelyIrreducible(M) then
                ErrorNoReturn("BilinearForm failed - group is not absolutely irreducible");
            fi;
        fi;
    od;

    return fail;
end;

RECOG.SymplecticForm := function(G)
    return RECOG.BilinearForm(G, "S");
end;

RECOG.SymmetricBilinearForm := function(G)
    return RECOG.BilinearForm(G, "O");
end;

RECOG.QuadraticForm := function(G)
    local d, F, formMatrix, polarFormMatrix, i, g, RightSideForLinSys,
    MatrixForLinSys, x;

    d := DimensionOfMatrixGroup(G);
    F := DefaultFieldOfMatrixGroup(G);
    if not IsFinite(F) then
        ErrorNoReturn("The base field of <G> must be finite");
    fi;

    if HasInvariantQuadraticForm(G) then
        formMatrix := InvariantQuadraticForm(G).matrix;
        return ImmutableMatrix(F, formMatrix);
    fi;

    # We first look for an invariant symmetric bilinear form of G, which will
    # be the polar form of the desired quadratic form
    polarFormMatrix := RECOG.SymmetricBilinearForm(G);
    # The Gram matrix formMatrix of the quadratic form is upper triangular and
    # polarFormMatrix = formMatrix + formMatrix ^ T, so the entries above the
    # main diagonal of polarFormMatrix and formMatrix must be the same
    formMatrix := List([1..d], i -> Concatenation(ListWithIdenticalEntries(i, Zero(F)),
                                                  polarFormMatrix[i]{[i + 1..d]}));
    if Characteristic(F) <> 2 then
        # In this case, the polar form determines the quadratic form completely
        formMatrix := formMatrix + 1 / 2 * DiagonalMat(DiagonalOfMatrix(polarFormMatrix));
    else
        # We are left to determine the diagonal entries of formMatrix. Let them
        # be x1, ..., xd and X = diag(x1, ..., xd); furthermore, let U be the
        # part of polarFormMatrix above the main diagonal (i.e. the current
        # value of formMatrix). Then for the quadratic form X + U to be
        # preserved, we need g * (X + U) * g ^ T to have the same diagonal
        # entries as X + U, i.e. as X, for each generator g of G.
        #
        # Hence, we need xi = (g * U * g ^ T)_ii + (x1 * g[i, 1] ^ 2 + ... + xd * g[i, d] ^ 2)
        # This leads to a linear system for the xi, which we solve.

        RightSideForLinSys := Concatenation(List(GeneratorsOfGroup(G),
                                                 g -> DiagonalOfMatrix(g * formMatrix * TransposedMat(g))));
        MatrixForLinSys := Concatenation(List(GeneratorsOfGroup(G),
                                              g -> List([1..d],
                                                        i -> DiagonalOfMatrix(TransposedMat([g[i]{[1..d]}]) * [g[i]{[1..d]}]))
                                                    + IdentityMat(d, F)));
        x := SolutionMat(TransposedMat(MatrixForLinSys), RightSideForLinSys);

        if x = fail then
            return fail;
        fi;

        formMatrix := formMatrix + DiagonalMat(x);
    fi;

    return formMatrix;
end;


#############################################################################
#############################################################################
################## Old function from RECOG package ##########################
#############################################################################
#############################################################################


RECOG.DerivedSubgroupMonteCarlo := function(g, NumberGenerators)
  local gens,gens2,i,x,y;
  gens := [];
  for i in [1..Maximum([NumberGenerators, Size(GeneratorsOfGroup(g)) * 2 + 10])] do
      x := PseudoRandom(g);
      y := PseudoRandom(g);
      Add(gens,Comm(x,y));
  od;
  gens2 := FastNormalClosure(GeneratorsOfGroup(g),gens,10);
  return GroupWithGenerators(gens2);
end;
