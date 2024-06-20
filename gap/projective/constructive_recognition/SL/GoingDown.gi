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
######## GoingDown method for special linear groups #########################
#############################################################################
#############################################################################



# TODO: Work on comments and documentation



# Find random element s = r^PseudRandom(g) such that <r,s> is isomorphic to SL(4,q)
# and check whether they are isomorphic
RECOG.SLn_constructsl4:=function(g,dim,q,r)
  local s,h,count,readydim4,readydim3,ready,u,orderu,
        nullr,nulls,nullspacer,nullspaces,int,intbasis,nullintbasis,
        newu,newbasis,newbasisinv,newr,news,outputu,mat,i,shorts,shortr;
  nullr:=RECOG.FixspaceMat(r);
  nullspacer:=VectorSpace(GF(q),nullr);
  mat:=One(r);
  ready:=false;
  repeat
    s:=r^PseudoRandom(g);
    nulls:=RECOG.FixspaceMat(s);
    nullspaces:=VectorSpace(GF(q),nulls);
    int:=Intersection(nullspacer,nullspaces);
    intbasis:=Basis(int);
    newbasis:=[];
    for i in [1..Length(intbasis)] do
        Add(newbasis,intbasis[i]);
    od;
    i:=0;
    repeat
       i:=i+1;
       if not mat[i] in int then
          Add(newbasis,mat[i]);
          int:=VectorSpace(GF(q),newbasis);
       fi;
    until Dimension(int)=dim;
    ConvertToMatrixRep(newbasis);
    newbasisinv:=newbasis^(-1);
    newr:=newbasis*r*newbasisinv;
    news:=newbasis*s*newbasisinv;

    #shortr, shorts do not need memory
    #we shall throw away the computations in h
    #check that we have SL(4,q), by non-constructive recognition
    
    # Remark D.R.: Tries to reduce matrix multiplications
    #               by working with 4 dimensional matrices
    shortr:=newr{[dim-3..dim]}{[dim-3..dim]};
    shorts:=news{[dim-3..dim]}{[dim-3..dim]};
    h:=Group(shortr,shorts);
    count:=0;
    readydim4:=false;
    readydim3:=false;
    repeat
       u:=PseudoRandom(h);
       orderu:=Order(u);
       if orderu mod ((q^4-1)/(q-1)) = 0 then
          readydim4:=true;
       elif Gcd(orderu,(q^2+q+1)/Gcd(3,q-1))>1 then
          readydim3:=true;
       fi;
       if readydim4 = true and readydim3 = true then
          ready:=true;
          break;
       fi;
       count:=count+1;
    until count=30;
  until ready=true;

  return Group(r,s);
end;



#g=SL(d,q), given as a subgroup of SL(dim,q)
#output: [SL(2,q), and a basis for the 2-dimensional subspace where it acts
RECOG.SLn_godownfromd:=function(g,q,d,dim)
  local y,yy,ready,order,es,dims,subsp,z,x,a,b,c,h,vec,vec2,
  pol,factors,degrees,comm1,comm2,comm3,image,basis,action,vs,readyqpl1,
  readyqm1,count,u,orderu;

  repeat
    ready:=false;
    y:=PseudoRandom(g);
    pol:=CharacteristicPolynomial(y);
    factors:=Factors(pol);
    degrees:=List(factors,Degree);
    if d-1 in degrees then
       order:=Order(y);
       if order mod (q-1)=0 then
          yy:=y^(order/(q-1));
       else
          yy:=One(y);
       fi;
       if not IsOne(yy) then
            es:= Eigenspaces(GF(q),yy);
            dims:=List(es,Dimension);
            if IsSubset(Set([1,d-1,dim-d]),Set(dims)) and
               (1 in Set(dims)) then
               es:=Filtered(es,x->Dimension(x)=1);
               vec:=Basis(es[1])[1];
               if vec*yy=vec then
                  vec:=Basis(es[2])[1];
               fi;
               repeat
                  z:=PseudoRandom(g);
                  x:=yy^z;
                  a:=Comm(x,yy);
                  b:=a^yy;
                  c:=a^x;
                  comm1:= Comm(a,c);
                  comm2:=Comm(a,b);
                  comm3:=Comm(b,c);
                  if comm1<>One(a) and comm2<>One(a) and
                    comm3<>One(a) and Comm(comm1,comm2)<>One(a) then
                    vec2:=vec*z;
                    vs:=VectorSpace(GF(q),[vec,vec2]);
                    basis:=Basis(vs);
                    #check that the action in 2 dimensions is SL(2,q)
                    #by non-constructive recognition, finding elements of
                    #order (q-1) and (q+1)
                    #we do not need memory in the group image
                    action:=List([a,b,c],x->RECOG.LinearAction(basis,q,x));
                    image:=Group(action);
                    count:=0;
                    readyqpl1:=false;
                    readyqm1:=false;
                    repeat
                       u:=PseudoRandom(image);
                       orderu:=Order(u);
                       if orderu = q-1 then
                          readyqm1:=true;
                       elif orderu = q+1 then
                          readyqpl1:=true;
                       fi;
                       if readyqm1 = true and readyqpl1 = true then
                          ready:=true;
                          break;
                       fi;
                       count:=count+1;
                     until count=20;
                  fi;
               until ready=true;
            fi;
       fi;
    fi;
  until ready;

  h:=Group(a,b,c);
  subsp:=VectorSpace(GF(q),[vec,vec2]);
  Info(InfoRecog,2,"New Dimension: 2");
  return [h,subsp];

end;



#going down from 4 to 2 dimensions, when q=2,3,4,5,9
#just construct the 4-dimensional invariant space and generators
#for the group acting on it
RECOG.SLn_exceptionalgodown:=function(h,q,dim)
  local basis, v, vs, i, gen;

  vs:=VectorSpace(GF(q),One(h));
  basis:=[];
  repeat
     if InfoLevel(InfoRecog) >= 3 then Print("C"); fi;
     for i in [1..4] do
        v:=PseudoRandom(vs);
        for gen in GeneratorsOfGroup(h) do
           Add(basis,v*gen-v);
        od;
     od;
     basis:=ShallowCopy(SemiEchelonMat(basis).vectors);
  until Length(basis)=4;
  Info(InfoRecog,2,"New Dimension: 2");
  return [h,VectorSpace(GF(q),basis)];
end;



RECOG.SLn_constructsl2:=function(g,d,q)
  local r,h;

  r := RECOG.constructppdTwoStingray(g,d,q,"SL",fail);
  Info(InfoRecog,2,"Finished main GoingDown, i.e. we found a stringray element which operates irreducible on a 2 dimensional subspace. \n");
  Info(InfoRecog,2,"Next goal: Find an random element s.t. the two elements generate SL(4,q). \n");
  h := RECOG.SLn_constructsl4(g,d,q,r);
  # Remark D.R.: at this point we know that h is isomorphic to SL(4,q)
  Info(InfoRecog,2,"Succesful. ");
  Info(InfoRecog,2,"Current Dimension: 4\n");
  Info(InfoRecog,2,"Next goal: Generate SL(2,q). \n");
  if not (q in [2,3,4,5,9]) then
     return RECOG.SLn_godownfromd(h,q,4,d);
  else
     return RECOG.SLn_exceptionalgodown(h,q,d);
  fi;
end;



##############################################################################
# The going down method while constructing smaller matrices:
##############################################################################



RECOG.CheckNewStingrayGroupSmallerMatrices := function(g1,dim1,base1,eigenspace1,g2,dim2,base2,eigenspace2,q)
    local baseSum, b, action1, action2, fld, module, eigenspaceintersection;

    baseSum := ShallowCopy(base1);
    Append(baseSum,base2);
    
    if NullspaceMat(baseSum) <> [] then
        return [false,[]];
    fi;

    fld := GF(q);
    b := Basis(VectorSpace(fld,baseSum),baseSum);
    action1 := List(baseSum,v->Coefficients(b,v*g1));
    action2 := List(baseSum,v->Coefficients(b,v*g2));
    module := GModuleByMats( [action1,action2], fld );
    if MTX.IsIrreducible(module) then
        eigenspaceintersection := SumIntersectionMat(eigenspace1,eigenspace2)[2];
        return [true,[action1,action2],BasisVectors(b),eigenspaceintersection];
    else
        return [false,[]];
    fi;
end;



RECOG.ConstructSL4SmallerMatrices := function(g1,g2,q)
    local baseSum, b, action1, action2, fld, module, base, EleBase, fixbase, ele, eigenspace1, eigenspace2, eigenspaceintersection;

    base := [];
    fld := GF(q);
    for ele in [g1,g2] do
        fixbase := RECOG.FixspaceMat(TransposedMat(ele));
        EleBase := NullspaceMat(TransposedMat(fixbase));
        Append(base,EleBase);
    od;

    eigenspace1 := RECOG.FixspaceMat(StripMemory(g1));
    eigenspace2 := RECOG.FixspaceMat(StripMemory(g2));
    eigenspaceintersection := SumIntersectionMat(eigenspace1,eigenspace2)[2];

    b := Basis(VectorSpace(fld,base),base);
    action1 := List(base,v->Coefficients(b,v*g1));
    action2 := List(base,v->Coefficients(b,v*g2));
    return [GroupByGenerators([action1,action2]),BasisVectors(b),eigenspaceintersection];
end;



RECOG.SLn_godownStingrayWithSmallerMatrices:=function(list)
local d, first, q, p, g, i, r, pol, factors, degrees, newdim, power, rr, ss,
    newgroup, colldegrees, exp, count, check, ocount, beta, NiList, Maxi, qFactors, irrfact, invbase, oneEigenspace, maxdim;

    first := function(list)
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
    if d <= 700 then
        maxdim := Maximum([Log2Int(d),3]);
    else
        # Test a heuristic
        maxdim := Int(d/20);
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
            if InfoLevel(InfoRecog) >= 3 then Print(".\c"); fi;
            r:=PseudoRandom(g);
            pol:=CharacteristicPolynomial(r);
            factors:=Factors(pol);
            degrees:=List(factors,Degree);
            newdim:=first(degrees);
        until (count>100) or (newdim <> fail and (degrees[newdim] < maxdim));
        # Be careful if Log2Int(d) = 2! In this case we search for stingray elements with k < 2. Hence use newdim < Maximum([Log2Int(d),3])

        if count>100 then
            return fail;
        fi;
        
        # Split result from first:
        irrfact := factors[newdim];
        newdim := degrees[newdim];
        
        if newdim > 2 then
            # Check whether the stingray candidate is a ppd-stingray element
            check := RECOG.IsPpdStingrayElement(p,Length(qFactors),newdim,irrfact);
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
            
                invbase := NullspaceMat(TransposedMat(RECOG.FixspaceMat(TransposedMat(StripMemory(rr)))));
                oneEigenspace := RECOG.FixspaceMat(StripMemory(rr));
                return [rr,newdim,invbase,oneEigenspace];
                
            fi;
        else
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
        
            invbase := NullspaceMat(TransposedMat(RECOG.FixspaceMat(TransposedMat(StripMemory(rr)))));
            if Size(invbase) = 2 then
                oneEigenspace := RECOG.FixspaceMat(StripMemory(rr));
                return [rr,newdim,invbase,oneEigenspace];
            fi;
        fi;
        
        ocount := ocount + 1;
    od;

    return fail;

end;



RECOG.SLn_constructppdTwoStingraySmallerMatrices:=function(g,dim,q)
local out, list, out2, currentdim, check, slplist, slpToSmallerGroup, baselist, eigenspacelist;

    Info(InfoRecog,2,"Current Dimension: ");
    Info(InfoRecog,2,dim);
    Info(InfoRecog,2,"\n");

    list:=[g,dim,q,g];
    slplist:=[];
    currentdim := dim;
    baselist:=[];
    eigenspacelist := [];
    repeat
        out:=RECOG.SLn_godownStingrayWithSmallerMatrices(list);
        if out=fail or out[1]*out[1]=One(out[1]) then
            if InfoLevel(InfoRecog) >= 3 then Print("B\c"); fi;
            Info(InfoRecog,2,"Restart. \n");
            Info(InfoRecog,2,"Current Dimension: ");
            Info(InfoRecog,2,dim);
            Info(InfoRecog,2,"\n");
            list:=[g,dim,q,g];
            slplist:=[];
            baselist:=[];
            eigenspacelist := [];
            out:=fail;
        else
            if out[2]>2 then
            repeat
                    out2:=RECOG.SLn_godownStingrayWithSmallerMatrices(list);
                    if out2=fail or out2[1]*out2[1]=One(out2[1]) then
                        if InfoLevel(InfoRecog) >= 3 then Print("B\c"); fi;
                        list:=[g,dim,q,g];
                        slplist:=[];
                        baselist:=[];
                        eigenspacelist := [];
                        out2:=fail;
                    fi;
            until out2<>fail and out2[2] > 2;
            check := RECOG.CheckNewStingrayGroupSmallerMatrices(out[1],out[2],out[3],out[4],out2[1],out2[2],out2[3],out2[4],q);
            if check[1] then
                    # At this point we can use the smaller matrices and use them during the next loop body execution
                    slpToSmallerGroup := SLPOfElms([out[1],out2[1]]);
                    Add(slplist,slpToSmallerGroup);
                    Add(baselist,check[3]);
                    Add(eigenspacelist,check[4]);
                    list:=[GroupWithMemory(check[2]),out[2]+out2[2],q,g];
                    currentdim := list[2];
                    
                    # We still have to compute the vector space on which the matrices act in the input group

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
                    list:=[g,dim,q,g];
                    slplist:=[];
                    baselist:=[];
                    eigenspacelist := [];
                    out:=fail;
                fi;
            fi;
        fi;
    until out<>fail and out[2]=2;
    
    return [out[1],list[1],list[2],slplist,baselist,eigenspacelist];

end;



RECOG.SLn_constructsl2WithSmallerMatrices:=function(g,d,q)
local r,h,slp,sl2,baselist,gens,b,sl2gens,sl2genss,f,eigenspacelist,subspaces,eigenspace1,eigenspace2,eigenspace3,eigenspaceintersection;

    r := RECOG.SLn_constructppdTwoStingraySmallerMatrices(g,d,q);
    slp:=r[4];
    baselist:=r[5];
    eigenspacelist:=r[6];
    Info(InfoRecog,2,"Finished main GoingDown, i.e. we found a stringray element which operates irreducible on a 2 dimensional subspace. \n");
    Info(InfoRecog,2,"Next goal: Find an random element s.t. the two elements generate SL(4,q). \n");
    h := RECOG.SLn_constructsl4(r[2],r[3],q,r[1]);
    Add(slp,SLPOfElms(GeneratorsOfGroup(h)));
    #h := RECOG.LinearActionRepresentationSmallerMatrices(h);
    #Add(baselist,h[3]);
    h := GeneratorsOfGroup(h);
    h := RECOG.ConstructSL4SmallerMatrices(h[1],h[2],q);
    Add(baselist,h[2]);
    Add(eigenspacelist,h[3]);
    h[1] := GroupWithMemory(h[1]);
    #Error("here");
    # Remark D.R.: at this point we know that h is isomorphic to SL(4,q)
    Info(InfoRecog,2,"Succesful. ");
    Info(InfoRecog,2,"Current Dimension: 4\n");
    Info(InfoRecog,2,"Next goal: Generate SL(2,q). \n");
    if not (q in [2,3,4,5,9]) then
        sl2 := RECOG.SLn_godownfromd(h[1],q,4,h[2]);
        b := Basis(sl2[2]);
        f := GF(q);
        sl2gens := StripMemory(GeneratorsOfGroup(sl2[1]));
        Add(eigenspacelist,RECOG.FixspaceMat(sl2gens[1]));
        #eigenspace1 := RECOG.FixspaceMat(sl2gens[1]);
        #eigenspace2 := RECOG.FixspaceMat(sl2gens[2]);
        #eigenspace3 := RECOG.FixspaceMat(sl2gens[3]);
        #eigenspaceintersection := SumIntersectionMat(eigenspace1,eigenspace2)[2];
        #eigenspaceintersection := SumIntersectionMat(eigenspaceintersection,eigenspace3)[2];
        #Add(eigenspacelist,eigenspaceintersection);
        # Test by DR:
        #sl2genss := List(sl2gens,x-> List(b,v->Coefficients(b,v*x)));
        sl2genss := List(sl2gens,x->RECOG.LinearAction(b,f,x));
        Add(slp,SLPOfElms(GeneratorsOfGroup(sl2[1])));
        Add(baselist,BasisVectors(Basis(sl2[2])));
        # Add(eigenspacelist,RECOG.FixspaceMat(sl2gens[1]));
        # Just for tests: Add(eigenspacelist,RECOG.FixspaceMat(TransposedMat(sl2gens[1])));
        Add(sl2,RECOG.ConnectSLPs(slp));
        Add(sl2,sl2genss);
        subspaces := RECOG.Computesl2Subspace(baselist,eigenspacelist);
        sl2[2] := subspaces[1];
        Add(sl2,subspaces[2]);
        #        Error("why");
        return sl2;
    else
        sl2 := RECOG.SLn_exceptionalgodown(h[1],q,h[2]);
        b := Basis(sl2[2]);
        f := GF(q);
        sl2gens := StripMemory(GeneratorsOfGroup(sl2[1]));
        sl2genss := List(sl2gens,x->RECOG.LinearAction(b,f,x));
        Add(slp,SLPOfElms(GeneratorsOfGroup(sl2[1])));
        Add(baselist,BasisVectors(Basis(sl2[2])));
        #Add(eigenspacelist,RECOG.FixspaceMat(sl2gens[1]));
        Add(sl2,RECOG.ConnectSLPs(slp));
        Add(sl2,sl2genss);
        subspaces := RECOG.Computesl2Subspace(baselist,eigenspacelist);
        sl2[2] := subspaces[1];
        Add(sl2,subspaces[2]);
        return sl2;
    #   return ["sorry only SL(4,q)",h];
    fi;
end;



RECOG.ConnectSLPs:=function(slps)
local slp, currentslp, i;

    if Size(slps) = 0 then
        Error("This should not happen.");
    elif Size(slps) = 1 then
        return slps[1];
    else
        slp := slps[1];
        for i in [2..Size(slps)] do
            slp := CompositionOfStraightLinePrograms(slps[i],slp);
        od;
        return slp;
    fi;
    
end;



RECOG.Computesl2Subspace:=function(generators,eigenspaceGenerators)
local result, i, gens, j, combination, vec, comb, zerovec, sl2eigenspacebase, newsl2eigenspacevectors, ele;

    if Size(generators) = 1 then
        # We started with a SL(4,q)
        # Just return the 2-dimensional subspace

        # TODO return eigenspacebase!!! See else case

        sl2eigenspacebase := eigenspaceGenerators[1];
        zerovec := ZeroOfBaseDomain(result) * result[1];
        for ele in eigenspaceGenerators[2] do
            vec := zerovec;
            for j in [1..Size(ele)] do
                vec := vec + ele[j] * result[j];
            od;
            Add(sl2eigenspacebase,vec);
        od;

        return [generators[1],sl2eigenspacebase];
    else
        # We start with the 1xd vectors
        result := generators[1];
        sl2eigenspacebase := eigenspaceGenerators[1];
        zerovec := ZeroOfBaseDomain(result) * result[1];
        for ele in eigenspaceGenerators[2] do
            vec := zerovec;
            for j in [1..Size(ele)] do
                vec := vec + ele[j] * result[j];
            od;
            Add(sl2eigenspacebase,vec);
        od;

        for i in [2..Size(generators)] do
            combination := generators[i];
            gens := [];
            for comb in combination do
                vec := zerovec;
                for j in [1..Size(comb)] do
                    vec := vec + comb[j] * result[j];
                od;
                Add(gens,vec);
            od;
            if i+1 <= Size(eigenspaceGenerators) then
                for ele in eigenspaceGenerators[i+1] do
                    vec := zerovec;
                    for j in [1..Size(ele)] do
                        vec := vec + ele[j] * result[j];
                    od;
                    Add(sl2eigenspacebase,vec);
                od;
            fi;
            result := gens;
        od;

        return [result,sl2eigenspacebase];
    fi;
    
end;


##############################################################################
# LGO approach for GoingDown to Dimension 2
##############################################################################



RECOG.SL_godownToDimension2WithInvolutions := function(h,q)
local counter, ele, ele2, x, x2, ord, invo, found, cent, product, productEle, fact1, fact2, eigenspace, result,
Minuseigenspace, newbasis, dimeigen, dimMinuseigen, gens, SL2, reco, SL2sub, pseudoorderlist, cord1, cord2, r1, r2;

    # First we construct an involution i in h

    found := false;
    for counter in [1..100] do
        ele := PseudoRandom(h);
        x := RECOG.EstimateOrder(ele);
        x2 := x[2];
        ord := x[3];
        if x2 <> One(h) then
            invo := x2^(ord/2);
        else
            invo := One(h);
        fi;

        if invo <> One(h) and invo^2 = One(h) then
            eigenspace := Eigenspaces(GF(q),invo);
            if Size(eigenspace) <> 1 then
                Minuseigenspace := eigenspace[2];
                eigenspace := eigenspace[1];
                dimeigen := Dimension(eigenspace);
                dimMinuseigen := Dimension(Minuseigenspace);
                if dimeigen = 2 then
                    found := true;
                    break;
                fi;
            fi;
        fi;
    od;

    if not(found) then
        Error("could not find an involution");
    fi;

    newbasis := MutableCopyMat(BasisVectors(Basis(eigenspace)));
    Append(newbasis,BasisVectors(Basis(Minuseigenspace)));

    # Second we compute the two factors by computing the centralizer of the involution i

    cent := RECOG.CentraliserOfInvolution(h,invo,[],false,100,RECOG.CompletionCheck,PseudoRandom);
    product := GroupByGenerators(cent[1]);

    # Third we continue as in "Constructive recognition of classical groups in odd characteristic" part 11 to find generator

    r1 := [1,2];
    r2 := [3,4];
    for counter in [1..100] do
        result := RECOG.ConstructSmallSub(r1, r2, product, newbasis, g -> RECOG.IsThisSL2Natural(GeneratorsOfGroup(g),GF(q)));
        if result <> fail then
            break;
        fi;
    od;

    return fail;
end;
