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
######## Solve Symmetric Powers (Ducs Code) #######################################################
###################################################################################################
###################################################################################################



# TODO: Use this for the constructive recognition of SL(2,q)

# Code has been written by Duc Khuat during his Bachelors thesis
# This partly implements an algorithm based on the paper ”Constructive Recognition of SL(2, q)” by Leedham Green and E. A. O’Brien.
# For q being a p-power, the algorithm can only be applied to representations where the degree is smaller than p.

## computes for an element of SL(2,q) its representation in the n-th symmetric power
## F is the field
## n-th symmetric power
## A element of SL(2,q)
## return : Matrix of dimension n+1 corresponding to the action of SL(2,q) on T_n represented in the basis ( x^n, ...., y^n)
RECOG.SymPowRepSL2 :=function(F,n, A)
    local res,i,t,k,sum;
    res := IdentityMat(n+1,F);
    for i in [0..n] do
        for t in [0..n] do
            sum :=0;
            for k in [0..i] do
                if n-i-(t-k) > -1 and t-k > -1 then
                    sum:= sum + Binomial(n-i,t-k)*Binomial(i,k)* (A[1][1])^(t-k)*(A[2][1])^k*(A[1][2])^(n -i -(t-k))*(A[2][2])^(i-k);
                fi;
            od;
            res[i+1][n-t+1]:= sum;
        od;
    od;
    return res;
end;;



## randomly looks for an element of order q-1.
##input:
## G the group where we look randomly for an element of order n.
## n the order of g.
## return g an element with order n, and the number of tries.
RECOG.RandomElementOfOrder:= function(G, n)
    local nrTries ,g; nrTries := 0;
    while nrTries < 1000 do
        g := PseudoRandom(G);
        if (Order(g) = n) then
            return [g, nrTries];
        fi;
        nrTries := nrTries +1;
    od;
    ####### Added by Daniel Rademacher #######
    return ["fail", "fail"];
    ##########################################
    ErrorNoReturn ( " No element of order ", n, " has been found.\n");
end ;;



## z^r is the eigenvalue of g on natural module.
## find the unique (up to multiplication of -1) element in Z_q-1, to obtain the expected set of exponents, namely {-n, -n+2, ..., n-2, n }.
##input:
## g has order q-1 and q-1 eigenvectors.
## E is the set of exponent of eigenvalues in respect to a fixed primitve element of the field ## F the underlying field F of order q.
## r in the unit group of Z_{q-1} such that E*(r^{-1}) = { -s,-s+2, ..., s-2,s}
## return M matrix with eigenvectors as rows such that the i-th row is the eigenvector to -s + 2(i-1) for i =1 , ..., s+1.
RECOG.OrderEigenvectors := function(g , E ,F, r)
    local
    i, # every row of M.
    s, # Eigenvector of g
    M, # Output Matrix
    EVs, # Eigenvectors of g.
    z;
    z:= PrimitiveElement(F);
    M := [];
    EVs := Eigenvectors(F,g);
    for i in [ 1 .. DimensionsMat(g)[1]] do
        for s in EVs do
            if s*g = (z^(E[i]*r))*s then
                M[i] := s;
            fi;
        od;
    od;
    return M;
end;;



## find k such that List([0..n], x -> (n-2*x) mod (q-1)) * k = E.
## this k is unique, up to adding (q-1) multiples.
## input:
## E is the set of exponent of eigenvalues in respect to a fixed primitve element of the field
## n the n-th symmetric power.
## q the order of the underlying field.
## return k such that E = k * {-s,-s+2,..., s-2, s}.
## Note: k is unique up to sign for the considered cases.
RECOG.EVNatRep := function(E,n,q)
    local k,l ,res, Exp;
    res := 0;
    Exp:=List([0..n], x -> (n-2*x) mod (q-1));
    for k in PrimeResidues(q-1) do
        l := OrderMod(k,q-1)-1; # inverse of k in Z_q-1.
        if Set(E*(k^l) mod (q-1)) = Set(Exp) then
            res := k;
            break;
        fi;
    od;
    return res;
end;;



## Symmetric Power Basis ###
## representation of SL(2,q) in GL(T_n) for n < p.
## find an element g having N distinct eigenvalues;
## if G is symmetric power of SL(2, q) n<p.
## find a geometric progression ; order eigenspaces to give
## a basis exhibiting diagonalisation of g.
##input:
## G n-th symmetric power of SL(2,q) n<p.
## return : Basis of the form (x^n, x^(n-1)y, ...,y^n) and the corresponding element g.

RECOG.SymmetricPowerBasis:= function (G)
    local F,z,q,p,n, #casual variables.
    k,               #z^k is eigenvalue of g on x.
    M,               # returned basis ( x^n,..., y^n)
    Ek,              #exponents of eigenvalues of g to fixed z.
    g,               #order q-1
    h,               # <g,h> = G. And h conjugated to g.
    con ,            # random conjugation element
    i,               # iterating through columns
    mu_i ,           # coefficients of basis element
    abZero ,         # if ab = 0 we take the last row, if ab not zero, we takte the first row of h.
    ab,              # coefficents to
    mu_bet           # coefficents to
    ;
    F := FieldOfMatrixGroup(G);
    z:= PrimitiveElement(F);
    n := DimensionsMat(PseudoRandom(G))[1] -1;
    q := Size(F);
    p := Characteristic(F);
    k :=1;
    if q < 6 or ((p mod 2 = 1) and q = p and p > 6 and n > (p-7)/2 and (not (p = 13 and n =4) )) then
        ErrorNoReturn (" Exceptional Case , use another method ");
    fi;
    if (Size(PseudoRandom(G)) mod 2 = 0) then
        g := RECOG.RandomElementOfOrder(G,q-1)[1];
    else
        g:= RECOG.RandomElementOfOrder(G,(q-1)/2)[1];
    fi;
    ####### Added by me #######
    if g = "fail" then
        return ["fail"];
    fi;
    ###########################
    Ek:= List(Eigenvalues(F,g), x -> LogFFE(x,z));
    k := RECOG.EVNatRep(Ek,n,q);
    M:= RECOG.OrderEigenvectors(g,List([0..n], x -> (n-2*x) mod (q-1) ), F, k);
    ####### Added by me #######
    if M = [] then
        return ["fail"];
    fi;
    ###########################
    #correct coefficients of ( x^(n-2)y^2,..,y^n)
    con := IdentityMat(n+1,F);
    while g*g^con = g^con*g do
        con:= PseudoRandom(G);
    od;
    h := M*g^con*M^(-1); # <g,h> = G.
    if not (h[1] in Subspace(VectorSpace(F,g), [IdentityMat(n+1,F)[1]]) or h[1] in Subspace(VectorSpace(F,g), [IdentityMat(n+1,F)[n+1] ])) then
        abZero :=1;
    else
        abZero := n+1;
    fi;
    ab := h[abZero][1] / (n^(-1)* h[abZero][2]); mu_bet := z^0;
    for i in [2..n] do
        mu_i := mu_bet*Binomial(n,i-1)^(-1)*ab^(-1)* h[abZero][i] /(Binomial(n,i)^(-1)*h[abZero][i+1]);
        mu_bet := mu_i;
        M[i+1]:= mu_i^(-1)*M[i+1];
    od;
    return [M,g];
end ;;



## For a symmetric power G and elm of G construct image in PSL(2,q).
## input: G   symmetric power of SL(2,q) of degree n < p.
##        elm   arbitrary matrix in G.
##        Trafo   the basis of the form (x^n, ..., y^n) for some element of order q-1 and eigenvectors x and y on the natrual module of SL(2,q).
## return: image of elm in PSL(2,q) for one possible homomorphism of
RECOG.HomToPSL := function (G, elm, Trafo, nOdd)
    local
    F, # field of matrix group
    n, # degree of the symmetric power
    z, # primitives element of the field
    M, # the basis of the form (x^n,..., y^n)
    h, # elm represented in M
    k, # exponend of a^2 or d^2
    ba,ca,da,a2,a,cd,bd,d2,d,bc,c2,c, #quotients ba = b/a.
    V;
    F:= FieldOfMatrixGroup(G); z:= PrimitiveElement(F);
    M :=Trafo;
    n:= Size(M)-1;
    h := M * elm * M^(-1);
    V:= VectorSpace(F,M); # equals F^(n+1)
    if not h[1] in Subspace(V,[IdentityMat(n+1, F)[n+1]]) then #check if a=0
        ba := (h[1][2]*n^(-1))/ h[1][1];
        ca := h[2][1]/ h[1][1];
        da := h[2][2]/h[1][1] - (n-1)*ba*ca; a2 :=1/ (da - ba*ca); k:=LogFFE(a2,z);
        if nOdd then
            a := h[1][1]/(a2)^(QuoInt(n,2));
        elif k mod 2 = 0 then
            a := z^(k/2);
        else
            ErrorNoReturn("Something is wrong.");
        fi;
        return [[a,ba*a],[ca*a,da*a]];
    elif not h[n+1] in Subspace(V,[IdentityMat(n+1,F)[1] ]) then #check if d =0
        cd := (h[n+1][n]*n^(-1))/h[n+1][n+1]; bd := h[n][n+1] / h[n+1][n+1];
        d2 :=1 / ( - bd * cd);
        k := LogFFE(d2,z);
        if nOdd then
            d := h[n+1][n+1] / (d2)^(QuoInt(n,2));
            elif k mod 2 = 0 then d := z^(k/2);
        else
            ErrorNoReturn("Something is wrong.");
        fi;
        return [[0,bd*d],[cd*d,d]];
    else
        #if a=d=0
        bc := h[1][n+1]/ h[2][n]; c2 := -(bc)^(-1);
        k := LogFFE(c2,z);
        if nOdd then
            c := h[n+1][1] / (c2)^(QuoInt(n,2));
        elif k mod 2 = 0 then
            c := z^(k/2);
        else
            ErrorNoReturn("Something is wrong.");
        fi;
        return [[0,bc*c],[c,0]];
    fi;
end;;



## MAIN FUNCTION
## G n-th symmetric power of SL(2,q) in GL(T_n) for n < p.
## return [homomorphism from G to PSL(2,q), homomorphism from SL(2,q) to G]
RECOG.RecTest := function(G)
    local Trafo ,d, F;
    Trafo:= RECOG.SymmetricPowerBasis(G)[1];
    if Trafo = "fail" then
        return fail;
    fi;
    F:= FieldOfMatrixGroup(G); # underlying field
    d:= Size(PseudoRandom(G))-1; # d-th symmetric power
    return [x-> RECOG.HomToPSL(G,x,Trafo, d mod 2 = 1), x->Trafo^(-1)*RECOG.SymPowRepSL2(F,d,x)*Trafo];
end;;



###################################################################################################
###################################################################################################
######## Decomposition of Tensor Products #########################################################
###################################################################################################
###################################################################################################



# given sequence E of elements of finite field, construct certain
#   arithmetic progressions; if MaxAP is true, give up as soon as
#   we find one of length #E */

# If unset: MaxAP := false
RECOG.FindAPs := function (E, deg, p, MaxAP)
local AP, first, x, y, index, d, list, i, term;

    if Size(E) <= 1 then
        return [];
    fi;

    AP := [];
    for first in [1..Size(E)] do
        x := E[first];
        for index in [1..Size(E)] do
            if index <> first then
                y := E[index];
                d := y - x;
                list := [x, y];
                if ((deg mod 2) = 0) then
                    Append (AP, list);
                fi;
                for i in [3..Size(E)] do
                    if MaxAP = false and Size(list) >= p then
                        break;
                    fi;
                    term := list[i - 1] + d;
                    if (term in E) and not(term in list) then
                        list[i] := term;
                        if ((deg mod i) = 0) then
                            Append (AP, list);
                        fi;
                    else
                        break;
                    fi;
                od;
                if MaxAP and Size(list) = Size(E) then
                    return [list];
                fi;
            fi;
        od;
    od;

    return Set(AP);
    #return SetToSequence (Set (AP));

end;



RECOG.RandomElementOfOrderModuleCentre := function(G, required, MaxTries, Central)
local nrTries ,g, ord, centre;

    nrTries := 0;
    centre := Centre(G.group);
    while nrTries < MaxTries do
        g := PseudoRandom(G.group);
        ord := Order(g);
        if (ord = 2*required) then
            if (g^(required) in centre) then
                return [true, g, nrTries];
            fi;
            Display("nop");
            #return [true, g, nrTries];
        fi;
        nrTries := nrTries +1;
    od;
    ####### Added by Daniel Rademacher #######
    return ["fail", "fail", nrTries];

end;



# construct space determined by g and arithmetic progression a
#   of its eigenvalues, and send space to FindPoint

RECOG.ProcessSequence := function(G, g, a)
local F, w, ev, Space, CB, Status, gens, vec;

    F := G.fld;
    w := PrimitiveElement(F);
    ev := List(a, x-> w^(Int(x)));
    # Maybe this line means to make one list with all the spaces? If yes, modify other lines like this too.... Space := &+[Eigenspace (g, e): e in ev];
    Space := List(ev, e -> RECOG.EigenspaceMat(g,e));
    gens := [];
    for vec in Space do
        Append(gens,vec);
    od;
    Space := VectorSpace(F,gens);
    CB := "unknown";
    Status := false;
    Space := RECOG.GeneralFindPoint(G, Space, Dimension(Space), Status, CB, true);
    Status := Space[2];
    CB := Space[3];
    Space := Space[1];
    return [Status, CB];
end;


 
RECOG.StoreDetails := function(G, Result)
local U,W, CB;
    CB := Result[1];
    RECOG.SetTensorProductFlag(G, true);
    RECOG.SetTensorBasis(G, CB);
    U := RECOG.ConstructTensorFactors(G, Result);
    W := U[2];
    U := U[1];
    RECOG.SetTensorFactors (G, [U, W]);
end;



# G is a tensor product of symmetric powers of SL(2, q)
#   twisted under action of Frobenius maps;
#   decompose one symmetric power

RECOG.DecomposeTensor := function (G, F)
local d, p, f, q, i, factors, g, list, u, w, NmrTries, required, lambda, original, eigenvectors, multiplicity, nmr, E, least, flag, Result, index, first, step, a, x, y, term, lp, Zq, primitiveEle;

    # TODO: Add check whether G is already prepared
    G := RECOG.PrepareTensor(G);

    d := G.d;
    if d = 2 then
        return [false,false];
    fi;

    q := Size(F);
    f := Factors(q);
    p := f[1];
    f := Size(f);

    if ( ( p mod 2 = 1) and ((f = 2 and (d in [(p - 1)^2, p * (p - 1)])) or (d = p^f))) or (p = 2 and f = 2 and d = 4) then
        Print("sl2q: Need special version of DecomposeTensor for these cases \n");
        return fail;

        # TODO: NON-GENERIC CASES. DEAL WITH THEM LATER

        # if d mod p = 0 then
        #     factors := [[p, Int(d/p)]];
        # elif d mod (p - 1) = 0 then
        #     factors := [[p - 1, Int(d/(p - 1))]];
        # fi;
        # # TODO: Need is Tensor
        # flag := RECOG.IsTensor(G, factors);
        # if flag then
        #     list := RECOG.TensorDimensions(G);
        #     u := list[1];
        #     w := list[2];
        #     #TODO: Write this in GAP
        #     #Result := <TensorBasis (G), u>;
        #     return [true, Result];
        # else
        #     return [false,false];
        # fi;
    fi;

    NmrTries := 100;
    if p = 2 then
        required := (q-1);
    else
        required := (q-1)/2;
    fi;
    flag := RECOG.RandomElementOfOrderModuleCentre(G, required, NmrTries, true);
    g := flag[2];
    flag := flag[1];
    if not(flag) then
        Print("sl2q: Failed to find element of order ", required);
        return [false, false];
    fi;

    lambda := Eigenvalues(F,g);
    #eigenvectors := Eigenvectors(F,g);
    original := Size(lambda);
    Print("sl2q: Number of eigenvalues is ", original, "\n");

    lambda := List([1..original], i -> [lambda[i],Size(RECOG.EigenspaceMat(g,lambda[i]))]);
    lambda := Filtered(lambda, x -> x[2] = 1);

    Print("sl2q: Number of eigenvalues of multiplicity 1 = ", Size(lambda), "\n");
    if Size(lambda) <= 1 then
        Print("sl2q: Too few eigenvalues left \n");
        return [false, false];
    fi;

    # are there multiplicities in eigenvalues?
    multiplicity := Size(lambda) < original;

    primitiveEle := PrimitiveElement(GF(q));
    E := List(lambda, x -> LogFFE(primitiveEle,x[1]));
    Zq := ZmodnZ(q-1);
    E := List(E, x-> ZmodnZObj(ElementsFamily(FamilyObj(Zq)),x));

    nmr := 0;

    # largest prime dividing d
    lp := Maximum(Factors(d));

    # minimum length of AP if multiplicity among EVs
    least := (p + 1)/2;

    # construct arithmetic progressions of length ell,
    # where ell is at most p and ell is a multiple of lp;
    # if multiplicity-free then ell is proper divisor of d;
    # if not, then ell >= least

    for first in [1..Size(E)] do
        x := E[first];
        for index in [1..Size(E)] do
            if index = first then
                continue;
            fi;
            y := E[index];
            step := y - x;
            a := [x, y];
            if d mod Size(a) = 0 then
                if (multiplicity and Size(a) >= least) or (not(multiplicity) and Size(a) mod lp = 0) then
                    flag := RECOG.ProcessSequence(G, g, a);
                    Result := flag[2];
                    flag := flag[1];
                    nmr := nmr + 1;
                    if flag then
                        RECOG.StoreDetails (G, Result);
                        Print("sl2q: Arithmetic progression is ", a);
                        Print("sl2q: Number of calls to FindPoint is", nmr);
                        return [true, Result];
                    fi;
                fi;
            fi;

            # construct APs of length at most p; if the length
            # of the AP properly divides the degree of G,
            # then send space to FindPoint
            for i in [3..p] do
                term := a[i - 1] + step;
                if not(term in E) then
                    break;
                fi;
                if (term in a) then
                    break;
                fi;
                a[i] := term;
                if Size(a) > (d/2) then
                    break;
                fi;
                if (d mod Size(a)) = 0 then
                    if (multiplicity and Size(a) >= least) or (not(multiplicity) and (Size(a) mod lp) = 0) then
                        flag := RECOG.ProcessSequence(G, g, a);
                        Display("process 1");
                        Result := flag[2];
                        flag := flag[1];
                        nmr := nmr + 1;
                        if flag then
                            Print("sl2q: Arithmetic progression is ", a);
                            Print("sl2q: Number of calls to FindPoint is", nmr);
                            RECOG.StoreDetails(G, Result);
                            return [true, Result];
                        fi;
                    fi;
                fi;
            od;
        od;
    od;

    return [false,false];

end;



###################################################################################################
###################################################################################################
######## Symmetric Powers and Twisted Tensor Products #############################################
###################################################################################################
###################################################################################################



RECOG.SymmetricPowerSL2 := function (q, n)
local G, fld, gens, res, g;

   gens := GeneratorsOfGroup(SL(2,q));
   res := [];
   fld := GF(q);
   for g in gens do
        Add(res,RECOG.SymPowRepSL2(q,n,g));
    od;
   return GroupByGenerators(res);
   #return ActionGroup (A);
end;

#   given matrix x, return result of applying Frobenius automorphism
#  x[i][j] --> x[i][j]^n to it
RECOG.GammaLMatrix:=function(x,d,n)
local G,i,j,y;

  if not(IsMutable(x)) then
    x := MutableCopyMat(x);
  fi;

  for i in [1..d] do
    for j in [1..d] do
        x[i,j] := x[i,j]^n;
    od;
  od;
  return x;
end;



RECOG.TwistedSymmetricPower:=function(q,s,f)
local F,Gens,S,Twisted,p,i,d;
  F:=GF(q);
  p:=Characteristic(F);
  S:=RECOG.SymmetricPowerSL2(q,s);
  Gens:=GeneratorsOfGroup(S);
  d := NumberRows(Gens[1]);
  Twisted:=List([1..Size(Gens)],i->RECOG.GammaLMatrix(Gens[i],d,p^f));
  return GroupByGenerators(Twisted);
end;



#   tensor product of twisted symmetric powers defined
#  over GF (p^e); s lists the symmetric powers,
#  f is the twisting via powers of the Frobenius
#  automorphism to be applied to each symmetric power
RECOG.SymmetricPowerExample:=function(p,e,s,f)
local F,q,G,L,T2,i,gens,j,gens2;
  F:=GF(p^e);
  q:= p^e;
  L:=SL(2,F);
  G:=RECOG.TwistedSymmetricPower(q,s[1],f[1]);
  if Size(s) = 1 then
    return G;
  fi;
  for i in [2..Size(s)] do
    T2:=RECOG.TwistedSymmetricPower(q,s[i],f[i]);
    gens := GeneratorsOfGroup(G);
    gens2 := [1..Size(gens)];
    for j in [1..Size(gens)] do
        gens2[j] := KroneckerProduct(gens[j],GeneratorsOfGroup(T2)[j]);
    od;
    G:=GroupByGenerators(gens2);
  od;
  return G;
end;
