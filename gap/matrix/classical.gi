#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This files's authors include Alice Niemeyer.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
##  This file contains an implementation of the non-constructive recognition
##  algorithms for classical groups in their natural representation by
##  Niemeyer and Praeger.
##
##  A description of them can be found in [NP97], [NP98], and [NP99].
##
##  This implementation uses some algorithms described elsewhere, in:
##  [CLG97a], [CLG97b], and [CLGM+95].
##
##  - In this implementation we use the irreducibility test of the algorithm
##    described in [CLG97b], which can often avoid an application of the
##    Meataxe algorithm.
##
##  For an overview, see also [Pra99].
##
#############################################################################

BindGlobal( "ClassicalMethDb", [] );

BindGlobal( "FindHomMethodsClassical", rec() );

#
###
# Test whether <n> (assumed integer) is a power of 2
IsPowerOfTwo := n -> n > 1 and 2 ^ Log2Int(n) = n;


# Check if m > 5 and the order of a basic lppd(d,q;e) element

HasLBGgt5 := function( m, p, a, e )

    local pm, i,  ppds;

    if m <= 5 then
        return false;
    fi;

    # Find the basic ppds of p^(ae)-1
    pm := PrimitivePrimeDivisors(a*e, p);
    # find the ppds in m
    ppds := GcdInt(pm.ppds, m);

    # There are no ppds
    if ppds = 1 then
        return false;
    fi;

    ## if e+1 does not divide ppds then
    ## we know that all primes dividing ppds are large
    ## and hence we know <m> is a large ppd-element
    if ppds mod (e+1) = 0 then
        ## Now we know (e+1) divides ppds and (e+1) has to be
        ## a prime since all ppds are at least (e+1)
        if not IsPrimeInt (e+1) then
             return false;
         fi;
         # if (e+1)^2 does not divide m, then not large
         if not (m mod (e+1)^2) = 0 then
             return false;
         fi;
     fi;

     return true;
end;


# "Inverse" to KroneckerProduct on 2x2 matrices -- does not handle inputs with
# a zero block in the top left (but the code calling this deals with this by
# simply looking at another random element)
BindGlobal("KroneckerFactors", function(g)
    local a, b, c, d, A, Ainv, B, C, D, I;

    A := g{[1,2]}{[1,2]};
    if IsZero(Determinant(A)) then
        return false;
    fi;
    Ainv := A^-1;
    B := g{[1,2]}{[3,4]};
    C := g{[3,4]}{[1,2]};
    D := g{[3,4]}{[3,4]};
    B := B * Ainv; b := B[1,1];
    C := C * Ainv; c := C[1,1];
    D := D * Ainv; d := D[1,1];

    I := A^0;
    if B <> I*b or C <> I*c or D <> I*d then
        return false;
    fi;

    return [ [[I[1,1], b], [c, d]], A ];
end);


######################################################################
##
#F  FindBase (field, phi) . . . . . . . . . . . find appropriate basis
##
##  The following function returns a matrix B such that B phi B^T has
##  the form ( 0, 0, 0, -1), ( 0, 0, 1, 0 ) (0, 1, 0, 0), (-1, 0, 0, 0)
##
FindBase := function( field, phi )

     local form, mat1, mat2, mat;

     form := BilinearFormByMatrix(
          [[ 0,0,0,-1],[ 0,0,1,0],[0,1,0,0],[-1,0,0,0]]*One(field), field);
     mat1 := BaseChangeToCanonical(phi);
     mat2 := BaseChangeToCanonical(form);
     mat := LeftQuotient(mat2, mat1);
     return mat;

end;

FindBaseC2 := function( field, qf )

     local form2, mat, mat2;

     form2 := QuadraticFormByMatrix(
             [[0,0,0,-1],[0,0,1,0],[0,0,0,0],[0,0,0,0]]*One(field), field);
     mat := BaseChangeToCanonical(qf);
     mat2 := BaseChangeToCanonical(form2);
     mat := mat2 / mat;
     return mat;

end;



# Test to check whether the group contains both a large ppd element
# and a basic ppd element
# TODO: Better comments...
BindRecogMethod(FindHomMethodsClassical, "IsGenericParameters",
"tests whether group has generic parameters",
function( recognise, grp )
    local fact, d, q, hint;

    hint := recognise.hint;

    d := recognise.d;
    q := recognise.q;

    if hint = "unknown"  then
        return false;

    elif hint = "linear" and d <= 2 then
        recognise.isGeneric := false;
        return false;

    elif hint = "linear" and d = 3 then
        #q = 2^s-1
        if IsPowerOfTwo( q+1 ) then
            recognise.isGeneric := false;
        fi;
        return false;

    elif hint = "symplectic" and
      (d < 6 or (d mod 2 <> 0) or
       [d,q] in [[6,2],[6,3],[8,2]]) then
        recognise.isGeneric := false;
        return false;

    elif hint = "unitary" and
      (d < 5 or d = 6 or [d,q] = [5,4]) then
        recognise.isGeneric := false;
        return false;

    elif hint = "orthogonalplus" and
      (d mod 2 <> 0 or d < 10
       or (d = 10 and q = 2)) then
        recognise.isGeneric := false;
        return false;

    elif hint = "orthogonalminus" and
      (d mod 2 <> 0 or d < 6
       or [d,q] in [[6,2],[6,3],[8,2]]) then
        recognise.isGeneric := false;
        return false;

    elif hint = "orthogonalcircle" then
        if d < 7 or [d,q] = [7,3] then
            recognise.isGeneric := false;
            return false;
        fi;
        if d mod 2 = 0 then
            recognise.isGeneric := false;
            return false;
        fi;
        if q mod 2 = 0 then
            #TODO: INFORECOG1 ... not irreducible
            #TODO: INFORECOG2 ... d odd --> q odd
            recognise.isReducible := true;
            recognise.isGeneric := false;
            return false;
        fi;
    fi;

    return false;
end);


# Generate elements until we find the required ppd type
# elements...monte  yes
# TODO: Better comments

BindRecogMethod(FindHomMethodsClassical, "IsGeneric",
"tests whether group is generic",
function (recognise, grp)
    if recognise.isGeneric = false then
        return NeverApplicable;
    fi;

    if Length(recognise.E) < 2 or
       Length(recognise.LE) = 0 or
       Length(recognise.BE) = 0 then
        return TemporaryFailure;
    fi;

    recognise.isGeneric := true;
    return NeverApplicable;
end);

#enough info to rule out extension field groups...?
#TODO: comments...
BindRecogMethod(FindHomMethodsClassical, "RuledOutExtField",
"tests whether extension field case is ruled out",
function (recognise, grp)
    local differmodfour, d, q, E, b, bx, hint;

    hint := recognise.hint;
    d := recognise.d;
    q := recognise.q;
    E := recognise.E;

    differmodfour := function(E)
        local e;
        for e in E do
            if E[1] mod 4 <> e mod 4 then
                return true;
            fi;
        od;
        return false;
    end;

    b := recognise.currentgcd;

    if hint in ["linear","unitary","orthogonalcircle"] then
        bx := 1;
    else
        bx := 2;
    fi;


    if b < bx then
        if hint <> "unknown" then
           recognise.hintIsWrong := true;
           # raeume auf + komme nie wieder
           return true;
        fi;
        recognise.isNotExt := true;
        return false;
    fi;
    if b > bx then
        return fail;
    fi;

    if hint = "linear" then
        if not IsPrime(d)
           or E <> [d-1,d]
           or d-1 in recognise.LE then
            recognise.isNotExt  := true;
            return false;
        fi;

    elif hint = "unitary" then
        recognise.isNotExt  := true;
        return false;

    elif hint = "symplectic" then
        if d mod 4 = 2 and q mod 2 = 1 then
             recognise.isNotExt := ForAny(E, x -> x mod 4 = 0);
        elif  d mod 4 = 0 and q mod 2 = 0 then
             recognise.isNotExt := ForAny(E, x -> x mod 4 = 2);
        elif d mod 4 = 0 and q mod 2 = 1 then
             recognise.isNotExt := differmodfour(E);
        elif d mod 4 = 2 and q mod 2 = 0 then
            recognise.isNotExt :=  (Length(E) > 0);
        else
           Info( InfoClassical, 2, "d cannot be odd in hint Sp");
           recognise.hintIsWrong := true;
           # raeume auf + komme nie wieder
           return true;
        fi;

    elif hint = "orthogonalplus" then
        if d mod 4 = 2  then
            recognise.isNotExt  := ForAny(E, x -> x mod 4 = 0);
        elif d mod 4 = 0  then
            recognise.isNotExt  := differmodfour(E);
        else
           Info( InfoClassical, 2, "d cannot be odd in hint O+");
           recognise.hintIsWrong := true;
           # raeume auf + komme nie wieder
           return true;
        fi;


    elif hint = "orthogonalminus" then
        if d mod 4 = 0  then
            recognise.isNotExt  := ForAny(E, x -> x mod 4 = 2);
        elif d mod 4 = 2  then
            recognise.isNotExt  := differmodfour(E);
        else
           Info( InfoClassical, 2, "d cannot be odd in hint O-");
           recognise.hintIsWrong := true;
           # raeume auf + komme nie wieder
           return true;
        fi;

    elif hint = "orthogonalcircle" then
        recognise.isNotExt  := true;
        return false;
    fi;

    if recognise.isNotExt = true then return false;
    else return fail;
    fi;
end);

BindRecogMethod(FindHomMethodsClassical, "IsNotAlternating",
"tests whether alternating groups are ruled out",
function( recognise, grp )
    local V, P, i, g ,q, o;

    q := recognise.q;

#   if recognise.hint <> "unknown" and recognise.hint <> "linear" then
#       Info( InfoClassical, 2, "G' not an AlternatingGroup;");
#       recognise.isNotAlternating := true;
#       return false;
#   fi;

    if Length(recognise.ClassicalForms) > 0 and
        First(recognise.ClassicalForms,IsTrivialForm)=fail then
       recognise.isNotAlternating := true;
       return false;
    fi;

    if recognise.d <> 4 or q <> recognise.p or (3 <= q and q < 23) then
       Info( InfoClassical, 2, "G is not an alternating group" );
       recognise.isNotAlternating := true;
       return false;
    fi;

    if q = 2 then
       if Size(grp) <> 2520 then  # 2520 = 3*4*5*6*7 = |A7|
           Info( InfoClassical, 2, "G is not an alternating group" );
           recognise.isNotAlternating := true;
           return false;
       else
           Info( InfoClassical, 2, "G' might be A7;");
           AddSet(recognise.possibleNearlySimple,"A7");
           return true;
       fi;
    fi;


    if q >= 23 then
        # TODO Check Magma Code
       o := Order( recognise.g );
       if o mod 25 = 0 then
           Info( InfoClassical, 2, "G' not alternating;");
           recognise.isNotAlternating := true;
           return false;
       fi;
       o := Collected( Factors (o) );
       for i in o do
           if i[1] >= 11 then
               Info( InfoClassical, 2, "G' not alternating;");
               recognise.isNotAlternating := true;
               return false;
           fi;
       od;

       if recognise.n > 15 then
           AddSet (recognise.possibleNearlySimple, "2.A7");
           Info( InfoClassical, 2, "G' might be 2.A7;");
           return  fail;
       fi;
   fi;

   return fail;

end);



BindRecogMethod(FindHomMethodsClassical, "IsNotMathieu",
"tests whether Mathieu groups are ruled out",
function( recognise, grp )
   local i, fn, g, d, q, E, ord;

   d := recognise.d;
   q := recognise.q;
   E := recognise.E;
   g := recognise.g;

#   if recognise.hint <> "unknown" and recognise.hint <> "linear" then
#       Info( InfoClassical, 2, "G' not a Mathieu Group;");
#       recognise.isNotMathieu := true;
#       return false;
#   fi;

    if Length(recognise.ClassicalForms) > 0 and
        First(recognise.ClassicalForms,IsTrivialForm)=fail then
       recognise.isNotMathieu := true;
       return false;
    fi;

   if not [d, q]  in [ [5, 3], [6,3], [11, 2] ] then
       Info( InfoClassical, 2, "G' is not a Mathieu group;");
       recognise.isNotMathieu := true;
       return false;
   fi;

   if d  in [5, 6] then
       ord := Order(g);
       if (ord mod 121=0 or (d=5 and ord=13) or (d=6 and ord=7)) then
          Info( InfoClassical, 2, "G' is not a Mathieu group;");
          recognise.isNotMathieu := true;
          return false;
       fi;
   else
       if ForAny([6,7,8,9], m -> m in E) then
          Info( InfoClassical, 2, "G' is not a Mathieu group;");
           recognise.isNotMathieu := true;
           return false;
       fi;
   fi;


# TODO Check how big n should be
    if d = 5 then
        if recognise.n > 15 then
            AddSet(recognise.possibleNearlySimple, "M_11" );
            Info( InfoClassical, 2, "G' might be M_11;");
            return fail;
        fi;
    elif d = 6 then
        if recognise.n > 15 then
            AddSet(recognise.possibleNearlySimple, "2M_12" );
            Info( InfoClassical, 2, "G' might be 2M_12;");
            return fail;
        fi;
    else
        if recognise.n > 15 then
            AddSet(recognise.possibleNearlySimple, "M_23" );
            AddSet(recognise.possibleNearlySimple, "M_24" );
            Info( InfoClassical, 2, "G' might be M_23 or M_24;");
            return fail;
        fi;
    fi;

   return fail;

end);


BindRecogMethod(FindHomMethodsClassical, "IsNotPSL",
"tests whether PSL groups are ruled out",
function (recognise, grp)
   local i, E, LE, d, p, a, q,  str, fn, ord;

    E := recognise.E;
    LE := recognise.LE;
    d := recognise.d;
    q := recognise.q;
    a := recognise.a;
    p := recognise.p;

#    if recognise.hint <> "unknown" and recognise.hint <> "linear" then
#        Info( InfoClassical, 2, "G' not PSL(2,r);");
#        recognise.isNotPSL := true;
#        return false;
#    fi;
    if Length(recognise.ClassicalForms) > 0 and
        First(recognise.ClassicalForms,IsTrivialForm)=fail then
       recognise.isNotPSL := true;
       return false;
    fi;

    if d = 3 and (q = 5 or q = 2) then
        Info( InfoClassical, 2,  "G' is not PSL(2,7)");
        recognise.isNotPSL := true;
        return false;
    fi;

    if d = 6 and q = 2 then
        Info( InfoClassical, 2,  "G' is not PSL(2,11)");
        recognise.isNotPSL := true;
        return false;
    fi;

    # test whether e_2 = e_1 + 1 and
    # e_1 + 1 and 2* e_2 + 1 are primes
    if  Length(E) >= 2 then
        if E[2]-1<>E[1] or
            not IsPrimeInt(E[1]+1) or not IsPrimeInt(2*E[2]+1) then
            Info(InfoClassical, 2, " G' is not PSL(2,r)");
            recognise.isNotPSL := true;
            return false;
        fi;
    fi;

   if d = 3 then
       # q = 3*2^s-1 and q^2-1 has no large ppd.
       # TODO recheck this
       if (q = 2 or ((q+1) mod 3 = 0 and IsPowerOfTwo((q+1)/3))) then
            ord := Order(recognise.g);
            if (ord mod 8 <> 0 or (p^(2*a)-1) mod ord = 0) then
                Info( InfoClassical, 2, "G' not PSL(2,7);");
                recognise.isNotPSL := true;
                return false;
           fi;
       else
           if p = 3 or p = 7 or 2 in LE then
                Info( InfoClassical, 2, "G' not PSL(2,7);");
                recognise.isNotPSL := true;
                return false;
           fi;
       fi;
   elif [d, q]  = [5,3] then
       ord := Order(recognise.g);
       if (ord mod 11^2 = 0  or ord mod 20 = 0) then
           Info( InfoClassical, 2, "G' not PSL(2,11);");
           recognise.isNotPSL := true;
           return false;
       fi;
   elif d = 5  and p <> 5 and p <> 11 then
       if (3 in LE or 4 in LE) then
           Info( InfoClassical, 2, "G' not PSL(2,11);");
           recognise.isNotPSL := true;
           return false;
       fi;
   elif [d, q]  = [6, 3] then
       ord := Order(recognise.g);
       if (ord mod (11^2)=0 or 6 in E) then
           Info( InfoClassical, 2, "G' not PSL(2,11);");
           recognise.isNotPSL := true;
           return false;
       fi;
   elif d = 6 and p <> 5 and p <> 11 then
       if  (6 in E or 4 in LE) then
           Info( InfoClassical, 2, "G' not PSL(2,11);");
           recognise.isNotPSL := true;
           return false;
       fi;
   else
       Info( InfoClassical, 2, "G' not PSL(2,r);");
       recognise.isNotPSL := true;
       return false;
   fi;


   if recognise.n > 15  and Length(recognise.E) > 2 then
       str := Concatenation("PSL(2,",Int(2*E[2]+1));
       str := Concatenation(str, ")");
       Info( InfoClassical, 2, "G' might be ", str);
       AddSet( recognise.possibleNearlySimple, str );
       return fail;
   fi;
   return fail;
end);


#############################################################################
##
## IsPrimitivePrimeDivisor . . . . . . . . . . . . . . ( b, a, p )
##
## Test whether p is a primitive prime divisor of b^a-1.
##
IsPrimitivePrimeDivisor := function( b, a, p )

    local i;

    if not IsPrimeInt(p) then
        return false;
    fi;
    if not IsInt(b) or b <= 1 then
        return false;
    fi;
    if not IsInt(a) or a <= 1 then
        return false;
    fi;

    if (b^a-1) mod p <> 0 then
        return false;
    fi;
    for i in [ 1 .. a-1 ] do
        if b^i-1 mod p = 0 then
            return false;
        fi;
    od;

    return true;
end;

# generate the next random element and its char polynomial
BindRecogMethod(FindHomMethodsClassical, "TestRandomElement",
"makes new random element and stores it and its char poly",
function(recognise, grp)
    local g, ppd, bppd, d, q, cpol, f, deg, facs, r, s, h, gmod, str,
    ord, bc, phi, kf, o1, o2, cf, i, found, p;

    recognise.g := PseudoRandom(grp);
    recognise.cpol := CharacteristicPolynomial(recognise.g);
    recognise.n := recognise.n + 1;

    d := recognise.d;
    q := recognise.q;
    p := recognise.p;
    f := recognise.field;
    g := recognise.g;
    cpol := recognise.cpol;

    if recognise.needOrders then
        ord := Order(g);
        recognise.ord := ord;
        AddSet( recognise.orders, ord );
    fi;
    if recognise.needPOrders then
        ord := ProjectiveOrder(g);
        AddSet( recognise.porders, ord );
    fi;

    ppd := IsPpdElement (f, cpol, d, q, 1);
    # if the element is no ppd we get out
    if ppd = false then
        recognise.isppd := false;
    else
        AddSet(recognise.E,ppd[1]);
        recognise.currentgcd := GcdInt( recognise.currentgcd, ppd[1] );
        if ppd[2] = true then
            AddSet(recognise.LE,ppd[1]);
        fi;
        recognise.ppd := [ ppd[1], ppd[2], "unknown" ];
        if Length(recognise.BE) < 1 or recognise.needLB then
            #We only need one basic ppd-element
            #Also, each basic ppd element is a ppd-element
            bppd := IsPpdElement (f, cpol, d, recognise.p, recognise.a);
            if bppd <> false then
                AddSet(recognise.BE, bppd[1]);
                if ppd[2] = true and ppd[1] = bppd[1] then
                    AddSet( recognise.LB, ppd[1] );
                    recognise.ppd[3] := true;
                fi;
            fi;
        fi;
    fi;
    if recognise.needE2 = true then
        ppd := IsPpdElementD2(f, cpol, d, recognise.q, 1);
        if ppd <> false then
            str := "  Found a large and special ppd(";
            str := Concatenation(str, String(recognise.d));
            str := Concatenation(str, ", " );
            str := Concatenation(str, String(recognise.q));
            str := Concatenation(str, "; " );
            str := Concatenation(str, String(ppd[1]));
            str := Concatenation(str,  ")-element");


            AddSet( recognise.E2, ppd[1] );
            if ppd[2] = true then

            ## first we test whether the characteristic polynomial has
            ## two factors of degree d/2.
            facs := Factors( cpol );
            deg := List(facs, EuclideanDegree );
            if Length(deg) = 2 and deg[1] = deg[2] and deg[1] = d/2 then

              ## Bug fix 29.10.09
              ## Now we compute the r-part h of g
              s := Order(g);
              s := GcdInt(s, ppd[3]);
              h := g^s;
              ## now order(h) is the product of all ppds dividing |g|, see
              ##  Section 6.1 page 250 of [NP99]
              if IsOne(h) then
                  return TemporaryFailure;
              fi;
              gmod := GModuleByMats([h], recognise.field);
              cf := MTX.CollectedFactors(gmod);
              if Length(cf) = 2 and cf[1][2] = cf[2][2] then
                # we have two non-isomorphic composition factors
                Info(InfoClassical,2, str );
                AddSet(recognise.LS, ppd[1] );
              fi;

            fi;
          fi;
        fi;
    fi;


    if ForAny(recognise.E, x -> x mod 2 <> 0) then
        recognise.isSpContained := false;
        recognise.isSOContained := false;
    fi;
    if ForAny(recognise.E, x -> x mod 2 = 0) then
        recognise.isSUContained := false;
    fi;

    if recognise.needBaseChange = true and recognise.bc = "unknown" then
        if Length(recognise.ClassicalForms) = 0 then
            recognise.needForms := true;
            return NotEnoughInformation;
        fi;
        i := 1;  found := false;
        while not found and  i <= Length(recognise.ClassicalForms) do
           phi := recognise.ClassicalForms[i];
           if IsSesquilinearForm(phi)  then
                if IsOddInt (q) and IsHyperbolicForm(phi) then
                    Info(InfoClassical, 2,"Performing base change");
                    found := true;
                    bc := FindBase (f, phi);
                    Info(InfoClassical, 2,"Computed base change matrix");
                    bc := bc^-1;
                    recognise.bc := bc;
                elif IsEvenInt(q) and recognise.QuadraticForm <> false then
                    bc := FindBaseC2 (f, recognise.QuadraticForm);
                    found := true;
                    Info(InfoClassical,2,
                     "Computed base change matrix for char 2");
                    bc := bc^-1;
                    recognise.bc := bc;
                fi;
            fi;
            i := i + 1;
        od;
        if not found then
            Info(InfoClassical, 2, "need basechange only in O+");
            return fail;
        fi;
     fi;

     if recognise.needKF  = true  then
            if recognise.bc = "unknown" then
                recognise.needBaseChange := true;
            else
                kf := KroneckerFactors( g^recognise.bc );
                if kf = false then
                    kf := KroneckerFactors( (g^2)^recognise.bc );
                fi;
                recognise.kf  := kf;
            fi;
      fi;

      if recognise.needPlusMinus = true then
            if recognise.kf = "unknown" then
                recognise.needKF := true;
                return fail;
            fi;
            if recognise.kf = false then
                return fail;
            fi;
            kf := recognise.kf;
            o1 := ProjectiveOrder( kf[1] )[1];
            o2 := ProjectiveOrder( kf[2] )[1];
            #o1 := Order( kf[1] );
            #o2 := Order( kf[2] );
            Info(InfoClassical,2,o1, " ", o2);
            ### ACN March 2007 needed Projective order
            if  q mod 2 = 0 and (o1 <= 2 or o2 <= 2) then
                return TemporaryFailure;
            elif q mod 2 <> 0 and (o1 <= 4 or o2 <= 4) then
                return TemporaryFailure;
            fi;
            if ( (q+1) mod o1 = 0 and (q+1) mod o2 = 0) then
                if not IsPowerOfTwo(q+1) and q <> 8 then
                    if not ForAny( PrimeDivisors(o1), r ->
                      IsPrimitivePrimeDivisor(p,2*recognise.a,r)) then
                        return TemporaryFailure;
                    fi;
                    if not ForAny( PrimeDivisors(o2), r ->
                      IsPrimitivePrimeDivisor(p,2*recognise.a,r)) then
                        return TemporaryFailure;
                    fi;
                elif q = 8 then
                    if not o1 mod 9 = 0 or not o2 mod 9 = 0 then
                        return TemporaryFailure;
                    fi;
                else
                    if o1 < (q+1)/2 or o2 < (q+1)/2 then
                        return TemporaryFailure;
                    fi;
                fi;
                AddSet( recognise.plusminus, [1,1] );
            fi;
            if ( (q+1) mod o1 = 0 and (q-1) mod o2 = 0) then
                AddSet( recognise.plusminus, [1,-1] );
            fi;
            if ( (q-1) mod o1 = 0 and (q+1) mod o2 = 0) then
                AddSet( recognise.plusminus, [1,-1] );
            fi;
            if ( (q-1) mod o1 = 0 and (q-1) mod o2 = 0) then
                AddSet( recognise.plusminus, [-1,-1] );
            fi;
        fi;

        if recognise.needDecompose = true then
            if recognise.kf = "unknown" then
                recognise.needKF := true;
                return fail;
            elif recognise.kf = false then
                return fail;
            fi;
            kf := recognise.kf;

            if not kf[1] in Group(recognise.sq1) then
                AddSet(recognise.sq1,kf[1]);
            fi;
            if not kf[2] in Group(recognise.sq2) then
                AddSet(recognise.sq2,kf[2]);
            fi;
       fi;

    return fail;

end);



# Compute the degrees of the irreducible factors of
# the characteristic polynomial <cpol>
BindRecogMethod(FindHomMethodsClassical, "IsReducible",
"tests whether current random element rules out reducible",
function( recognise, grp )
    local deg, dims, g;

    # compute the degrees of the irreducible factors
    deg := List(Factors(recognise.cpol), Degree);

    # compute all possible dimensions
    dims := [0];
    for g in deg do
        UniteSet(dims,dims+g);
    od;

    # intersect it with recognise.dimsReducible
    if IsEmpty(recognise.dimsReducible) then
        recognise.dimsReducible := dims;
    else
        IntersectSet(recognise.dimsReducible,dims);
    fi;

    # G acts irreducibly if only 0 and d are possible
    if Length(recognise.dimsReducible)=2 then
        recognise.isReducible := false;
        return false;
    fi;

    return fail;
end);

BindRecogMethod(FindHomMethodsClassical, "NoClassicalForms",
"tests whether we can rule out certain forms",
function( recognise, grp )
    local d,field;
    PossibleClassicalForms( grp, recognise.g, recognise );

    d := recognise.d;
    field := recognise.field;
    if recognise.maybeDual = false and
      recognise.maybeFrobenius = false then
          if First(recognise.ClassicalForms,IsTrivialForm)=fail then
              Add(recognise.ClassicalForms,
              BilinearFormByMatrix(NullMat(d,d,field),field));
          fi;
          return false;
   fi;

    return fail;

end);



BindRecogMethod(FindHomMethodsClassical, "ClassicalForms",
"Find the invariant forms",
function( recognise, grp)
    local   field,  z,  d,  i,  qq,  A,  c,  I,  t,  i0,
            a,  l,  g,  module,  forms,  dmodule,  fmodule,  form;

    if recognise.n > 1 then
        recognise.needForms := true;
    fi;

    if recognise.needForms <> true then
        return NotEnoughInformation;
    fi;

    # the group has to be absolutely irreducible
    if recognise.isReducible = "unknown"  then
        recognise.needMeataxe := true;
        return fail;
    fi;

    # set up the field and other information
    field := recognise.field;
    d := recognise.d;
    z := Zero(field);
    module := recognise.module;

    if recognise.maybeFrobenius  = true then
        qq := Characteristic(field)^(DegreeOverPrimeField(field)/2);
    fi;

    # if all forms are excluded then we are finished
    if not recognise.maybeDual and not recognise.maybeFrobenius  then
        if First(recognise.ClassicalForms,IsTrivialForm)=fail then
            Add(recognise.ClassicalForms,
            BilinearFormByMatrix(NullMat(d,d,field), field ) );
        fi;
        return false;
    fi;


    # now try to find an invariant form
    if recognise.maybeDual then
        dmodule := ClassicalForms_GeneratorsWithoutScalarsDual(grp);
        if dmodule <> false then
            form := ClassicalForms_InvariantFormDual(module,dmodule);
            if form <> false  then
                Add( recognise.ClassicalForms,
                BilinearFormByMatrix(form[2], field));
                if Length(form)=4 then
                    recognise.QuadraticFormType := form[1];
                    recognise.QuadraticForm := QuadraticFormByMatrix(form[4]);
                fi;
                return false;
            else
                recognise.maybeDual := false;
            fi;
        fi;
    fi;

    if recognise.maybeFrobenius then
        fmodule := ClassicalForms_GeneratorsWithoutScalarsFrobenius(grp);
        if fmodule <> false then
            form := ClassicalForms_InvariantFormFrobenius(module,fmodule);
            if form <> false  then
                Add( recognise.ClassicalForms,
                     HermitianFormByMatrix(form[2], field));
               return false;
            else
                recognise.maybeFrobenius := false;
            fi;
        fi;
    fi;


    # if all forms are excluded then we are finished
    if not recognise.maybeDual and not recognise.maybeFrobenius  then
        if First(recognise.ClassicalForms,IsTrivialForm)=fail then
            Add(recognise.ClassicalForms,
            BilinearFormByMatrix(NullMat(d,d,field), field));
            return false;
        fi;
    fi;

    return fail;

end);


BindRecogMethod(FindHomMethodsClassical, "MeatAxe",
"Test irreducibility",
function( recognise, grp )
    if recognise.n > 15 then
        recognise.needMeataxe := true;
    fi;

    if recognise.needMeataxe <> true then
        return NotEnoughInformation;
    fi;


    if MTX.IsIrreducible(recognise.module) then
        recognise.isReducible := false;
        return false;
    else
        Info( InfoClassical, 2,
        "The group acts reducibly and thus doesn't contain a classical group");
        recognise.isReducible := true;
        recognise.isSLContained := false;
        recognise.isSpContained := false;
        recognise.isSUContained := false;
        recognise.isSOContained := false;
        return true;
    fi;
end);

## Main function to test whether group contains SL
BindRecogMethod(FindHomMethodsClassical, "IsSLContained",
"tests whether group contains SL",
function( recognise, grp )
    if recognise.isGeneric <> true or
       recognise.isNotExt <> true or
       recognise.isNotPSL <> true  or
       recognise.isReducible = true or
       recognise.isNotMathieu <> true or
       recognise.isNotAlternating <> true  then
          return fail;
    fi;


    if recognise.isReducible = "unknown" then
        recognise.needMeataxe := true;
        return NotEnoughInformation;
    fi;


    # if we reach this point the natural module is irreducible
    # since the MeatAxe Method aborts in the reducible case.
    # Also we know that the module is absolutely irreducible,
    # since we are in the generic case.
    if Length(recognise.ClassicalForms)=0 then
        recognise.needForms := true;
        return NotEnoughInformation;
    fi;

    if First(recognise.ClassicalForms, IsTrivialForm) <> fail then
        recognise.isSLContained := true;
        Info(InfoClassical,2,"The group contains SL(", recognise.d, ", ",
             recognise.q, ");");
        return true;
    else
        recognise.isSLContained := false;
        Info(InfoClassical,2,"The group does not contain SL(",
             recognise.d, ", ", recognise.q, ");");
        return false;
    fi;

end);

## Main function to test whether group contains Sp
BindRecogMethod(FindHomMethodsClassical, "IsSpContained",
"tests whether group contains Sp",
function( recognise, grp )
    local isSpForm;

    isSpForm := f -> IsSesquilinearForm(f) and IsSymplecticForm(f);

    # if the dimension is not even, the group cannot be symplectic
    if recognise.d mod 2 <> 0 or recognise.isSpContained = false then
        recognise.isSpContained := false;
        return false;
    fi;

    if recognise.isGeneric <> true or
       recognise.isReducible = true or
       recognise.currentgcd <> 2 or
       recognise.isNotPSL <> true  or
       recognise.isNotMathieu <> true or
       recognise.isNotAlternating <> true  then
          return fail;
    fi;



    if recognise.isReducible = "unknown" then
        recognise.needMeataxe := true;
        return NotEnoughInformation;
    fi;

    # if we reach this point the natural module is irreducible
    # since the MeatAxe Method aborts in the reducible case.
    # Also we know that the module is absolutely irreducible,
    # since we are in the generic case.
    if Length(recognise.ClassicalForms)=0 then
        recognise.needForms := true;
        return NotEnoughInformation;
    fi;

    # if the group preserves a symplectic form but not a
    # form we have found Sp
    if recognise.QuadraticForm = false and
        First(recognise.ClassicalForms,isSpForm) <> fail then
        # symplectic form
        recognise.isSpContained := true;
        recognise.isNotExt := true;
        Info(InfoClassical,2,"The group contains Sp(", recognise.d, ", ",
             recognise.q, ");");
        return true;
    else
        recognise.isSpContained := false;
        Info(InfoClassical,2,"The group does not contain Sp(",
             recognise.d, ", ", recognise.q, ");");
        return false;
    fi;
end);


## Main function to test whether group contains SU
BindRecogMethod(FindHomMethodsClassical, "IsSUContained",
"tests whether group contains SU",
function( recognise, grp )
    local f, isHermForm, q0;

    isHermForm := f -> IsSesquilinearForm(f) and IsHermitianForm(f);

    f := recognise.field;

    # if size of field not a square, the group cannot be unitary
    if LogInt(Size(f),Characteristic(f))  mod 2 <> 0 then
        recognise.isSUContained := false;
        return false;
    fi;

    q0 := Characteristic(recognise.field)^
         (LogInt(recognise.q,Characteristic(recognise.field))/2);



    if recognise.isSUContained = false then
        return false;
    fi;

    if recognise.isGeneric <> true or
       recognise.isReducible = true or
       recognise.isNotExt <> true or
       recognise.isNotPSL <> true  or
       recognise.isNotMathieu <> true or
       recognise.isNotAlternating <> true  then
          return fail;
    fi;



    if recognise.isReducible = "unknown" then
        recognise.needMeataxe := true;
        return NotEnoughInformation;
    fi;

    # if we reach this point the natural module is irreducible
    # since the MeatAxe Method aborts in the reducible case.
    # Also we know that the module is absolutely irreducible,
    # since we are in the generic case.
    if Length(recognise.ClassicalForms)=0 then
        recognise.needForms := true;
        return NotEnoughInformation;
    fi;

    if First(recognise.ClassicalForms,isHermForm)<> fail then
        recognise.isSUContained := true;
        Info(InfoClassical,2,"The group contains SU(", recognise.d, ", ",
             q0, ");");
        return true;
    else
        recognise.isSUContained := false;
        Info(InfoClassical,2,"The group does not contain SU(",
             recognise.d, ", ", q0, ");");
        return false;
    fi;
end);


## Main function to test whether group contains SO
BindRecogMethod(FindHomMethodsClassical, "IsSOContained",
"tests whether group contains SO",
function( recognise, grp )
    local f, isParForm, isEllForm, isHypForm;

    isParForm := f -> IsSesquilinearForm(f) and IsParabolicForm(f);
    isEllForm := f -> IsSesquilinearForm(f) and IsEllipticForm(f);
    isHypForm := f -> IsSesquilinearForm(f) and IsHyperbolicForm(f);

    if recognise.isSOContained = false then
        return false;
    fi;


    if IsOddInt(recognise.d) and not IsOddInt(recognise.q) then
        return false;
    fi;

    if recognise.isGeneric <> true or
       not recognise.currentgcd in [1,2] or
       recognise.isNotPSL <> true  or
       recognise.isReducible = true or
       recognise.isNotMathieu <> true or
       recognise.isNotAlternating <> true  then
          return fail;
    fi;


    if recognise.isReducible = "unknown" then
        recognise.needMeataxe := true;
        return NotEnoughInformation;
    fi;

    # if we reach this point the natural module is irreducible
    # since the MeatAxe Method aborts in the reducible case.
    # Also we know that the module is absolutely irreducible,
    # since we are in the generic case.
    if Length(recognise.ClassicalForms)=0 then
        recognise.needForms := true;
        return NotEnoughInformation;
    fi;

    if First(recognise.ClassicalForms,isParForm)<> fail or
        IsQuadraticForm( recognise.QuadraticForm) and
        recognise.QuadraticFormType = "orthogonalcircle" then
        #orthogonal circle
        if recognise.d mod 2 = 0 then
            return false;
        fi;
        if recognise.currentgcd <> 1 then
            return fail;
        fi;
        recognise.isNotExt := true;
        recognise.isSOContained := true;
        Info(InfoClassical,2,"The group contains SO^o(", recognise.d, ", ",
             recognise.q, ");");
        return true;

    elif First(recognise.ClassicalForms,isHypForm) <> fail or
        IsQuadraticForm( recognise.QuadraticForm) and
        recognise.QuadraticFormType = "orthogonalplus" then
        #orthogonal plus
        if recognise.d mod 2 <> 0 then
            return false;
        fi;
        if recognise.currentgcd <> 2 then
            return fail;
        fi;
        recognise.isNotExt := true;
        recognise.isSOContained := true;
        Info(InfoClassical,2,"The group contains SO+(", recognise.d, ", ",
             recognise.q, ");");
        return true;

    elif First(recognise.ClassicalForms,isEllForm) <> fail or
        IsQuadraticForm( recognise.QuadraticForm) and
        recognise.QuadraticFormType = "orthogonalminus" then
        # orthogonal minus
        if recognise.d mod 2 <> 0 then
            return false;
        fi;
        if recognise.currentgcd <> 2 then
            return fail;
        fi;
        recognise.isNotExt := true;
        recognise.isSOContained := true;
        Info(InfoClassical,2,"The group contains SO-(", recognise.d, ", ",
             recognise.q, ");");
        return true;
    else
        recognise.isSOContained := false;
        Info(InfoClassical,2,"The group does not contain SO(",
             recognise.d, ", ", recognise.q, ");");
        return false;
    fi;
end);


# orders: list of observed element orders
# ord: list of required element orders
#
# For all elements n of ord, we must have observed at least one
# element whose order is a multiple of n
HasElementsMultipleOf := function(orders, ord)
    return ForAll(ord, n -> ForAny(orders, i -> i mod n = 0));
end;

############################################################################/
##
##  The following functions deal with the Non-generic cases. See [NP99].
##

############################################################################/
##
##  NonGenericLinear (recognise, grp)  . . . . . . . non-generic linear case
##
##  Recognise non-generic linear matrix groups over finite fields:
##  In order to prove that a group G <= GL( 3, 2^s-1) contains SL, we need to
##  find an element of order a multiple of 4 and a large and basic ppd(3,q;3)-
##  element
##
BindRecogMethod(FindHomMethodsClassical, "NonGenericLinear",
"tests whether group is non-generic Linear",
function( recognise, grp )
    local CheckFlag;

    CheckFlag := function( )
        if recognise.isReducible = "unknown" then
           recognise.needMeataxe := true;
           return fail;
        fi;
        if  Length(recognise.ClassicalForms) = 0 then
            recognise.needForms :=  true;
            return fail;
        fi;
        Info(InfoClassical,2,"The group is not generic");
        Info(InfoClassical,2,"and contains SL(", recognise.d, ", ",
             recognise.q, ");");
        recognise.isSLContained := true;
        return true;
    end;

    if recognise.d > 3 then
        return false;
    fi;
    if recognise.d = 3 and not IsPowerOfTwo(recognise.q+1) then
        return false;
    fi;
    # grp is non-generic if either d = 2 or (d,q) = (3, 2^s-1)

    if recognise.isReducible = true then
       return false;
    fi;

    if Length( recognise.ClassicalForms ) > 0 and
       First(recognise.ClassicalForms,IsTrivialForm) = fail then
       return false;
    fi;

    if recognise.n <= 5 then
        return fail;
    elif recognise.n = 6 then
        recognise.needOrders := true;
        return fail;
    fi;

    if 3 in recognise.LE and 3 in recognise.BE
       and HasElementsMultipleOf(recognise.orders, [4]) then
           return CheckFlag();
    fi;

    return fail;
end);

############################################################################/
##
##  Recognise non-generic symplectic matrix groups over finite fields
##
BindRecogMethod(FindHomMethodsClassical, "NonGenericSymplectic",
"tests whether group is non-generic Symplectic",
function(recognise, grp)
    local d, q, CheckFlag, isSpForm;

    isSpForm := f -> IsSesquilinearForm(f) and IsSymplecticForm(f);

    CheckFlag := function( )
        if recognise.isReducible = "unknown" then
           recognise.needMeataxe := true;
           return fail;
        fi;
        if  Length(recognise.ClassicalForms) = 0 then
            recognise.needForms :=  true;
            return fail;
        fi;
        Info(InfoClassical,2,"The group is not generic");
        Info(InfoClassical,2,"and contains Sp(", recognise.d, ", ",
             recognise.q, ");");
        recognise.isSpContained := true;
        return true;
    end;

    d := recognise.d;
    q := recognise.q;

    if not IsEvenInt(recognise.d) then
        return false;
    fi;

    if recognise.isReducible = true then
       return false;
    fi;

    if Length( recognise.ClassicalForms ) > 0 and
       recognise.QuadraticForm = false and
       First( recognise.ClassicalForms, isSpForm) = fail then
       return false;
    fi;

    if d > 8 then 
        return false;
    fi;

    if recognise.n <= 5 then
        return NotEnoughInformation;
    elif recognise.n <= 6 and d <> 4 then
        recognise.needOrders := true;
        return fail;
    elif d = 4 then
        recognise.needOrders := true;
        recognise.needLB := true;
        recognise.needE2 := true;
    fi;


    if d = 8 and q = 2 then
        if not HasElementsMultipleOf(recognise.orders, [5,9,17]) then
            return fail;
        fi;
    elif d = 6 and q = 2 then
        if not HasElementsMultipleOf(recognise.orders, [5,7,9]) then
            return fail;
        fi;
    elif d = 6 and q = 3 then
        if not HasElementsMultipleOf(recognise.orders, [5,7]) then
            return fail;
        fi;
    elif d = 4 and q = 3 then
        if not HasElementsMultipleOf(recognise.orders, [5,9]) then
            return fail;
        fi;
    elif d = 4 and q = 2 then
        if Size(grp) mod 720 <> 0 then
            Info(InfoClassical,2,"group does not contain Sp(",
                 recognise.d, ", ", recognise.q, ");");
           recognise.isSpContained := false;
           return false;
        fi;
    elif d = 4 and q = 5 then
        if not HasElementsMultipleOf(recognise.orders, [13,15]) then
            return fail;
        fi;
    elif d = 4 and not IsPowerOfTwo(q+1) and not ((q+1) mod 3 = 0 and
                   IsPowerOfTwo((q+1)/3)) and q<>2 then
        if not 4 in recognise.LB then
            return fail;
        fi;
        if not 2 in  recognise.LS then
            return fail;
        fi;
    elif d = 4  and q >= 7 and IsPowerOfTwo(q+1) then
        if not 4 in recognise.LB then
            return fail;
        fi;
        if not HasElementsMultipleOf(recognise.orders, [4]) then
            return fail;
        fi;

    elif d = 4 and q >= 11 and IsPowerOfTwo((q+1)/3) then
        if not HasElementsMultipleOf(recognise.orders, [3,4]) then
            return fail;
        fi;
        if not 4 in recognise.LB then
            return fail;
        fi;
    else
        Info(InfoClassical,2,
             "NonGenericSymplectic: d and q must have been generic");
        return false;
    fi;

    return CheckFlag();

end);

############################################################################/
##
##  Recognise non-generic unitary matrix groups over finite fields
##
BindRecogMethod(FindHomMethodsClassical, "NonGenericUnitary",
"tests whether group is non-generic Unitary",
function(recognise, grp)
    local d, q,  g, f1, f2, o, CheckFlag, isHermForm, str;

    isHermForm := f -> IsSesquilinearForm(f) and IsHermitianForm(f);

    CheckFlag := function( )
        if recognise.isReducible = "unknown" then
           recognise.needMeataxe := true;
           return fail;
        fi;
        if  Length(recognise.ClassicalForms) = 0 then
            recognise.needForms :=  true;
            return fail;
        fi;
         Info(InfoClassical,2,"group contains SU(",
              recognise.d, ", ", recognise.q, ");");
        recognise.isSUContained := true;
        return true;
    end;

    d := recognise.d;
    q := recognise.q;

    if d > 6 then 
        return false;
    fi;

    if recognise.isReducible = true then
       return false;
    fi;

    if Length( recognise.ClassicalForms ) > 0 and
       First( recognise.ClassicalForms, isHermForm )=fail then
       return false;
    fi;

    if recognise.maybeFrobenius = false then
        return false;
    fi;

    if recognise.n <= 5 then
        return NotEnoughInformation;
    elif recognise.n = 6 then
        recognise.needOrders := true;
        if d = 6 or d = 4 then
            recognise.needLB := true;
            recognise.needE2 := true;
        fi;
        if d = 3 then
            recognise.needPOrders := true;
            if q >= 49 then
               recognise.needLB := true;
            fi;
        fi;
        return fail;
    fi;

    if d = 6 and q = 4 then
        if not HasElementsMultipleOf(recognise.orders, [7,10,11]) then
            return fail;
        fi;
    elif d = 6 and q >= 9 then
        if not 3 in recognise.E2 then
            return fail;
        fi;
        if not 5 in recognise.LB then
            return fail;
        fi;
    elif d = 5 and q = 4 then
        if not HasElementsMultipleOf(recognise.orders, [11,12]) then
            return fail;
        fi;
    elif d = 4 and q = 4 then
        #TO DO : check this is same in Magma
        if not HasElementsMultipleOf(recognise.orders, [5,9]) then
            return fail;
        fi;
    elif d = 4 and q = 9 then
        if not HasElementsMultipleOf(recognise.orders, [5,7,9]) then
            return fail;
        fi;
    elif d = 4 and q > 9 then
        if not 3 in recognise.LB then
            return fail;
        fi;
        if not 2 in recognise.E2  then
            return fail;
        fi;
        f1 := Collected(Factors( q^3-1 ));
        f2 := Collected(Factors( q^2-1 ));
        # check if we have a prime at least 11
        if PositionProperty( f1, i-> (i[1] >= 11)) <> fail then
            return CheckFlag();
        fi;
        if PositionProperty( f2, i-> (i[1] >= 11)) <> fail then
            return CheckFlag();
        fi;
        # Now we know that q^3-1 and q^2-1 only contain primes
        # at most 7
        if not q^3 mod 7 = 1 or q^2 mod 7 = 1 or q mod 7 = 1 then
            # 7 is not ppd of q^3-1
            return CheckFlag();
        fi;
        # Now we know 7 is ppd of q^3 -1
        if not q^2 mod 5 = 1 or q mod 5 = 1 then
            # 5 is not ppd of q^2-1
            return CheckFlag();
        fi;
        if ForAny( recognise.orders, i ->
        (i mod 7 = 0 and     # order divisible by 7
         i <> 7 and          # but not equal to 7
         q^3 mod i = 1 and   # order divides q^3-1
        (7*(q-1)) mod i <> 0 # order does not divide 7*(q-1)
         )) then
            # 5 is not ppd of q^2-1
            return CheckFlag();
        fi;
    elif d = 3 and q = 4 then
        if Order(grp) mod 216 = 0 then
            return CheckFlag();
        else
            recognise.isSUContained := false;
            return false;
        fi;
    elif d = 3 and q = 9 then
        if not HasElementsMultipleOf(recognise.orders, [7]) then
            return fail;
        fi;
        if recognise.hasSpecialEle = false then
            if not Order( recognise.g ) mod 6 = 0 then
                return fail;
            fi;
            if ForAny( GeneratorsOfGroup(grp),
                h -> not IsOne(Comm(h,recognise.g^3))) then
                Info( InfoClassical,2,
                      "Cube of element of order div by 6 is not central" );
                      recognise.hasSpecialEle := true;
                return CheckFlag();
             fi;
        else return CheckFlag();
        fi;
    elif d = 3 and q = 16 then
        if not HasElementsMultipleOf(recognise.orders, [5,13]) then
            return fail;
        fi;
        if recognise.hasSpecialEle = false then
            if not Order(recognise.g) mod 5  = 0 then
                return fail;
            fi;
            if ForAny(GeneratorsOfGroup(grp), h -> not IsOne(Comm(h,recognise.g))) then
                Info( InfoClassical,2,
                      "The element of order 5 is not central" );
                recognise.hasSpecialEle := true;
                return CheckFlag();
            fi;
        else return CheckFlag();
        fi;
    elif d = 3 and q = 25 then
        if not HasElementsMultipleOf(recognise.orders, [5,7,8]) then
            return fail;
        fi;
        if recognise.hasSpecialEle = false then
            if Order(recognise.g) mod 8 <> 0 then
                return fail;
            fi;
            g := recognise.g^(Order(recognise.g)/2);
            if ForAny(GeneratorsOfGroup(grp), h -> not IsOne(Comm(h,g))) then
                Info( InfoClassical,2,
                  "involution in cyclic subgroup  of order 8 is not central" );
                recognise.hasSpecialEle := true;
                return CheckFlag();
             fi;
        else return CheckFlag();
        fi;
    elif d = 3 and q >= 49  then
        if not 3 in recognise.LE or not 3 in recognise.BE then
           return fail;
        fi;
        if not recognise.ppd[1] = 3 or not recognise.ppd[2]=true
           or not recognise.ppd[3]=true then
            return fail;
        fi;
        if recognise.hasSpecialEle = false then
             str := "Searching for elements of order > 3 mod scalars";
             str := Concatenation( str,  " and dividing ");
             str := Concatenation( str,  String(q-1) );
             Info(InfoClassical,2, str );
             if not ForAny(recognise.porders, i -> i[1] > 3 and q mod i[1] = 1) then
                 return fail;
             fi;
             recognise.hasSpeccialEle := true;
             return CheckFlag();
         else
             return CheckFlag();
         fi;
    else
        Info(InfoClassical,2,
            "NonGenericUnitary: d and q must have been be generic");
        return false;
    fi;


    return CheckFlag();
end);


BindRecogMethod(FindHomMethodsClassical, "NonGenericOrthogonalPlus",
"tests whether group is non-generic O+",
function(recognise,grp)
    local d, q, gp1, gp2, CheckFlag, pgrp, orbs, isHypForm;

    isHypForm := f -> IsSesquilinearForm(f) and IsHyperbolicForm(f);

    CheckFlag := function( )
        if recognise.isReducible = "unknown" then
           recognise.needMeataxe := true;
           return fail;
        fi;
        if  Length(recognise.ClassicalForms) = 0 then
            recognise.needForms :=  true;
            return fail;
        fi;
        Info(InfoClassical,2,"group contains SO+(",
             recognise.d, ", ", recognise.q, ");");

        recognise.isSOContained := true;
        return true;
    end;

    d := recognise.d;
    q := recognise.q;

    if not d in [4,6,8,10] then
        return false;
    fi;
    if d = 10 and q <> 2 then
        return false;
    fi;

    if recognise.isReducible = true then
       return false;
    fi;

    if (Length( recognise.ClassicalForms ) > 0 and
       First(recognise.ClassicalForms, isHypForm)=fail) and
       (not IsQuadraticForm(recognise.QuadraticForm) or not
       recognise.QuadraticFormType = "orthogonalplus") then
       return false;
    fi;

    if d = 6 or d = 8 then
       recognise.needE2 := true;
       recognise.needLB := true;
    fi;

    if recognise.n <= 5 then
        return NotEnoughInformation;
    elif recognise.n = 6 then
        recognise.needOrders := true;
        return fail;
    fi;

    if d = 10 and q = 2 then
        if not HasElementsMultipleOf( recognise.orders, [17,31])  then
            return fail;
        fi;
    elif d = 8 and q = 2 then
        if not HasElementsMultipleOf( recognise.orders, [7,9,15]) and
           not HasElementsMultipleOf( recognise.orders, [7,10,15]) then
            return fail;
        fi;

        pgrp := ProjectiveActionOnFullSpace( grp, recognise.field, d );
        orbs := Orbits( pgrp, MovedPointsPerms( GeneratorsOfGroup(pgrp)));

        if Set(List(orbs,Length)) <> [ 120, 135 ] then
           recognise.isSOContained := false;
           return false;
        fi;
        if Size(pgrp) mod  174182400 = 0 then
           return CheckFlag();
           recognise.isSOContained := true;
        else
           recognise.isSOContained := false;
           return false;
         fi;
    elif d = 8 and q = 3 then
        if not HasElementsMultipleOf( recognise.orders, [7,13])  then
            return fail;
        fi;
        pgrp := ProjectiveActionOnFullSpace( grp, recognise.field, d );
        orbs := Orbits( pgrp, MovedPointsPerms( GeneratorsOfGroup(pgrp)));
        if Set(List(orbs, Length)) <> [ 1080, 1120] then
             recognise.isSOContained := false;
             return false;
        fi;
        if Size(pgrp) mod 4952179814400 = 0 then
             return CheckFlag();
        else
             recognise.isSOContained := false;
             return false;
        fi;
    elif d = 8 and  q =  5 then
        #ACN Feb 07: added fix - need also elements of order a mult of 3
        #            these are missing in the paper [NP99]
        if not HasElementsMultipleOf( recognise.orders, [7,13,3])  then
            return fail;
        fi;
    elif d = 8 and (q = 4 or q > 5) then
        if not 6 in recognise.LB then
            return fail;
        fi;
        if not 4 in recognise.LS then
            return fail;
        fi;
    elif d = 6 and q = 2 then
        if not HasElementsMultipleOf( recognise.orders, [7]) and
           not HasElementsMultipleOf( recognise.orders, [15]) then
            return fail;
        fi;
    elif d = 6 and q = 3 then
        if not HasElementsMultipleOf( recognise.orders, [5])  then
            return fail;
        fi;
        if not 13 in recognise.orders then
            return fail;
        fi;
    elif d = 6 and q >= 4 then
        if not 4 in recognise.LB then
            return fail;
        fi;
        if not 3 in recognise.E2 then
            return fail;
        fi;
    elif d = 4 and (q = 8 or q >= 11) then
        if recognise.needPlusMinus = false then
            recognise.needPlusMinus := true;
            return NotEnoughInformation;
        fi;
        if not IsSubset(recognise.plusminus,[[1,1],[1,-1],[-1,-1]]) then
            return fail;
        fi;
    elif d = 4 and q = 2 then
        if Size(grp) mod 36 <> 0 then
            recognise.isSOContained := false;
            return false;
        fi;
        if recognise.needDecompose = false then
           recognise.needDecompose := true;
           return fail;
        fi;
        gp1 := Group(recognise.sq1);
        gp2 := Group(recognise.sq2);
        Info(InfoClassical,2,"Group projects to group of order ",
             Size(gp1/recognise.scalars), "x", Size(gp2/recognise.scalars));
        if Size(gp1/recognise.scalars) mod 6 = 0 and
           Size(gp2/recognise.scalars) mod 6 = 0 then
                return CheckFlag();
        fi;
    elif d = 4 and q = 3 then
        if Size(grp) mod 288 <> 0 then
            recognise.isSOContained := false;
            return false;
        fi;
        if recognise.needDecompose = false then
           recognise.needDecompose := true;
           return fail;
        fi;
        gp1 := Group(recognise.sq1);
        gp2 := Group(recognise.sq2);
        Info(InfoClassical,2,"Group projects to group of order ",
             Size(gp1/recognise.scalars), "x", Size(gp2/recognise.scalars));
        if Size(gp1/recognise.scalars) mod 12 = 0 and
           Size(gp2/recognise.scalars) mod 12 = 0 then
                return CheckFlag();
        fi;
    elif d = 4 and q =  4 then
        pgrp := ProjectiveActionOnFullSpace( grp, recognise.field, d );
        orbs := Orbits( pgrp, MovedPointsPerms(
           GeneratorsOfGroup(pgrp)));
        if Size(pgrp) mod 3600 <> 0 then
             recognise.isSOContained := false;
             return false;
        fi;
        if recognise.needDecompose = false then
           recognise.needDecompose := true;
           return fail;
        fi;
        gp1 := Group(recognise.sq1);
        gp2 := Group(recognise.sq2);
        Info(InfoClassical,2,"Group projects to group of order ",
             Size(gp1/recognise.scalars), "x", Size(gp2/recognise.scalars));
        if Size(gp1/recognise.scalars) mod 3 = 0 and
           Size(gp2/recognise.scalars) mod 3 = 0 then
                return CheckFlag();
        fi;
    elif d = 4 and q = 5 then
        pgrp := ProjectiveActionOnFullSpace( grp, recognise.field, d );
        if Size(pgrp) mod 7200 <> 0 then
            recognise.isSOContained := false;
            return false;
        else
            return CheckFlag();
        fi;
    elif d = 4 and q = 7 then
        pgrp := ProjectiveActionOnFullSpace( grp, recognise.field, d );
        if Size(pgrp) mod 56448  <> 0 then
            recognise.isSOContained := false;
            return false;
        fi;
        if recognise.needDecompose = false then
           recognise.needDecompose := true;
           return fail;
        fi;
        gp1 := Group(recognise.sq1);
        gp2 := Group(recognise.sq2);
        Info(InfoClassical,2,"Group projects to group of order ",
             Size(gp1/recognise.scalars), "x", Size(gp2/recognise.scalars));
        if Size(gp1/recognise.scalars) mod 168 = 0 and
           Size(gp2/recognise.scalars) mod 168 = 0 then
                return CheckFlag();
        fi;
    elif d = 4 and q = 9 then
        pgrp := ProjectiveActionOnFullSpace( grp, recognise.field, d );
        if Size(pgrp) mod 259200 <> 0 then
            recognise.isSOContained := false;
            return false;
        else
            return CheckFlag();
        fi;
    else
        Info(InfoClassical, 2,
             "NonGenericO+: d and q must have  been be generic");
        return false;
    fi;

     return CheckFlag();

end);

BindRecogMethod(FindHomMethodsClassical, "NonGenericOrthogonalMinus",
"tests whether group is non-generic O-",
function(recognise, grp)
    local d, q,  orbs, pgrp, h,  g, ppd,  CheckFlag, isEllForm;


    isEllForm := f -> IsSesquilinearForm(f) and IsEllipticForm(f);

    CheckFlag := function( )
        if recognise.isReducible = "unknown" then
           recognise.needMeataxe := true;
           return fail;
        fi;
        if  Length(recognise.ClassicalForms) = 0 then
            recognise.needForms :=  true;
            return fail;
        fi;
        Info(InfoClassical,2,"group contains SO-(",
             recognise.d, ", ", recognise.q, ");");
        recognise.isSOContained := true;
        return true;
    end;

    d := recognise.d;
    q := recognise.q;

    if not d in [4,6,8] then
        return false;
    fi;
    if d = 8 and q <> 2 then
        return false;
    fi;
    if d = 6 and q > 3 then
        return false;
    fi;

    if recognise.isReducible = true then
       return false;
    fi;

    if (Length(recognise.ClassicalForms) > 0 and
       First(recognise.ClassicalForms,isEllForm)=fail) and
       (not IsQuadraticForm(recognise.QuadraticForm) or not
       recognise.QuadraticFormType = "orthogonalminus") then
       return false;
    fi;

    if recognise.n <= 5 then
        return NotEnoughInformation;
    elif recognise.n = 6 then
        recognise.needOrders := true;
        return fail;
    fi;


    if d = 8 and q = 2 then
        if not HasElementsMultipleOf( recognise.orders, [9,17])  then
            return fail;
        fi;
    elif d = 6 and q = 3 then
        if not HasElementsMultipleOf( recognise.orders, [5,7,9])  then
            return fail;
        fi;
    elif d = 6 and q = 2 then
        if not HasElementsMultipleOf( recognise.orders, [5,9])  then
            return fail;
        fi;
    elif d = 4 and q = 2 then
        if not HasElementsMultipleOf( recognise.orders, [3,5])  then
            return fail;
        fi;
    elif d = 4 and q = 3 then
        if not HasElementsMultipleOf( recognise.orders, [3,5])  then
            return fail;
        fi;
        pgrp := ProjectiveActionOnFullSpace( grp, GF(3), 4 );
        orbs := Orbits( pgrp, MovedPointsPerms( GeneratorsOfGroup(pgrp)));
        if Length(orbs) >  3 then # ACN 10/6/08
            recognise.isSOContained := false;
            return false;
         fi;
    elif d = 4 and q >=  4 then
        ppd := IsPpdElement( recognise.field, recognise.cpol, d, q, 1 );
        if ppd = false or ppd[1] <> 4  or ppd[2] <> true then
            return fail;
        fi;
        # found a ppd( 4, q; 4)-element
        g := recognise.g;
        for h in GeneratorsOfGroup(grp) do
# ACN May 2007
            if Comm(h,g) <> One(grp) then
                if Comm(Comm(h,g),g) <> One(grp) then
                        return CheckFlag();
                fi;
            fi;
        od;
        Info(InfoClassical, 2, "grp contained in O-(2,", q,  "^2)" );
        recognise.isNotExt := false;
        recognise.isSOContained := false;
        return false;
    else
      Info(InfoClassical, 2, "NonGenericO-: d and q must be generic" );
        return false;
    fi;

     return CheckFlag();

end);

BindRecogMethod(FindHomMethodsClassical, "NonGenericOrthogonalCircle",
"tests whether group is non-generic Oo",
function( recognise, grp )
    local d, q, g, s, CheckFlag, isParForm;

    isParForm := f -> IsSesquilinearForm(f) and IsParabolicForm(f);

    if not IsOddInt(recognise.d) then
        return false;
    fi;
    if not IsOddInt(recognise.q) then
        return false;
    fi;

    CheckFlag := function( )
        if recognise.isReducible = "unknown" then
           recognise.needMeataxe := true;
           return fail;
        fi;
        if  Length(recognise.ClassicalForms) = 0 then
            recognise.needForms :=  true;
            return fail;
        fi;
        Info(InfoClassical,2,"group contains SOo(",
             recognise.d, ", ", recognise.q, ");");
        recognise.isSOContained := true;
        return true;
    end;

    d := recognise.d;
    q := recognise.q;

    if recognise.isReducible = true then
       return false;
   fi;

    if (Length( recognise.ClassicalForms ) > 0 and
       First(recognise.ClassicalForms, isParForm)=fail) and
       (not IsQuadraticForm(recognise.QuadraticForm) or not
       recognise.QuadraticFormType = "orthogonalcircle") then
       return false;
    fi;


    if recognise.n <= 5 then
        return NotEnoughInformation;
    elif recognise.n = 6 then
        recognise.needOrders := true;
        return fail;
    fi;

    if d = 3 then
        recognise.needLB := true;
    fi;


    if d = 7 and q = 3 then
        if not HasElementsMultipleOf( recognise.orders, [5,7,13])  then
            return fail;
        fi;
    elif d = 5 and q = 3 then
        if not HasElementsMultipleOf( recognise.orders, [5,9])  then
            return fail;
        fi;
    elif d = 5 and q >= 5 then
        if not 4 in recognise.LE then
            return fail;
        fi;
    elif d = 3 and q = 3 then
        if not HasElementsMultipleOf( recognise.orders, [3])  then
            return fail;
        fi;
    elif d = 3 and q = 5 then
        if not HasElementsMultipleOf( recognise.orders, [3,5])  then
            return fail;
        fi;
    elif d = 3 and q = 7 then
        if not HasElementsMultipleOf( recognise.orders, [4,7])  then
            return fail;
        fi;
    elif d = 3 and q = 9 then
        if not HasElementsMultipleOf( recognise.orders, [3,5])  then
            return fail;
        fi;
        if recognise.hasSpecialEle = false then
            if not Order(recognise.g) in [4,8] then
                return fail;
            fi;
            g := recognise.g^2;
            if ForAny(GeneratorsOfGroup(grp), h -> not IsOne(Comm(h,g))) then
               recognise.hasSpecialEle := true;
               return CheckFlag();
            fi;
        else
               return CheckFlag();
        fi;
        recognise.isSOContained := false;
        return false;
    elif d = 3 and q = 11 then
        if not HasElementsMultipleOf( recognise.orders, [3,11])  then
            return fail;
        fi;
    elif d = 3 and q = 19 then
        if not HasElementsMultipleOf( recognise.orders, [5,9,19])  then
            return fail;
        fi;
    elif d = 3 and q >=31 and IsPowerOfTwo(q+1) then
        s := Log2Int(q+1);
        if not ForAny(recognise.orders, i -> i > 2 and (q-1) mod i = 0) then
            return fail;
        fi;
        if not ForAny(recognise.orders, i -> i mod 2^(s-1) = 0) then
            return fail;
        fi;
    elif d = 3 and q>11 and ((q+1) mod 3=0 and
        IsPowerOfTwo((q+1)/3)) then
        s := Log2Int((q+1)/3);
        if not ForAny(recognise.orders, i -> i mod (3*2^(s-1)) = 0) then
            return fail;
        fi;
        if not ForAny(recognise.orders, i -> i > 2 and (q-1) mod i = 0) then
            return fail;
        fi;
    elif d = 3 and ((q+1) mod 3 <> 0 or not IsPowerOfTwo((q+1)/3)) and
                   not IsPowerOfTwo(q+1) then
        if not 2 in recognise.LB then
            return fail;
        fi;
        if not ForAny(recognise.orders, i -> i > 2 and (q-1) mod i = 0) then
            return fail;
        fi;
        ## need to check that the basic lppd( 3,q;2) elements have order
        ## greater than 5.
        s := LogInt(q, recognise.p);
        if not ForAny(recognise.orders, i -> HasLBGgt5(i, recognise.p, s, 2)) then
            return fail;
        fi;
    else
       Info(InfoClassical, 2, "NonGenericOo: d and q must be generic" );
        return false;
    fi;


     return CheckFlag();

end);

########

# 100 Test Random
#
#  50 - 99 Conclusions
#
#  10 - 49 Termination Conditions
#
# 1 - 10 Workers

AddMethod(ClassicalMethDb, FindHomMethodsClassical.TestRandomElement, 100);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.IsGenericParameters, 90);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.IsGeneric, 89);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.IsReducible, 80);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.RuledOutExtField, 81);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.IsNotMathieu, 82);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.IsNotAlternating, 83);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.IsNotPSL, 84);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.NoClassicalForms, 85);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.MeatAxe, 9);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.ClassicalForms, 8);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.NonGenericLinear, 10);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.NonGenericUnitary, 11);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.NonGenericSymplectic, 12);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.NonGenericOrthogonalPlus, 13);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.NonGenericOrthogonalMinus, 14);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.NonGenericOrthogonalCircle, 15);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.IsSLContained, 16);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.IsSpContained, 17);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.IsSUContained, 18);

AddMethod(ClassicalMethDb, FindHomMethodsClassical.IsSOContained, 19);



InstallGlobalFunction( RecogniseClassical,
function( arg )
  local ret, recognise, grp, case, nrrandels, i, f, q, merkinfolevel;

  if Length( arg ) < 1 or Length( arg ) > 3 then
      ErrorNoReturn( "Usage: RecogniseClassical( grp [,nrrandels][,case] )" );
  fi;
  grp := arg[1];
  nrrandels := 30;
  if DimensionOfMatrixGroup(grp) = 8 then
     nrrandels := 200;
  elif DimensionOfMatrixGroup(grp) = 4 and
      Size(FieldOfMatrixGroup(grp)) = 8 then
     nrrandels := 300;
  elif DimensionOfMatrixGroup(grp) <= 10 then
      nrrandels := 50;
  fi;
  case := "unknown";
  for i in [2..Length(arg)] do
      if IsInt(arg[i]) then
          nrrandels := arg[i];
      else
          if arg[i] in ["linear", "symplectic", "unitary",
           "orthogonalplus", "orthogonalcircle", "unknown" ] then
              case := arg[i];
          else
              Info(InfoClassical,2,"Unknown case ",arg[i]," - ignored.");
          fi;
      fi;
  od;

  # init record recognition...
  f := FieldOfMatrixGroup(grp);
  q := Characteristic(f)^DegreeOverPrimeField(f);
  recognise := rec( field :=  f,
                   d := DimensionOfMatrixGroup(grp),
                   p := Characteristic(f),
                   a := DegreeOverPrimeField(f),
                   q := Characteristic(f)^DegreeOverPrimeField(f),
                   E := [], LE := [], BE := [], LB := [],
                   LS := [], E2 := [], LE2 := [], BE2 := [],
                   g := fail,
                   cpol := fail,
                   isppd := fail,
                   n := 0,
                   module := GModuleByMats(GeneratorsOfGroup(grp),f),
                   currentgcd := DimensionOfMatrixGroup(grp),
                   isReducible := "unknown",
                   isGeneric := "unknown",
                   isNotExt  := "unknown",
                   hint := case,
                   hintIsWrong := false,
                   isNotMathieu := "unknown",
                   isNotAlternating := "unknown",
                   isNotPSL := "unknown",
                   possibleNearlySimple := [],
                   dimsReducible := [],
                   orders := [],
                   porders := [],
                   hasSpecialEle := false,
                   bc := "unknown",
                   kf := "unknown",
                   plusminus := Set([]),
                   sq1 := [Z(q)*One(GL(2,q))],
                   sq2 := [Z(q)*One(GL(2,q))],
                   scalars := Group(Z(q)*One(GL(2,q))),
                   needMeataxe := false,
                   needForms := true, # changed 29.10.09
                   needOrders := false,
                   needPOrders := false,
                   needBaseChange := false,
                   needKF := false,
                   needPlusMinus := false,
                   needDecompose := false,
                   needLB := false,
                   needE2 := false,
                   maybeDual := true,
                   maybeFrobenius := (LogInt(Size(f),Characteristic(f)) mod 2=0),
                   ClassicalForms := [],
                   QuadraticForm := false,
                   QuadraticFormType := "unknown",
                   isSLContained := "unknown",
                   isSpContained := "unknown",
                   isSUContained := "unknown",
                   isSOContained := "unknown",
                  );
  merkinfolevel := InfoLevel(InfoMethSel);
  SetInfoLevel(InfoMethSel,0);
  CallMethods( ClassicalMethDb, nrrandels, recognise, grp );
  SetInfoLevel(InfoMethSel,merkinfolevel);
  # fail: bedeutet, dass entnervt aufgegeben wurde
  # true: bedeutet, dass eine Methode "erfolgreich" war

  return recognise;
  # return result
end);

# The following function pretty prints the output of RecogniseClassical.
# This can be helpful when debugging it.
DisplayRecog := function( r )

    local q0;

           Print("Reducible : ", r.isReducible, "\n" );
           Print("Forms: " );
           if Length(r.ClassicalForms)<> 1 then
              Print("Several Forms preserved\n");
           elif IsTrivialForm( r.ClassicalForms[1] ) then
              Print("linear i.e. no forms\n");
           elif IsQuadraticForm(r.QuadraticForm) then
              Print("quadratic form of type: ", r.QuadraticFormType, "\n");
           elif IsSymplecticForm(r.ClassicalForms[1]) then
              Print("symplectic\n");
           elif IsHermitianForm( r.ClassicalForms[1] ) then
              Print("unitary\n");
           elif IsEllipticForm( r.ClassicalForms[1] ) then
              Print("orthogonal minus\n");
           elif IsParabolicForm( r.ClassicalForms[1] ) then
              Print("orthogonal circle\n");
           elif IsHyperbolicForm( r.ClassicalForms[1] ) then
              Print("orthogonal plus\n");
           fi;
           if Length(r.E) > 0 then
               Print("E : ", r.E, "\n" );
           fi;
           if Length(r.LE) > 0 then
               Print("LE : ", r.LE, "\n" );
           fi;
           if Length(r.BE) > 0 then
               Print("BE : ", r.BE, "\n" );
           fi;
           if Length(r.LS) > 0 then
               Print("LS : ", r.LS, "\n" );
           fi;
           if Length(r.LB) > 0 then
               Print("LB : ", r.LB, "\n" );
           fi;
           if Length(r.E2) > 0 then
               Print("E2 : ", r.E2, "\n" );
           fi;
           if Length(r.LE2) > 0 then
               Print("LE2 : ", r.LE2, "\n" );
           fi;
           if Length(r.BE2) > 0 then
               Print("BE2 : ", r.BE2, "\n" );
           fi;
           if r.isNotMathieu <> "unknown" then
               Print( "Mathieu ruled out: ", r.isNotMathieu, "\n");
           fi;
           if r.isNotAlternating <> "unknown" then
               Print( "An ruled out: ", r.isNotAlternating, "\n");
           fi;
           if r.isNotPSL <> "unknown" then
               Print( "PSL ruled out: ", r.isNotPSL, "\n");
           fi;
#           if Length(r.dimsReducible) > 0 then
#               Print( "dimsred ", r.dimsReducible, "\n");
#           fi;

           if Length(r.orders) > 0 then
               Print( "orders ", r.orders, "\n");
           fi;
           if Length(r.porders) > 0 then
               Print( "porders ", r.porders, "\n");
           fi;

            if r.isSLContained = true then
                Print("--------> contains SL(", r.d, ",", r.q, ")\n");
            fi;

            if r.isSpContained = true then
                Print("--------> contains Sp(", r.d, ",", r.q, ")\n");
            fi;


            if r.isSUContained = true then
                q0 := Characteristic(r.field)^
               (LogInt(r.q,Characteristic(r.field))/2);
                Print("--------> contains SU(", r.d, ",", q0, ")\n");
            fi;

            if r.isSOContained = true then
                Print("--------> contains SO(", r.d, ",", r.q, ")\n");
            fi;

            if r.isReducible = true then
                Print("--------> reducible + not classical \n");
            fi;

end;
