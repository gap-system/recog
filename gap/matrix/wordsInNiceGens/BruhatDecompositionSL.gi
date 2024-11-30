######################################
# BruhatDecompositionSL.gi
######################################

######################################
# Concept:
#    This implementation follows the ideas of
#    "Straight-line programs with memory and matrix Bruhat decomposition"
#    by Alice Niemeyer, Tomasz Popiel & Cheryl Praeger.
#    In the following all references will mean this paper
#    and in case we differ from this paper (due to readability or bug-fixing)
#    this will also be remarked.
#
#    Let g \in SL(d,p^f)
#    Bruhat Decomposition computes g = u1 * w * u2, where
#         - u1,u2 are lower triangular matrices
#         - w is monomial matrix
#
#    In this algorithm we want to compute the Bruhat-Decomposition of g
#    and give g (respectively u1,w and u2) as word in the so called
#    "LGO standard generators" (Section 3.1).
#
#    1) While computing u1 (resp u2) with some kind of Gauß-Algorithm,
#    we express the matrices as product of so called transvections
#    - For 1 <= j < i <= d: t_{i,j}(\alpha) is the matrix T with
#        1-entries on diagonal, T_i,j = \alpha, 0 elsewhere
#    Each t_{i,j}(\alpha) can be computed from t_{2,1}(\alpha) via recursion,
#    where we have to distinguish the odd and even dimensons (p12 Lemma 4.2).
#    This again can be expressed as a product of t_{2,1}(omega^\ell)
#    (where omega is a primitive element and 0 <= ell < f).
#    The transvections as words in the standard generators are described in
#    (p12 Lemma 4.2).
#    This yields a decomposition of u1 and u2 in standard generators.
#
#    2) In a further step we will decompose the monomial Matrix w in
#    a signed permutation matrix p_sign and a diagonal Matrix diag.
#    ( How to associate p_sign with a product of generators is
#    further described in (PART I b) and (PART III) )
#
#    3) The last step is the decomposition of the diagonal Matrix in 2)
#    as word in the standard generators.
#
#    We won't do this matrix multiplications directly, but write them
#    in a list to evaluate in a StraightLineProgram. (Section 2)
#    Although described differently in the paper, we sometimes will allow
#    instructions to multiply more than two elements (eg during conjugating).
#    This doesn't affect the optimality of an slp much, but higly increases
#    the readability of our implementation.
######################################



####################
# PART I - a)
#    Originally implemented subfunctions
####################

InfoBruhat := NewInfoClass("InfoBruhat");;
SetInfoLevel( InfoBruhat, 2 );
#####
# MakeSLP()
#####

# To increase readability, the lists slp as defined later
# (see Unipotent-, Diagonal-, BruhatDecomposition and PermSLP)
# start with [1,1],[2,1],.. [5,1]. However this represents the LGO standard-
# generators and is the input of our straight-line program.
# Defining and SLP we thus have to exclude this instructions from our list.

# Input: slp: A list of instructions for a straight-line program
#            genlen: The number of inputs for our SLP
#                        (ie the number of generators )

# Output: An SLP using the instructions of slp and genlen inputs

#
# BruhatDecomposition: Computes the Bruhat Decomposition of matrices of the classical groups.
#
# Implementations
#

InstallGlobalFunction(  MakeSLP,
 function( slp, genlen )

    return StraightLineProgram( slp{[ genlen+1 .. Length(slp) ]}, genlen );

end
);


InstallGlobalFunction(  MakeSLPNC,
function( slp, genlen )

    return StraightLineProgramNC( slp{[ genlen+1 .. Length(slp) ]}, genlen );

end
);



#####
# CoefficientsPrimitiveElement()
#####

# The following function has been written by Thomas Breuer.
# It expresses an element alpha in a field fld as
# a linear combination of a Primitive Element.

# Input: fld: A field,
#        alpha : An element of fld

# Output: Coefficients: A vector c sth for omega primitive element
#            alpha = sum c[i] omega^(i-1)

InstallGlobalFunction(  CoefficientsPrimitiveElement,
function ( fld, alpha )

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

end
);


#####
# MyPermutationMat()
#####

# Given a permutation an integer d > 0 and a field fld, this function computes
# the permutation matrix P in M_{d x d}(fld).

# Input:
#    perm:    A permutation
#    dim:     A natural number
#    fld:     A field

# Output: res: The permutation matrix of perm over M_{d x d}(fld)
#                 (ie res_{i,j} = One(fld) if i^perm = j)

InstallGlobalFunction(  MyPermutationMat,
function(perm, dim, fld)

    local res;

    res := PermutationMat(perm, dim) * One(fld);
    ConvertToMatrixRep(res);

    return res;

end
);


InstallGlobalFunction(  MyPermutationMatNC,
function(perm, dim, fld)

    local res;

    res := PermutationMat( perm, dim ) * One( fld );
    ConvertToMatrixRepNC(res);

    return res;

end
);



#####
# LGOStandardGensSL
#####

# This function computes the standard generators of SL
# as given by C. R. Leedham-Green and E. A. O'Brien in
# "Constructive Recognition of Classical Groups  in odd characteristic"
# (This matrices can also be found in the paper ch 3.1 ps 6-7)

# Input:
#    d: the dimension of our matrix
#    q: A prime power q = p^f, where F_q ist the field whereover the matrices
#        are defined

# Output: stdgens the LGO standard-generators of SL(d,q)

InstallGlobalFunction(  LGOStandardGensSL,
function( d, q )

    local t, w, s, x, v, i, delta, fld;

    fld := GF(q);

    if d < 3 then
        Error("LGOStandardGens: d has to be at least 3\n");
        return;
    fi;

    # t: The transvection
    t := IdentityMat( d, fld );
    t[1][2] := One(fld);

    # delta: The diagonal matrix
    delta := IdentityMat(d,fld);
    delta[1][1] := PrimitiveRoot(fld);
    delta[2][2] := PrimitiveRoot(fld)^-1;

    # s: The transposition
    s := IdentityMat( d, fld );
    s{[1..2]}{[1..2]} :=  MyPermutationMat( (1,2), 2, fld );
    s[2][1] := - s[2][1];


    # x: The 4-cycle (resp identity if d odd)
    if IsEvenInt(d) then
        x := MyPermutationMat( (1,2,3,4), d, fld );
        x[4][1] := - x[4][1];
    else
        x := IdentityMat(d,fld);
    fi;

    # v: The cycle
    if IsEvenInt(d) then
        if d = 2 then
            v := ();
        else
            v := (1,3)(2,4);
            for i in [5,7 .. d-1] do
                v := v * (1,i)(2,i+1);
            od;
        fi;
        v := MyPermutationMat( v, d, fld );

    else
        v :=  0* IdentityMat(d,fld);
        v[1][d] := One(fld);
        v{[ 2..d ]}{[ 1..d-1 ]} := - IdentityMat( d-1 , fld );
    fi;

    return [ s, t, delta, v, x ];

end
);


InstallGlobalFunction(  LGOStandardGensSLNC,
function( d, q )

    local s, t, delta, v, x, i, fld;

    fld := GF(q);


    # s: The transposition
    s := IdentityMat( d, fld );
    s{[ 1..2 ]}{[ 1..2 ]} :=  MyPermutationMatNC( (1,2), 2, fld );
    s[2][1] := - s[2][1];


    # t: The transvection
    t := IdentityMat( d, fld );
    t[1][2] := One(fld);


    # delta: The diagonal matrix
    delta := IdentityMat(d,fld);
    delta[1][1] := PrimitiveElement(fld);
    delta[2][2] := PrimitiveElement(fld)^-1;


    # v: The cycle
    if IsEvenInt(d) then
        if d = 2 then
            v := ();
        else
            v := (1,3)(2,4);
            for i in [ 5,7 .. d-1 ] do
                v := v * (1,i)(2,i+1);
            od;
        fi;
        v := MyPermutationMatNC( v, d, fld );

    else
        v :=  0* IdentityMat(d,fld);
        v[1][d] := One(fld);
        v{[ 2..d ]}{[ 1..d-1 ]} := - IdentityMat( d-1 , fld );
    fi;


    # x: The 4-cycle (resp identity if d odd)
    if IsEvenInt(d) then
        x := MyPermutationMatNC( (1,2,3,4), d, fld );
        x[4][1] := - x[4][1];
    else
        x := IdentityMat(d,fld);
    fi;


    return [ s, t, delta, v, x ];

end
);




####################
# PART I - b)
#    Additionally implemented subfunctions
####################

#####
# HighestSlotOfSLP()
#####

# We can't use Length(slp) as done in the original code to determine which
# slots are already used, because not every entry of slp creates a new slot
# while others may increase the highest slot used by more than one.
# (After explicitly writing in a slot j>N, the SLP continues creating slots
#    j+1,j+2,.. if no slot is explicitly given.)

# The following function determines the highest slot a SLP
# constructed from the list slp will write in.

# Input: slp: A list of instructions satisfying the properties for an SLP

# Output: highestslot: The number of slots this SLP will need if evaluated

InstallGlobalFunction(  HighestSlotOfSLP,
function(slp)

    local len, i, highestslot;

    len := Length(slp);
    highestslot := 0;

    for i in [ 1..len ] do

        if IsList( slp[i][1] ) and not IsList( slp[i][2] ) then
            # ie slp[i] = [list,i], thus will write in i.
            highestslot := Maximum( highestslot, slp[i][2] );
        elif not IsList( slp[i][1] ) then
            # ie slp[i] = list, thus creates new highest slot
            highestslot := highestslot + 1;
        else
            # ie slp[i] = [list_1,..list_n], thus the end of slp
            # and only shows slots
        fi;
    od;

    return highestslot;

end
);


#####
# MatToWreathProd() and WreathProdToMat()
#####

# In PermSLP we want to transform the monomial matrix w given by
# UnipotentDecomposition() into a diagonal matrix.
#    (The exact procedure is described in PermSLP)
# Since multiplying the LGO standard-generators s,v and x not only involves
# permutations but we also have to consider which non-zero entries are +1 and
# which -1, we want to associate this matrices with permutations on 2d points.
# (cf Wreath-Product)

# < s,v,x > -> Sym(2d), M -> Mwr where
# i^Mwr =  j  and (i+d)^Mwr= j+d if M_i,j = 1        and
# i^Mwr = j+d and (i+d)^Mwr=  j  if M_i,j = -1
# for 1<=i<=d

# Due to their relation to wreath-products, we will call denote the image
# of a matrix M \in < s,v,x > by Mwr

# Input: M: A monomial matrix with only +1 and -1 entries

# Output: perm: the permutation Mwr

InstallGlobalFunction(  MatToWreathProd,
function( M )

    local zero, d, found, perm, perm2, diag, r, j;

    zero := Zero( M[1][1] );
    d := DimensionsMat(M);
    if d[1] <> d[2] then Error("Matrix must be square"); return; fi;
    d := d[1];

    found:= BlistList( [1..d], [] );
    perm := [];
    diag := [];

    for r  in [1..d]  do
        j := PositionNot( M[r], zero );
        if d < j or found[j]  then return false;  fi;
        diag[r] := M[r][j];
        if PositionNot( M[r], zero, j ) <= d  then
            return false;
        fi;
        found[j] := true;
        if M[r][j] = One(M[1][1]) then
            perm[ r ]  := j;
            perm[ r+d ]  := j+d;
        elif M[r][j] = -One(M[1][1]) then
            perm[ r ]  := j+d;
            perm[ r+d ]  := j;
        fi;
    od;

    perm := PermList(perm);

    return perm;
end
);


InstallGlobalFunction(  MatToWreathProdNC,
function( M )

    local zero, d, found, perm, perm2, diag, r, j;

    zero := Zero( M[1][1] );
    d := Length( M );

    found:= BlistList( [1..d], [] );
    perm := [];
    diag := [];

    for r  in [ 1..d ]  do
        j := PositionNot( M[r], zero );
        if d < j or found[j]  then return false;  fi;
        diag[r] := M[r][j];
        if PositionNot( M[r], zero, j ) <= d  then
            return false;
        fi;
        found[j] := true;
        if M[r][j] = One(M[1][1]) then
            perm[ r ]  := j;
            perm[ r+d ]  := j+d;
        elif M[r][j] = -One(M[1][1]) then
            perm[ r ]  := j+d;
            perm[ r+d ]  := j;
        fi;
    od;

    perm := PermList(perm);

    return perm;
end
);



# In fact the association above is an isomorphism and we can associate to each
# permutation we compute during PermSLP a unique monomial matrix whose non-zero
# entries are +1 or -1.

# M_i,j = 1  if i^Mwr =  j <= d        and
# M_i,j = -1 if i^Mwr = j+d

# Input:    perm: A permutation in Sym(2d) sth. {{i,i+d}}_1<=i<=d are blocks
#            dim: The dimension of the matrix we want perm send to
#            fld: The field whereover the matrix is defined.

# Output:    res: The Matrix M satisfying the above properties

InstallGlobalFunction(  WreathProdToMat,
function( perm, dim, fld )

    local res,sign,r,one,tmp;

    one := One(fld);
    sign := [];
    tmp := [];

    for r in [1..dim] do

        if r^perm <= dim then

            sign[ r ] := one;
            tmp[ r ] := r^perm;

        else

            sign[ r ] := - one;
            tmp[ r ] := r^perm - dim;

        fi;

    od;

    perm := PermList(tmp);
    res := PermutationMat( perm, dim ) * one;

    for r in [ 1..dim ] do
        res[ r ][ r^perm ]:= sign[ r ];
    od;

    ConvertToMatrixRep( res );

    return res;

end
);

#####
# AEM (Ancient Egytian Multiplication)
#####

# At several occasions we will need to compute a high power of some value
# saved in a memory slot. For this purpose there is a variaton of AEM
# implemented below.

# Input:     spos: The memory slot, where a value b is saved in
#             respos:    The memory slot we want the exponentation to be written in
#            tmppos: A memory slot for temporary results
#            k:        An integer.

# Output:    instr: Lines of an SLP that will (when evaluated) take the value b
#            saved in spos and write b^k in respos

# Remarks:     tmpos and respos must differ.
#            If spos = respos or spos =  tmpos it will be overwritten.

InstallGlobalFunction(  AEM,
function(spos,respos,tmppos,k)

    local instr,i;

    instr:=[];
    instr[1] := [ [spos,0], respos ];
    instr[2] := [ [spos,1], tmppos ];
    i:=3;

    if k < 0 then
        instr[2] := [ [spos,-1], tmppos ];
        k:=-k;
    fi;

    while k > 0 do

        if IsOddInt(k) then
            instr[i] := [ [respos,1,tmppos,1], respos ];
            i := i + 1;
        fi;

        instr[i] := [ [tmppos,2], tmppos ];
        k := QuoInt( k, 2 );
        i := i + 1;
    od;

    return instr;

end
);

#####
# TestIfMonomial()
#####

# Tests if a given matrix M is monomial matrix
# there is function in GAP, however it does not seem to work for SL(d,q).

# Input: M: A Matrix

# Output: true if M is Monomial, false else

InstallGlobalFunction(  TestIfMonomial,
function( M )

    local zero, d, found, r, j;

    zero := Zero( M[1][1] );
    d := DimensionsMat(M);

    if d[1] <> d[2] then
        return false;
    fi;

    d := d[1];
    found:= BlistList( [1..d], [] );

    for r  in [ 1..d ] do

        j := PositionNot( M[r], zero );

        if d < j or found[j]  then
            return false;
        fi;

        if PositionNot( M[r], zero, j ) <= d  then
            return false;
        fi;

        found[j] := true;

    od;

    return true;

end
);


InstallGlobalFunction(  TestIfMonomialNC,
function( M )

    local zero, d, found, r, j;

    zero := Zero( M[1][1] );
    d := Length( M );

    found:= BlistList( [1..d], [] );

    for r  in [ 1..d ] do

        j := PositionNot( M[r], zero );

        if d < j or found[j]  then
            return false;
        fi;

        if PositionNot( M[r], zero, j ) <= d  then
            return false;
        fi;

        found[j] := true;

    od;

    return true;

end
);



####################
# PART II - a)
#    UnipotentDecomposition and Transvections
####################

#####
# Transvections2()
#####

#  Let stdgens be the list of standard generators for SL(d,p^f)
#  and let omega be a primitive element of G(p^f).
#  This function computes T_2 := { t21(omega^ell) | 0 <= ell <= f-1 }
#  Record what we do in slp

# This function coincides with eq (6) p12

# Input: stdgens: The LGO standard-generators of SL(d,q)
#            omega: A primitive element of GF(q)
#            slp: A list of instructions
#            pos: A list of numbers, denoting where to save the transvections
#                    t_{2,1}(omega^ell)  0 <= ell < f

# Output: slp: The list of instruction with additional instructions writing
#                    t_{2,1}(\omega^ell) in Slot pos[l+1] 0 <= ell < f.

InstallGlobalFunction(  Transvections2,
function( stdgens, omega, slp, pos )

    local ell, f, fld;

    fld := DefaultField( omega );
    f := LogInt( Size(fld), Characteristic(fld) );

    for ell in [0..f-1] do

        if IsOddInt( Length( stdgens[1] ) ) then
            #del^-1*v*del^v*v^-1 (see p12 (6))
            Add(slp, [ [8,ell, 4,1, 8,ell, 9,1 ], pos[ell+1] ] );
        else
            #del^-ell*x^-1*del^-ell*x (see p12 (6))
            Add(slp, [ [8,ell, 10,1, 8,ell,5,1], pos[ell+1] ] );
        fi;

        #t_{2,1}*s*t^-1*s^-1*t_{2,1}^-1
        Add(slp,[ [pos[ell+1],1, 1,1, 7,1, 6,1, pos[ell+1],-1 ],
                    pos[ell+1] ] );
    od;

    return slp;

end
);

#####
# UnipotentDecomposition()
#####
# Computes the Unitriangular decomposition of the matrix g

# Input:
#    stdgens: The LGO standard-generators
#    g:    a matrix in SL(d,q)

# Output: slp: A list of instructions yielding u1,u2 if evaluated as SLP
#        [u1,g,u2]: The matrices of Bruhat-Decomposition

InstallGlobalFunction(  UnipotentDecomposition,
function( arg )

    local    stdgens, c, r, i, j, a, z, d, f, ell, fld, u1, u2, g, slp, instr,
            tmppos, AEMrespos, vxpos, vxipos, u1pos, u2pos, tvpos,
            tir1pos, tirzpos, tcj1pos, tcjzpos, T2pos, Tipos, Ti_1pos,
            TransvecAtAlpha, ShiftTransvections, FastShiftTransvections,
            BackShiftTransvections, FastBackShiftTransvections;

#    ###############
#    Local Functions
#    ###############

#    The following five functions are local as they have side effects.
#    In particular, they modify the global variables T_i and Ti_1

    #####
    # TransvectionAtAlpha()
    #####

    # Let alpha in GF(p^f), alpha = Sum a_l omega^l, omega a primitive element
    # Let slp be the list of instructions in UnipotentDecomposition and Tipos
    # denote the slots where transvections t_{i,j}(omega^ell) 0 <= ell < f
    # are saved. This function computes
    # t_{i,j}(alpha) = product t_{i,j}(omega^ell)^{a_ell}  (see Lemma 4.2)
    # where the exponents a_ell are given by CoefficientsPrimitiveElement.
    # (For Definition of Transvections see paper p11)

    TransvecAtAlpha := function( alpha )

        local cc, ell, instr;

        # if omega = 1 then we overwrite the position for tv with Ti(1)
        if IsOne( alpha ) then
            Add(slp, [ [ Tipos[1], 1 ], tvpos ] );
            return;
        fi;

        cc := CoefficientsPrimitiveElement( fld, alpha );
        instr := [];

        for ell in [ 1..Length(cc) ] do

            if not IsZero( cc[ell] ) then
                Append( instr, [ Tipos[ell], Int(cc[ell]) ] );
            fi;
        od;

        if Length( instr ) = 0 then
            Error("TransvecAtAlpha: this should not happen");
        fi;

        Add( slp, [ instr,tvpos ] );

        return;

    end;


    #####
    # ShiftTransvections()
    #####

    # Let Ti be the set of transvections { t_{i(i-1)}(omega^ell) }
    # and Ti_1 the set of transvections { t_{(i-1)(i-2)}(omega^ell) }.

    # ShiftTransvections computes { t_{i+1,i}(omega^ell) } for given
    # Ti and Ti_1 (This coincides with eq(8) p12)
    # stores them in the variable Ti and stores
    # the transvections  { t_{i,i-1}(omega^ell) } in the variable Ti_1.

    # This corresponds to ( eq (7+8) p12 )

    ShiftTransvections := function(i)

        local ell;

        # For i = 2: Ti=T2.
        if i <= 2 then return; fi;

        if IsOddInt(d) then
            # If d is Odd: Conjugate the last Ti (eq (8))
            for ell in [ 1..f ] do
                Add( slp, [ [ 4,1, Tipos[ell],1, 9,1], Tipos[ell] ] );
            od;
        else
            if i = 3 then
                # Compute T3 differently (eq (7))
                for ell in [ 1..f ] do
                    # Copy what is in Ti into Ti_1
                    Add(slp, [ [Tipos[ell],1 ], Ti_1pos[ell] ] );
                    # Write the new instruction to compute Ti
                    Add( slp, [ [ vxipos,1, Tipos[ell],1, vxpos,1],
                                Tipos[ell]    ] );
                od;
            else
                # If d is Even: Conjugate the 2nd last Ti (eq (8))
                for ell in [ 1..f ] do
                    # Copy the instruction in Ti into tmp position,
                    Add(slp,[ [ Tipos[ell], 1 ], tmppos ] );
                    # conjugate Ti_1 by v and write into Tipos
                    Add( slp, [ [ 9,1, Ti_1pos[ell],1, 4,1], Tipos[ell] ] );
                    Add(slp, [ [tmppos,1], Ti_1pos[ell] ] );
                od;
            fi;
        fi;
    end;


    #####
    # FastShiftTransvections()
    #####

    # Given t_2,1 we compute t_{i,i-1} using fast exponentation.
    # This algorithm will be called in each step of the main loop and
    # is more efficient than calling ShiftTransvections (r-2) times.

    FastShiftTransvections := function(i)

        local ell;

        # For i = 2: Ti=T2.
        if i <= 2 then return; fi;

        if IsOddInt(d) then

            instr := AEM( 4, AEMrespos, tmppos, i-2 );
            Append( slp, instr );

            # If d is Odd: Conjugate the last Ti (eq (8))
            for ell in [ 1..f ] do
                Add( slp, [ [ AEMrespos,1, Tipos[ell],1, AEMrespos,-1 ],
                            Tipos[ell] ] );
            od;
        else
            if i = 3 then
                # Compute T3 differently (eq (7))
                for ell in [ 1..f ] do
                    # Copy what is in Ti into Ti_1
                    Add(slp, [ [Tipos[ell],1], Ti_1pos[ell] ] );
                    # Write the new instruction to compute Ti
                    Add( slp, [ [ vxipos,1, Tipos[ell],1, vxpos,1],
                                Tipos[ell]    ] );
                od;
            elif IsOddInt(i) then

                #T_i = v^-(i-3)/2*T_3*v^(i-3)/2
                #T_i-1=v^-(i-3)/2*T_2*v^(i-3)/2

                #Set T3 and T2 in Position
                for ell in [ 1..f ] do
                    # Copy what is in Ti into Ti_1
                    Add(slp, [[Tipos[ell],1],Ti_1pos[ell]] );
                    # Write the new instruction to compute Ti
                    Add( slp, [ [ vxipos,1, Tipos[ell],1, vxpos,1],
                                Tipos[ell]    ] );
                od;

                instr := AEM(4,AEMrespos,tmppos,(i-3)/2);
                Append( slp, instr );
                # now AEMrespos knows v^(i-3)/2

                for ell in [ 1..f ] do

                    Add( slp, [ [ AEMrespos,-1, Tipos[ell],1, AEMrespos,1],
                                        Tipos[ell]    ] );

                    Add( slp, [ [ AEMrespos,-1, Ti_1pos[ell],1, AEMrespos,1],
                                        Ti_1pos[ell]  ] );
                od;

            else

                #T_i = v^-(i-2)/2*T_2*v^(i-2)/2
                #T_i-1=v* v^-(i-2)/2*T_3*v^(i-2)/2* v^-1
                #So save t_3 in Ti_1pos
                for ell in [ 1..f ] do
                    Add( slp, [ [ vxipos,1, Tipos[ell],1, vxpos,1],
                                Ti_1pos[ell]    ] );
                od;

                # and compute v^(i-2)/2
                instr := AEM(4,AEMrespos,tmppos,(i-2)/2);
                Append( slp, instr );

                for ell in [ 1..f ] do
                    Add( slp, [ [ AEMrespos,-1, Tipos[ell],1, AEMrespos,1],
                                    Tipos[ell] ] );

                    Add( slp, [ [ AEMrespos,-1, Ti_1pos[ell],1, AEMrespos,1],
                                    Ti_1pos[ell] ] );

                    Add( slp, [ [ 4,1, Ti_1pos[ell],1, 9,1], Ti_1pos[ell] ] );
                od;
            fi;
        fi;

    end;

    #####
    # BackShiftTransvections()
    #####

    # This function is very similar to ShiftTransvections,
    # except it works in the reverse order, namely
    # BackShiftTransvections computes t{(i+1)i}
    # given t_{(i+2)i} and t_{(i+3)(i+2)}

    BackShiftTransvections := function(i)

        local ell;

        if IsOddInt(d) then
            # for odd d we have to conjugate the previous Ti by v
            for ell in [ 1..f ] do
                Add(slp, [[ 9,1, Tipos[ell],1, 4,1], Tipos[ell]]);
            od;
        else
            if i = 1 then
                # We compute T3 differently
                for ell in [ 1..f ] do

                    Add( slp, [ [Tipos[ell],1], tmppos ] );
                    # write the new instruction to compute Ti
                    Add( slp, [ [ vxpos,1, Tipos[ell],1, vxipos,1],
                                Tipos[ell] ] );
                    # copy what is in tmppos into Ti_1
                    Add(slp, [[tmppos,1],Ti_1pos[ell]] );
                od;
            else
                # for even d we have to conjugate the 2nd last Ti
                for ell in [ 1..f ] do

                    # copy the instruction in Ti into the tmp position
                    Add(slp,[[Tipos[ell],1], tmppos]);
                    # now conjugate T_{i+1} by v and write into Tipos
                    Add( slp, [ [ 4,1, Ti_1pos[ell],1, 9,1],
                                Tipos[ell] ] );

                    Add( slp, [ [tmppos,1], Ti_1pos[ell] ] );
                od;
             fi;
        fi;
    end;

    #####
    # FastBackShiftTransvections()
    #####

    # As for ShiftTransvections, we need an efficient way to compute
    # BackShiftTransvections multiple times in a row.

    FastBackShiftTransvections := function(i)

        local ell;

        if IsOddInt( d ) then

            instr := AEM( 4, AEMrespos, tmppos, i - d + 1 );
            Append( slp, instr );

            # If d is Odd: Conjugate the last Ti (eq (8))
            for ell in [ 1..f ] do

                Add( slp, [ [ AEMrespos,1, Tipos[ell],1, AEMrespos,-1 ],
                                Tipos[ell] ] );
            od;
        else
            # The case i = 1 cant occur in our implementation
            if IsOddInt(i) then

                instr := AEM( 4, AEMrespos, tmppos, (i-d+1)/2 );
                Append( slp, instr );

                for ell in [ 1..f ] do

                    Add( slp, [ [ AEMrespos,-1, Tipos[ell],1, AEMrespos,1],
                                    Tipos[ell] ] );

                    Add( slp, [ [ AEMrespos,-1, Ti_1pos[ell],1, AEMrespos,1],
                                    Ti_1pos[ell] ] );
                od;
            else
                for ell in [ 1..f ] do

                    Add( slp, [ [ Tipos[ell],1 ], tmppos ] );
                    Add( slp, [ [ Ti_1pos[ell],1], Tipos[ell] ] );
                    Add(slp,[ [ tmppos,1 ], Ti_1pos[ell] ] );
                od;

                instr := AEM( 4, AEMrespos, tmppos, (d-c)/2 );
                Append( slp, instr );

                for ell in [ 1..f ] do
                    Add( slp, [ [ AEMrespos,1, Tipos[ell],1, AEMrespos,-1],
                                    Tipos[ell] ] );

                    Add( slp, [ [ AEMrespos,1, Ti_1pos[ell],1, AEMrespos,-1],
                                    Ti_1pos[ell]         ] );

                    Add( slp, [ [ 9,1, Ti_1pos[ell],1, 4,1], Ti_1pos[ell] ] );
                od;

             fi;
        fi;

    end;

#    ############
#    Back to Function
#    ############

    if Length( arg ) >= 2 and IsList( arg[1] ) and IsMatrix( arg[2] ) then

        stdgens := arg[1];  # the LGO standard generators
        g := arg[2];

        if Length( stdgens ) < 1 or not IsMatrix( stdgens[1] ) then

            Error("first argument must be the LGO standard generators");
            return;
        fi;

        if not IsMatrix( g ) then
            Error("second argument must be a matrix"); return;
        fi;
    else
        Error("input: LGO standard generators and a matrix");
        return;
    fi;

    if Length(arg) = 3 then

        # The first 10 entries are the stdgens and their inverses
        slp := arg[3];

        if not IsList(slp) then
            Error("third argument must be a list");
            return;
        fi;
    else
        # We write an SLP into the variable slp
        # The first 10 entries are the stdgens and the inverses
        # s, t, del, v, x, s^-1, t^-1, del^-1, v^-1, x^-1
        slp := [    [1,1], [2,1], [3,1], [4,1], [5,1],
                    [1,-1],[2,-1],[3,-1],[4,-1],[5,-1]    ];
    fi;

    # the matrix
    d := Length( g );
    fld := FieldOfMatrixList( stdgens );

    # To create an MSLP, we allocate all the memory needed at the beginning.
    Add( slp, [1,0] );        tmppos        := Length(slp);    #11
    Add( slp, [1,0] );        AEMrespos    := Length(slp);    #12
    Add( slp,[4,1,10,1]);    vxpos        := Length(slp); #13  v*x^-1
    Add( slp, [13,-1] );    vxipos        := Length(slp);    #14 (v*x^-1)^-1
    Add( slp, [1,0] );        u1pos        := Length(slp);    #15
    Add( slp, [1,0] );        u2pos        := Length(slp);    #16
    Add( slp, [1,0] );        tir1pos        := Length(slp);    #17
    Add( slp, [1,0] );        tirzpos        := Length(slp);    #18
    Add( slp, [1,0] );        tvpos        := Length(slp);    #19

    # To save two slots of we allow two slots to be used by each two values
    # This does not create a conflict and increases the readability
    tcj1pos :=17; tcjzpos :=18;

    u1 := MutableCopyMat( One(g) );
    u2 := MutableCopyMat( One(g) );

    # If g is already a monomial matrix return u_1 = u_2 = I_d
    if TestIfMonomial( g ) then
        Add( slp, [ [1,0],[1,0] ] );
        return [ slp, [u1,g,u2] ];
    fi;

    f := LogInt(Size(fld), Characteristic(fld)); #ie q=p^f

    # We create the space for the T2 := { t_{2,1}(omega^ell)}
    # A Call of Transvections2 adds T2 to slp.
    T2pos := [ HighestSlotOfSLP(slp)+1 .. HighestSlotOfSLP(slp)+f ];

    for ell in [ 1..f ] do
        Add(slp, [1,0] );
    od;

    slp := Transvections2( stdgens, PrimitiveRoot(fld), slp, T2pos );
    # The positions of the transvections of T2 in slp are now
    # in the list T2pos.
    # In part. t_{2,1}(w^i) is in position T2pos[i].

    # Now we create the space for the Ti
    Ti_1pos := [ HighestSlotOfSLP(slp)+1 .. HighestSlotOfSLP(slp)+f ];

    for ell in [ 1..f ] do
        Add(slp, [1,0]);
    od;

    Tipos := [ HighestSlotOfSLP(slp)+1.. HighestSlotOfSLP(slp)+f ];

    for ell in [ 1..f ] do
        Add(slp, [1,0] );
    od;

    # Up until here the slp and the memory agree.
    # From now on we only overwrite existing memory positions.

    Info( InfoBruhat, 2, "Memory Usage is: ",19 + 3*f," memory slots ",
                            "in UnipotentDecomposition()\n");


    ########################
    # This is the usual Bruhat Decomposition
    # with additional Transvections
    # Changing columns means :changing u1, multiplying transvections
    #     at u1 from left, compute ShiftTransvections
    # Changing rows means :changing u2, multiplying transvections
    #     at u2 from right, BackShiftTransvections
    ########################

    # We perform something like a GAUSS algorithm
    # as described in Taylor with SLPs as in the MSLP paper

    g := MutableCopyMat( g );

    for c in [ d, d-1..2 ] do

        # Find the first non-zero entry in column c
        # g_{r,c} will be the pivot.
        j := 1; r := 0;

        while r <= d and j <= d and r = 0 do

            if not IsZero(g[j][c]) then
                r := j;
            fi;

            j := j + 1;

        od;

        if r = 0 then
            Error("matrix has 0 column");
        fi;

        # Step One: Clear all entries in column c apart from g[r][c]
        # This coincides with multiplying t_{i,r} from left.

        # Reinitialize Ti and Ti_1
        # Tipos <- { t_{2,1}(\omega^l) }, ti_1pos <- { I_d }
        for ell in [ 1..f ] do
            Add(slp, [ [1,0], Ti_1pos[ell] ] );
        od;
        for ell in [ 1..f ] do
            Add(slp, [ [T2pos[ell],1], Tipos[ell] ] );
        od;

        # If r is not the last row, we clear the rest of colum c:

        # First we clear the entry g[r+1][c]
        # Thus compute { t_{r,r-1}(\omega^l) }
        if r > 2 then
            FastShiftTransvections( r );
        fi;

        # Note: If r = d then Tipos= { t_{d,d-1} } and
        # there are no entries to clear below row r in column c.

        a := g[r][c]^-1;

        if r <= d-1 then

            # SLP-instructions: Compute { t_{r+1,r}(\omega^l) }
            # Save them in Tipos
            ShiftTransvections( r+1 );

            if not IsZero( g[r+1][c] ) then

                z := - g[r+1][c] * a;

                # add z times row r of g  to row r+1
                # add z times row r of u1  to row r+1
                 g[r+1] :=  g[r+1] + z *  g[r];
                u1[r+1] := u1[r+1] + z * u1[r];

                # SLP-instructions: Compute t_{r+1,r}(z) (cf Lemma 4.2 p12)
                # tvpos <- t_{r+1,r}(z)
                TransvecAtAlpha(z);

                # SLP-instructions: u_1 -> t_{r+1,r}(z) * u_1
                Add( slp, [ [tvpos,1, u1pos,1 ], u1pos ] );

            fi;

            Add(slp, [ [Tipos[1],1],tir1pos ] );
            # we have now cleared the entry in g[r+1][c]

            # Second: Clear the rest of column c
            for i in [ r+2..d ] do

                ShiftTransvections( i );
                # Now Ti contains all the Transvections
                # \{ t_{i,i-1}(ell) \}

                if not IsZero(g[i][c]) then

                    z := -g[i][c] * a;

                    # add z times row r of g  to row i
                    # add z times row r of u1  to row i
                    g[i] := g[i] + z*g[r];
                    u1[i] := u1[i] + z*u1[r];

                    # SLP-instructions: Compute t_{i,i-1}(z) (cf Lemma 4.2 p12)
                    # tvpos <- t_{i,i-1}(z)
                    TransvecAtAlpha(z);

                    # In tir1pos is the value t_{i-1,r}(1)
                    # SLP-instructions: compute t_{i,r}(z)
                    instr := [tvpos,-1,tir1pos,-1,tvpos, 1,tir1pos, 1];
                    Add( slp, [ instr, tirzpos ] ); # tirz

                    # SLP-instructions: u_1 -> t_{i,r}(z) * u_1
                    instr := [ tirzpos, 1, u1pos,1];
                    Add( slp, [ instr, u1pos ] );

                fi;

                # SLP-instructions: Iterate t_{i,r}(1) -> t_{i+1,r}(1)
                instr := [ Tipos[1],-1, tir1pos,-1, Tipos[1],1, tir1pos,1 ];
                Add(slp, [ instr, tir1pos ] );

            od;

        fi; # r <= d-1

        # Step Two: Clear all entries in row r apart from g[r][c]
        # This coincides with multiplying t_{c,j} from right.
        if c >= 2 then

            # if c = d then Ti already contains t_d(d-1)
            # if c <= d-1 then we swap Ti and Ti-1 so that
            # initially Ti contains t_(d-1)(d-2) and
            # Ti_1 contains t_d(d-1) and then shift back
            if IsEvenInt(d) and c <= d-1 then

                for ell in [ 1..f ] do

                    Add(slp, [ [ Tipos[ell],1 ], tmppos ] );
                    Add(slp, [ [ Ti_1pos[ell],1 ], Tipos[ell] ] );
                    Add(slp, [ [ tmppos,1 ], Ti_1pos[ell] ] );

                od;

            elif c <= d-1 then
               BackShiftTransvections( c );
            fi;

            # First we clear the entry g[r][c-1]
            # Thus determine SLP-instructions:
            # given t_{d-1,d-2} = Tipos, write Tipos <- t_{c,c-1} (d odd)
            # resp.
            #    t_{d-1,d-2} = Tipos     Tipos <- t_{c,c-1}
            #    t_{d,d-1} = Ti_1pos        Ti_1pos <- t_{c+1,c}     (d even)
            if c <= d-2 then
               FastBackShiftTransvections(c);
            fi;
            # Now Tipos = { t_{c,c-1}(\omega^l) }

            if not IsZero( g[r][c-1] ) then

                z := -g[r][c-1] * a;

                # SLP-instructions: Compute t_{c,c-1}(z) (cf Lemma 4.2 p12)
                # tvpos <- t_{c,c-1}(z)
                TransvecAtAlpha(z);

                # add z times column c of g to column c-1
                # add z times column c of u2 to column c-1
                g{[ 1..d ]}[ c-1 ] := g{[ 1..d ]}[ c-1 ] + z * g{[1..d]}[c];
                u2{[1..d]}[c-1] := u2{[1..d]}[c-1] + z * u2{[1..d]}[c];

                # SLP-instructions: u_2 -> u_2 * t_{c,c-1}(z)
                instr := [ u2pos, 1, tvpos,1];
                Add(slp,[instr, u2pos] ); # u2 overwritten

            fi;

            Add(slp, [ [Tipos[1],1], tcj1pos ] );

            # If c = d then Ti_1 is not correct yet.
            if IsEvenInt(d) and c = d then
                for ell in [ 1..f ] do
                    Add( slp, [ [ Tipos[ell],1 ], tmppos ] );
                    Add( slp, [ [ Ti_1pos[ell],1 ], Tipos[ell] ] );
                    Add( slp, [ [ tmppos,1 ], Ti_1pos[ell] ] );
                od;
            elif c-2 > 0 then
                BackShiftTransvections( c-2 );
            fi;

            # Now clear the rest of row r
            for j in [ c-2, c-3..1 ] do

                if not IsZero( g[r][j] ) then

                    z := - g[r][j] * a;

                    # SLP-instructions: Compute t_{j+,j}(z) (cf Lemma 4.2 p12)
                    # tvpos <- t_{j+1,j}(z)
                    TransvecAtAlpha(z);

                    # SLP-instructions to compute t_{c,j}(z) using (eq (9) p12)
                    instr := [ tcj1pos,-1, tvpos,-1, tcj1pos,1, tvpos,1 ];
                    Add( slp, [ instr,tcjzpos ] ); # tcjz

                    # add z times column c of g to column j
                    # add z times column c of u2 to column j
                     g{[1..d]}[j] :=  g{[1..d]}[j] + z *  g{[1..d]}[c];
                    u2{[1..d]}[j] := u2{[1..d]}[j] + z * u2{[1..d]}[c];

                    # SLP-instructions: u_2 -> u_2 * t_{c,j}(z)
                    instr := [ u2pos,1, tcjzpos,1 ];
                    Add( slp, [ instr, u2pos ] );
                fi;

                # SLP-instructions: Iterate t_{c,j+1}(1) -> t_{c,j}(1)
                instr := [ tcj1pos,-1, Tipos[1],-1, tcj1pos,1, Tipos[1],1 ];
                Add(slp, [ instr, tcj1pos ]);

                # SLP-instructions:
                # Iterate { t_{j+1,j}(\omega^l) } -> { t_{j,j-1}(\omega^l) }
                if j > 1 then
                    BackShiftTransvections( j );
                fi;
            od;
        fi;
    od;

    ## Add lastline to the slp to display u1 and u2
    ## Thus StraightLineProgram yields [u1,u2] as result
    Add( slp, [ [u1pos,1], [u2pos,1] ]);

    # Now u1^-1 * g * u2^-1 is the input matrix
    return [slp, [u1, g,  u2] ];

end
);


InstallGlobalFunction(  UnipotentDecompositionNC,
function( arg )

    local    stdgens, c, r, i, j, a, z, d, f, ell, fld, u1, u2, g, slp, instr,
            tmppos, AEMrespos, vxpos, vxipos, u1pos, u2pos, tvpos,
            tir1pos, tirzpos, tcj1pos, tcjzpos, T2pos, Tipos, Ti_1pos,
            TransvecAtAlpha, ShiftTransvections, FastShiftTransvections,
            BackShiftTransvections, FastBackShiftTransvections;

#    ###############
#    Local Functions
#    ###############

#    The following five functions are local as they have side effects.
#    In particular, they modify the global variables T_i and Ti_1

    #####
    # TransvectionAtAlpha()
    #####

    # Let alpha in GF(p^f), alpha = Sum a_l omega^l, omega a primitive element
    # Let slp be the list of instructions in UnipotentDecomposition and Tipos
    # denote the slots where transvections t_{i,j}(omega^ell) 0 <= ell < f
    # are saved. This function computes
    # t_{i,j}(alpha) = product t_{i,j}(omega^ell)^{a_ell}  (see Lemma 4.2)
    # where the exponents a_ell are given by CoefficientsPrimitiveElement.
    # (For Definition of Transvections see paper p11)

    TransvecAtAlpha := function( alpha )

        local cc, ell, instr;

        # if omega = 1 then we overwrite the position for tv with Ti(1)
        if IsOne( alpha ) then
            Add(slp, [ [ Tipos[1], 1 ], tvpos ] );
            return;
        fi;

        cc := CoefficientsPrimitiveElement( fld, alpha );
        instr := [];

        for ell in [ 1..Length(cc) ] do

            if not IsZero( cc[ell] ) then
                Append( instr, [ Tipos[ell], Int(cc[ell]) ] );
            fi;
        od;

        if Length( instr ) = 0 then
            Error("TransvecAtAlpha: this should not happen");
        fi;

        Add( slp, [ instr,tvpos ] );

        return;

    end;


    #####
    # ShiftTransvections()
    #####

    # Let Ti be the set of transvections { t_{i(i-1)}(omega^ell) }
    # and Ti_1 the set of transvections { t_{(i-1)(i-2)}(omega^ell) }.

    # ShiftTransvections computes { t_{i+1,i}(omega^ell) } for given
    # Ti and Ti_1 (This coincides with eq(8) p12)
    # stores them in the variable Ti and stores
    # the transvections  { t_{i,i-1}(omega^ell) } in the variable Ti_1.

    # This corresponds to ( eq (7+8) p12 )

    ShiftTransvections := function( i )

        local ell;

        # For i = 2: Ti=T2.
        if i <= 2 then return; fi;

        if IsOddInt(d) then
            # If d is Odd: Conjugate the last Ti (eq (8))
            for ell in [ 1..f ] do
                Add( slp, [ [ 4,1, Tipos[ell],1, 9,1], Tipos[ell] ] );
            od;
        else
            if i = 3 then
                # Compute T3 differently (eq (7))
                for ell in [ 1..f ] do
                    # Copy what is in Ti into Ti_1
                    Add(slp, [ [Tipos[ell],1 ], Ti_1pos[ell] ] );
                    # Write the new instruction to compute Ti
                    Add( slp, [ [ vxipos,1, Tipos[ell],1, vxpos,1],
                                Tipos[ell]    ] );
                od;
            else
                # If d is Even: Conjugate the 2nd last Ti (eq (8))
                for ell in [ 1..f ] do
                    # Copy the instruction in Ti into tmp position,
                    Add(slp,[ [ Tipos[ell], 1 ], tmppos ] );
                    # conjugate Ti_1 by v and write into Tipos
                    Add( slp, [ [ 9,1, Ti_1pos[ell],1, 4,1], Tipos[ell] ] );
                    Add(slp, [ [tmppos,1], Ti_1pos[ell] ] );
                od;
            fi;
        fi;
    end;


    #####
    # FastShiftTransvections()
    #####

    # Given t_2,1 we compute t_{i,i-1} using fast exponentation.
    # This algorithm will be called in each step of the main loop and
    # is more efficient than calling ShiftTransvections (r-2) times.

    FastShiftTransvections := function( i )

        local ell;

        # For i = 2: Ti=T2.
        if i <= 2 then return; fi;

        if IsOddInt( d ) then

            instr := AEM( 4, AEMrespos, tmppos, i-2 );
            Append( slp, instr );

            # If d is Odd: Conjugate the last Ti (eq (8))
            for ell in [ 1..f ] do
                Add( slp, [ [ AEMrespos,1, Tipos[ell],1, AEMrespos,-1 ],
                            Tipos[ell] ] );
            od;
        else
            if i = 3 then
                # Compute T3 differently (eq (7))
                for ell in [ 1..f ] do
                    # Copy what is in Ti into Ti_1
                    Add(slp, [ [Tipos[ell],1], Ti_1pos[ell] ] );
                    # Write the new instruction to compute Ti
                    Add( slp, [ [ vxipos,1, Tipos[ell],1, vxpos,1],
                                Tipos[ell]    ] );
                od;
            elif IsOddInt( i ) then

                #T_i = v^-(i-3)/2*T_3*v^(i-3)/2
                #T_i-1=v^-(i-3)/2*T_2*v^(i-3)/2

                #Set T3 and T2 in Position
                for ell in [ 1..f ] do
                    # Copy what is in Ti into Ti_1
                    Add(slp, [[Tipos[ell],1],Ti_1pos[ell]] );
                    # Write the new instruction to compute Ti
                    Add( slp, [ [ vxipos,1, Tipos[ell],1, vxpos,1],
                                Tipos[ell]    ] );
                od;

                instr := AEM(4,AEMrespos,tmppos,(i-3)/2);
                Append( slp, instr );
                # now AEMrespos knows v^(i-3)/2

                for ell in [ 1..f ] do

                    Add( slp, [ [ AEMrespos,-1, Tipos[ell],1, AEMrespos,1],
                                        Tipos[ell]    ] );

                    Add( slp, [ [ AEMrespos,-1, Ti_1pos[ell],1, AEMrespos,1],
                                        Ti_1pos[ell]  ] );
                od;

            else

                #T_i = v^-(i-2)/2*T_2*v^(i-2)/2
                #T_i-1=v* v^-(i-2)/2*T_3*v^(i-2)/2* v^-1
                #So save t_3 in Ti_1pos
                for ell in [ 1..f ] do
                    Add( slp, [ [ vxipos,1, Tipos[ell],1, vxpos,1],
                                Ti_1pos[ell]    ] );
                od;

                # and compute v^(i-2)/2
                instr := AEM(4,AEMrespos,tmppos,(i-2)/2);
                Append( slp, instr );

                for ell in [ 1..f ] do
                    Add( slp, [ [ AEMrespos,-1, Tipos[ell],1, AEMrespos,1],
                                    Tipos[ell] ] );

                    Add( slp, [ [ AEMrespos,-1, Ti_1pos[ell],1, AEMrespos,1],
                                    Ti_1pos[ell] ] );

                    Add( slp, [ [ 4,1, Ti_1pos[ell],1, 9,1], Ti_1pos[ell] ] );
                od;
            fi;
        fi;

    end;


    #####
    # BackShiftTransvections()
    #####

    # This function is very similar to ShiftTransvections,
    # except it works in the reverse order, namely
    # BackShiftTransvections computes t{(i+1)i}
    # given t_{(i+2)i} and t_{(i+3)(i+2)}

    BackShiftTransvections := function( i )

        local ell;

        if IsOddInt(d) then
            # for odd d we have to conjugate the previous Ti by v
            for ell in [ 1..f ] do
                Add(slp, [[ 9,1, Tipos[ell],1, 4,1], Tipos[ell] ] );
            od;
        else
            if i = 1 then
                # We compute T3 differently
                for ell in [ 1..f ] do

                    Add( slp, [ [Tipos[ell],1], tmppos ] );
                    # write the new instruction to compute Ti
                    Add( slp, [ [ vxpos,1, Tipos[ell],1, vxipos,1],
                                Tipos[ell] ] );
                    # copy what is in tmppos into Ti_1
                    Add(slp, [ [ tmppos,1 ], Ti_1pos[ell] ] );
                od;
            else
                # for even d we have to conjugate the 2nd last Ti
                for ell in [ 1..f ] do

                    # copy the instruction in Ti into the tmp position
                    Add(slp,[[Tipos[ell],1], tmppos]);
                    # now conjugate T_{i+1} by v and write into Tipos
                    Add( slp, [ [ 4,1, Ti_1pos[ell],1, 9,1],
                                Tipos[ell] ] );

                    Add( slp, [ [ tmppos,1 ], Ti_1pos[ell] ] );
                od;
             fi;
        fi;
    end;


    #####
    # FastBackShiftTransvections()
    #####

    # As for ShiftTransvections, we need an efficient way to compute
    # BackShiftTransvections multiple times in a row.

    FastBackShiftTransvections := function( i )

        local ell;

        if IsOddInt( d ) then

            instr := AEM( 4, AEMrespos, tmppos, i - d + 1 );
            Append( slp, instr );

            # If d is Odd: Conjugate the last Ti (eq (8))
            for ell in [ 1..f ] do

                Add( slp, [ [ AEMrespos,1, Tipos[ell],1, AEMrespos,-1 ],
                                Tipos[ell] ] );
            od;
        else
            # The case i = 1 cant occur in our implementation
            if IsOddInt( i ) then

                instr := AEM( 4, AEMrespos, tmppos, (i-d+1)/2 );
                Append( slp, instr );

                for ell in [ 1..f ] do

                    Add( slp, [ [ AEMrespos,-1, Tipos[ell],1, AEMrespos,1],
                                    Tipos[ell] ] );

                    Add( slp, [ [ AEMrespos,-1, Ti_1pos[ell],1, AEMrespos,1],
                                    Ti_1pos[ell] ] );
                od;
            else
                for ell in [ 1..f ] do

                    Add( slp, [ [ Tipos[ell],1 ], tmppos ] );
                    Add( slp, [ [ Ti_1pos[ell],1], Tipos[ell] ] );
                    Add(slp,[ [ tmppos,1 ], Ti_1pos[ell] ] );
                od;

                instr := AEM( 4, AEMrespos, tmppos, (d-c)/2 );
                Append( slp, instr );

                for ell in [ 1..f ] do
                    Add( slp, [ [ AEMrespos,1, Tipos[ell],1, AEMrespos,-1],
                                    Tipos[ell] ] );

                    Add( slp, [ [ AEMrespos,1, Ti_1pos[ell],1, AEMrespos,-1],
                                    Ti_1pos[ell]         ] );

                    Add( slp, [ [ 9,1, Ti_1pos[ell],1, 4,1], Ti_1pos[ell] ] );
                od;

             fi;
        fi;

    end;

#    ############
#    Back to Function
#    ############

    stdgens := arg[1];  # the LGO standard generators
    g := arg[2];

    if Length( arg ) = 3 then

        # The first 10 entries are the stdgens and their inverses
        slp := arg[3];

    else
        # We write an SLP into the variable slp
        # The first 10 entries are the stdgens and the inverses
        # s, t, del, v, x, s^-1, t^-1, del^-1, v^-1, x^-1
        slp := [    [1,1], [2,1], [3,1], [4,1], [5,1],
                    [1,-1],[2,-1],[3,-1],[4,-1],[5,-1]    ];
    fi;

    # the matrix
    d := Length( g );
    fld := FieldOfMatrixList( stdgens );

    # To create an MSLP, we allocate all the memory needed at the beginning.
    Add( slp, [1,0] );        tmppos        := Length(slp);    #11
    Add( slp, [1,0] );        AEMrespos    := Length(slp);    #12
    Add( slp,[4,1,10,1]);    vxpos        := Length(slp); #13  v*x^-1
    Add( slp, [13,-1] );    vxipos        := Length(slp);    #14 (v*x^-1)^-1
    Add( slp, [1,0] );        u1pos        := Length(slp);    #15
    Add( slp, [1,0] );        u2pos        := Length(slp);    #16
    Add( slp, [1,0] );        tir1pos        := Length(slp);    #17
    Add( slp, [1,0] );        tirzpos        := Length(slp);    #18
    Add( slp, [1,0] );        tvpos        := Length(slp);    #19

    # To save two slots of we allow two slots to be used by each two values
    # This does not create a conflict and increases the readability
    tcj1pos :=17; tcjzpos :=18;

    u1 := MutableCopyMat( One(g) );
    u2 := MutableCopyMat( One(g) );

    # If g is already a monomial matrix return u_1 = u_2 = I_d
    if TestIfMonomialNC( g ) then
        Add( slp, [ [u1pos,1], [u2pos,1] ] );
        return [ slp, [u1,g,u2] ];
    fi;

    f := LogInt(Size(fld), Characteristic(fld)); #ie q=p^f

    # We create the space for the T2 := { t_{2,1}(omega^ell)}
    # A Call of Transvections2 adds T2 to slp.
    T2pos := [ HighestSlotOfSLP(slp)+1 .. HighestSlotOfSLP(slp)+f ];

    for ell in [ 1..f ] do
        Add(slp, [1,0] );
    od;

    slp := Transvections2( stdgens, PrimitiveElement(fld), slp, T2pos );
    # The positions of the transvections of T2 in slp are now
    # in the list T2pos.
    # In part. t_{2,1}(w^i) is in position T2pos[i].

    # Now we create the space for the Ti
    Ti_1pos := [ HighestSlotOfSLP(slp)+1 .. HighestSlotOfSLP(slp)+f ];

    for ell in [ 1..f ] do
        Add(slp, [1,0]);
    od;

    Tipos := [ HighestSlotOfSLP(slp)+1.. HighestSlotOfSLP(slp)+f ];

    for ell in [ 1..f ] do
        Add(slp, [1,0] );
    od;

    # Up until here the slp and the memory agree.
    # From now on we only overwrite existing memory positions.

    Info( InfoBruhat, 2, "Memory Usage is: ",19 + 3*f," memory slots ",
                            "in UnipotentDecomposition()\n");


    ########################
    # This is the usual Bruhat Decomposition
    # with additional Transvections
    # Changing columns means :changing u1, multiplying transvections
    #     at u1 from left, compute ShiftTransvections
    # Changing rows means :changing u2, multiplying transvections
    #     at u2 from right, BackShiftTransvections
    ########################

    # We perform something like a GAUSS algorithm
    # as described in Taylor with SLPs as in the MSLP paper

    g := MutableCopyMat( g );

    for c in [ d,d-1..2 ] do

        # Find the first non-zero entry in column c
        # g_{r,c} will be the pivot.
        j := 1; r := 0;

        while r <= d and j <= d and r = 0 do

            if not IsZero( g[j][c] ) then
                r := j;
            fi;

            j := j + 1;

        od;

        if r = 0 then
            Error("matrix has 0 column");
        fi;

        # Step One: Clear all entries in column c apart from g[r][c]
        # This coincides with multiplying t_{i,r} from left.

        # Reinitialize Ti and Ti_1
        # Tipos <- { t_{2,1}(\omega^l) }, ti_1pos <- { I_d }
        for ell in [ 1..f ] do
            Add(slp, [ [1,0], Ti_1pos[ell] ] );
        od;
        for ell in [ 1..f ] do
            Add(slp, [ [ T2pos[ell],1 ], Tipos[ell] ] );
        od;

        # If r is not the last row, we clear the rest of colum c:

        # First we clear the entry g[r+1][c]
        # Thus compute { t_{r,r-1}(\omega^l) }
        if r > 2 then
            FastShiftTransvections( r );
        fi;

        # Note: If r = d then Tipos= { t_{d,d-1} } and
        # there are no entries to clear below row r in column c.

        a := g[r][c]^-1;

        if r <= d-1 then

            # SLP-instructions: Compute { t_{r+1,r}(\omega^l) }
            # Save them in Tipos
            ShiftTransvections( r+1 );

            if not IsZero( g[r+1][c] ) then

                z := - g[r+1][c] * a;

                # add z times row r of g  to row r+1
                # add z times row r of u1  to row r+1
                 g[r+1] :=  g[r+1] + z *  g[r];
                u1[r+1] := u1[r+1] + z * u1[r];

                # SLP-instructions: Compute t_{r+1,r}(z) (cf Lemma 4.2 p12)
                # tvpos <- t_{r+1,r}(z)
                TransvecAtAlpha(z);

                # SLP-instructions: u_1 -> t_{r+1,r}(z) * u_1
                Add( slp, [ [tvpos,1, u1pos,1 ], u1pos ] );

            fi;

            Add(slp, [ [ Tipos[1],1 ], tir1pos ] );
            # we have now cleared the entry in g[r+1][c]

            # Second: Clear the rest of column c
            for i in [ r+2..d ] do

                ShiftTransvections( i );
                # Now Ti contains all the Transvections
                # \{ t_{i,i-1}(ell) \}

                if not IsZero(g[i][c]) then

                    z := -g[i][c] * a;

                    # add z times row r of g  to row i
                    # add z times row r of u1  to row i
                     g[i] :=  g[i] + z *  g[r];
                    u1[i] := u1[i] + z * u1[r];

                    # SLP-instructions: Compute t_{i,i-1}(z) (cf Lemma 4.2 p12)
                    # tvpos <- t_{i,i-1}(z)
                    TransvecAtAlpha(z);

                    # In tir1pos is the value t_{i-1,r}(1)
                    # SLP-instructions: compute t_{i,r}(z)
                    instr := [tvpos,-1,tir1pos,-1,tvpos, 1,tir1pos, 1];
                    Add( slp, [ instr, tirzpos ] ); # tirz

                    # SLP-instructions: u_1 -> t_{i,r}(z) * u_1
                    instr := [ tirzpos, 1, u1pos,1];
                    Add( slp, [ instr, u1pos ] );

                fi;

                # SLP-instructions: Iterate t_{i,r}(1) -> t_{i+1,r}(1)
                instr := [ Tipos[1],-1, tir1pos,-1, Tipos[1],1, tir1pos,1 ];
                Add(slp, [ instr, tir1pos ] );

            od;

        fi; # r <= d-1

        # Step Two: Clear all entries in row r apart from g[r][c]
        # This coincides with multiplying t_{c,j} from right.
        if c >= 2 then

            # if c = d then Ti already contains t_d(d-1)
            # if c <= d-1 then we swap Ti and Ti-1 so that
            # initially Ti contains t_(d-1)(d-2) and
            # Ti_1 contains t_d(d-1) and then shift back
            if IsEvenInt(d) and c <= d-1 then

                for ell in [ 1..f ] do

                    Add(slp, [ [ Tipos[ell],1 ], tmppos ] );
                    Add(slp, [ [ Ti_1pos[ell],1 ], Tipos[ell] ] );
                    Add(slp, [ [ tmppos,1 ], Ti_1pos[ell] ] );

                od;

            elif c <= d-1 then
               BackShiftTransvections( c );
            fi;

            # First we clear the entry g[r][c-1]
            # Thus determine SLP-instructions:
            # given t_{d-1,d-2} = Tipos, write Tipos <- t_{c,c-1} (d odd)
            # resp.
            #    t_{d-1,d-2} = Tipos     Tipos <- t_{c,c-1}
            #    t_{d,d-1} = Ti_1pos        Ti_1pos <- t_{c+1,c}     (d even)
            if c <= d-2 then
               FastBackShiftTransvections( c );
            fi;
            # Now Tipos = { t_{c,c-1}(\omega^l) }

            if not IsZero( g[r][c-1] ) then

                z := -g[r][c-1] * a;

                # SLP-instructions: Compute t_{c,c-1}(z) (cf Lemma 4.2 p12)
                # tvpos <- t_{c,c-1}(z)
                TransvecAtAlpha(z);

                # add z times column c of g to column c-1
                # add z times column c of u2 to column c-1
                 g{[1..d]}[ c-1 ] :=  g{[1..d]}[ c-1 ] + z *  g{[ 1..d ]}[c];
                u2{[1..d]}[ c-1 ] := u2{[1..d]}[ c-1 ] + z * u2{[ 1..d ]}[c];

                # SLP-instructions: u_2 -> u_2 * t_{c,c-1}(z)
                instr := [ u2pos, 1, tvpos,1];
                Add( slp, [ instr, u2pos ] ); # u2 overwritten

            fi;

            Add(slp, [ [Tipos[1],1], tcj1pos ] );

            # If c = d then Ti_1 is not correct yet.
            if IsEvenInt( d ) and c = d then
                for ell in [ 1..f ] do
                    Add( slp, [ [ Tipos[ell],1 ], tmppos ] );
                    Add( slp, [ [ Ti_1pos[ell],1 ], Tipos[ell] ] );
                    Add( slp, [ [ tmppos,1 ], Ti_1pos[ell] ] );
                od;
            elif c-2 > 0 then
                BackShiftTransvections( c-2 );
            fi;

            # Now clear the rest of row r
            for j in [ c-2, c-3..1 ] do

                if not IsZero( g[r][j] ) then

                    z := - g[r][j] * a;

                    # SLP-instructions: Compute t_{j+,j}(z) (cf Lemma 4.2 p12)
                    # tvpos <- t_{j+1,j}(z)
                    TransvecAtAlpha(z);

                    # SLP-instructions to compute t_{c,j}(z) using (eq (9) p12)
                    instr := [ tcj1pos,-1, tvpos,-1, tcj1pos,1, tvpos,1 ];
                    Add( slp, [ instr,tcjzpos ] ); # tcjz

                    # add z times column c of g to column j
                    # add z times column c of u2 to column j
                     g{[1..d]}[j] :=  g{[1..d]}[j] + z *  g{[1..d]}[c];
                    u2{[1..d]}[j] := u2{[1..d]}[j] + z * u2{[1..d]}[c];

                    # SLP-instructions: u_2 -> u_2 * t_{c,j}(z)
                    instr := [ u2pos,1, tcjzpos,1 ];
                    Add( slp, [ instr, u2pos ] );
                fi;

                # SLP-instructions: Iterate t_{c,j+1}(1) -> t_{c,j}(1)
                instr := [ tcj1pos,-1, Tipos[1],-1, tcj1pos,1, Tipos[1],1 ];
                Add(slp, [ instr, tcj1pos ]);

                # SLP-instructions:
                # Iterate { t_{j+1,j}(\omega^l) } -> { t_{j,j-1}(\omega^l) }
                if j > 1 then
                    BackShiftTransvections( j );
                fi;
            od;
        fi;
    od;

    ## Add lastline to the slp to display u1 and u2
    ## Thus StraightLineProgram yields [u1,u2] as result
    Add( slp, [ [u1pos,1], [u2pos,1] ]);

    # Now u1^-1 * g * u2^-1 is the input matrix
    return [slp, [u1, g,  u2] ];

end
);



####################
# PART II - b)
#    Basically the same as in II - a)
#    But now we save all Transvections
####################

# Compute the Bruhat decomposition of the matrix g, given
# the standard generators for the group.
# In this version we will store all the transvections t_i,i-1(w^l).
# this will increase the memory usage by (d-3)*f but reduce runtime

InstallGlobalFunction(  UnipotentDecompositionWithTi,
function(arg)

    local    stdgens, c, r, i, j, a, z, f, ell, fld, d, slp, instr, lastline,
            u1, u2, g, Tipos, u1pos, u2pos, tir1pos, tirzpos, tcj1pos,
            tcjzpos, tvpos, T2pos, vxpos, vxipos,
            TransvectionAtAlpha, ComputeAllTransvections;


#    ###############
#    Local Functions
#    ###############

    #####
    # TransvectionAtAlpha()
    #####

    # Let alpha in GF(p^f), alpha = sum a_ell omega^ell
    # where omega is a primitive element
    # Suppose further that Tipos is a list of transvections
    # of the form { t_{i,i-1}(omega^l) }, 2 <= i <= d, 0 <= ell < f.
    # Then this function computes t_{i,i-1}( alpha ) by (Lemma 4.2)
    # And saves the result in tvpos.

    TransvectionAtAlpha := function( i, alpha )

        local cc, ell;

        if IsOne( alpha ) then
            Add( slp , [ [Tipos[i][1],1] , tvpos ] );
            return true;
        fi;

        cc := CoefficientsPrimitiveElement( fld, alpha );
        instr := [];

        for ell in [ 1..Length(cc) ] do

            if not IsZero( cc[ell] ) then
                Append(    instr, [ Tipos[i][ell], Int( cc[ell] ) ] );
            fi;
        od;

        Add( slp, [ instr, tvpos ] );

        return true;

    end;

    #####
    # ComputeAllTransvections()
    #####

    ## We first compute all the Ti for i >= 3 and add them to the SLP
    ## This are eq (7) and (8) p12
    ## Used instead of Schift- and BackshiftTransvections

    ComputeAllTransvections := function()

        local i;

        for i in [ 3..d ] do

            if IsOddInt( d ) then
                # If d is Odd: Conjugate the previous Ti
                for ell in [ 1..f ] do
                    Add(slp,[ [4,1, Tipos[i-1][ell],1, 9,1],
                                    Tipos[i][ell] ] );
                od;
            elif i = 3 then
                # Compute T3 differently
                for ell in [ 1..f ] do
                    Add( slp, [ [ vxipos,1, Tipos[i-1][ell],1, vxpos,1],
                            Tipos[3][ell] ] );
                od;
            else
                # If d is Even: Conjugate the 2nd last Ti
                for ell in [ 1..f ] do
                    Add( slp , [ [ 9,1, Tipos[i-2][ell],1, 4,1 ],
                                    Tipos[i][ell] ] );
                od;
            fi;

        od;
    end;

#    ###############
#    Back to Function
#    ###############

    if Length(arg) >= 2 and IsList(arg[1]) and IsMatrix(arg[2]) then

        stdgens := arg[1];  # the LGO standard generators
        g := arg[2];

        if Length(stdgens) < 1 or not IsMatrix( stdgens[1]) then
            Error("first argument must be the LGO standard generators");
            return;
        fi;

        if not IsMatrix( g ) then
            Error("second argument must be a matrix");
            return;
        fi;
    else

        Error("input: LGO standard generators and a matrix");
        return;
    fi;

    if Length(arg) = 3 then

        # The first 10 entries are the stdgens and their inverses
        slp := arg[3];
        if not IsList(slp) then
            Error("third argument must be a list");
            return;
        fi;
    else
        # we write an SLP into the variable slp
        # The first 10 entries are the stdgens and inverses
        # s, t, del, v, x, s^-1, t^-1, del^-1, v^-1, x^-1
        slp := [    [1,1], [2,1], [3,1], [4,1], [5,1],
                    [1,-1],[2,-1],[3,-1],[4,-1],[5,-1]    ];
    fi;

    # the matrix
    g := MutableCopyMat(g); #ie Matrix can be modified
    d := Length(g);
    fld := FieldOfMatrixList(stdgens);

    # To create a MSLP, we allocate all the memory needed at the beginning.
    Add( slp, [4,1,10,1]);    vxpos    := Length(slp);    #11 v*x^-1
    Add( slp, [11,-1]);        vxipos     := Length(slp);    #12 (v*x^-1)^-1
    Add( slp, [1,0] );        u1pos     := Length(slp); #13
    Add( slp, [1,0] );        u2pos     := Length(slp); #14
    Add( slp, [1,0] );        tvpos     := Length(slp); #15

    # The implementation allows us to use the same slot for different purposes
    tir1pos    := 11; tirzpos := 12;
    tcj1pos := 11; tcjzpos := 12;

    # u1,u2 coincide with the Input used in paper p16 Alg1.
    u1 := MutableCopyMat( One(g));    #Copy of id_dxd
    u2 := MutableCopyMat( One(g));    #Copy of id_dxd

    # add lastline to the slp to display the memory contents u1,u2
    lastline := [ [u1pos,1], [u2pos,1] ];

    f := LogInt( Size(fld), Characteristic(fld) );

    # now we create the space for the T2 \{ t_{2,1}(w^l) \}
    T2pos := [ HighestSlotOfSLP(slp)+1 .. HighestSlotOfSLP(slp)+f ];

    for ell in [ 1..f ] do
        Add(slp, [1,0] );
    od;

    slp := Transvections2( stdgens, PrimitiveElement(fld), slp, T2pos );
    # Now slp computes T2 and the positions of the transvections
    # of T2 in the slp are in the list T2pos
    # now we create the space for all of the other Ti
    Tipos := [];
    Tipos[2] := T2pos;

    for i in [3 .. d] do

        Tipos[i] := [ HighestSlotOfSLP(slp)+1..HighestSlotOfSLP(slp)+f ];

        for ell in [1 .. f] do
            Add(slp, [1,0]);
        od;
    od;

    # Up until here the slp and the memory agree.
    # From now on we only overwrite existing memory positions.
    Info( InfoBruhat, 2, "Memory Usage is: ",HighestSlotOfSLP(slp)," memory slots ",
                            "in UnipotentDecompositionWithTi()\n");

    ComputeAllTransvections();

    # Now we don't need vxpos and vxipos again,
    # we now use the slots alternating for tir1pos and tirzpos resp.
    # for tcj1pos and tcjzpos

    for i in [ 2..d ] do
        Append( lastline, List( Tipos[i], j -> [j,1] ));
    od;

    # As described in the MSLP paper
    # We perform something like a GAUSS algorithm

    for c in [ d, d-1..2 ] do

        # find the first non-zero entry in column c
        j := 1; r := 0;
        while r <= d and r = 0 do

            if not IsZero( g[j][c] ) then
                r := j;
            fi;

            j := j + 1;
        od;

        # Now we clear all entries in column c apart from g[r][c]
        # if r is not the last row, we clear the rest of colum c
        # first we clear the entry g[r+1][c]

        a := g[r][c]^-1;

        if r <= d-1 then

            if not IsZero( g[r+1][c] ) then

                z := - g[r+1][c] * a;

                TransvectionAtAlpha( r+1, z );

                # add z times row r of g  to row r+1
                # add z times row r of u1  to row r+1
                g[r+1] := g[r+1] + z * g[r];
                u1[r+1] := u1[r+1] + z * u1[r];
                # This is just Gauß:

                Add(slp, [ [tvpos,1, u1pos, 1], u1pos] );
            fi;

            Add( slp, [ [Tipos[r+1][1],1], tir1pos ] );
            # we have now cleared the entry in g[r+1][c]

            # Now clear the rest of column c
            for i in [ r+2..d ] do
                if not IsZero( g[i][c] ) then

                    z := -g[i][c] * a;

                    TransvectionAtAlpha(i, z );

                    instr := [ tvpos,-1, tir1pos,-1,
                                tvpos,1, tir1pos,1 ];
                    Add(slp,[instr,tirzpos]); # tirz

                    # add z times row r of g  to row i
                    # add z times row r of u1  to row i
                     g[i] :=  g[i] + z *  g[r];
                    u1[i] := u1[i] + z * u1[r];

                    instr := [ tirzpos, 1, u1pos,1];
                    Add(slp,[instr, u1pos] );


                fi;

                # get tir1 ready for the next i
                instr := [ Tipos[i][1],-1,tir1pos,-1,
                            Tipos[i][1],1,tir1pos,1 ];

                Add(slp, [instr,tir1pos]);
            od;
        fi; # r <= d-1

        # Next we clear row r apart from g[r][c]
        if c >= 2 then
            # if c = d then Ti already contains t_d(d-1)
            # if c <= d-1 then we swap Ti and Ti-1 so that
            # initially Ti contains t_(d-1)(d-2) and
            # Ti_1 contains t_d(d-1) and then shift back
            # now Ti contains t_c(c-1)
            if not IsZero( g[r][c-1] ) then

                z := - g[r][c-1] * a;

                TransvectionAtAlpha( c, z );

                # Add z times column c of g  to column c-1,
                # add z times column c of u2 to column c-1
                 g{[1..d]}[c-1] :=  g{[1..d]}[c-1] + z *  g{[1..d]}[c];
                u2{[1..d]}[c-1] := u2{[1..d]}[c-1] + z * u2{[1..d]}[c];

                # Copy this in slp
                instr := [ u2pos, 1, tvpos,1];
                Add(slp,[instr, u2pos] ); # u2 overwritten



            fi;
            Add(slp, [ [Tipos[c][1],1 ], tcj1pos ] );

            # Now clear the rest of row r
            for j in [ c-2, c-3..1 ] do

                if not IsZero( g[r][j] ) then

                    z := - g[r][j] * a;

                    TransvectionAtAlpha( j+1, z );

                    instr := [ tcj1pos,-1, tvpos,-1, tcj1pos,1, tvpos,1 ];
                    Add(slp, [instr,tcjzpos] ); # tcjz

                    # add z times column c of g to column j
                    # add z times column c of u2 to column j
                    g{[1..d]}[j] := g{[1..d]}[j] + z*g{[1..d]}[c];
                    u2{[1..d]}[j] := u2{[1..d]}[j] + z*u2{[1..d]}[c];

                    instr := [ u2pos, 1, tcjzpos,1];
                    Add( slp, [instr, u2pos] ); # u2 overwritten

                fi;

                # get tcj1 ready for the next iteration
                instr := [tcj1pos,-1, Tipos[j+1][1],-1,
                            tcj1pos,1, Tipos[j+1][1],1 ];
                Add( slp, [ instr, tcj1pos ] );
           od;
        fi;
    od;

    Add( slp, lastline );

    return [slp, [u1, g, u2] ];

end
);


InstallGlobalFunction(  UnipotentDecompositionWithTiNC,
function( arg )

    local    stdgens, c, r, i, j, a, z, f, ell, fld, d, slp, instr, lastline,
            u1, u2, g, Tipos, u1pos, u2pos, tir1pos, tirzpos, tcj1pos,
            tcjzpos, tvpos, T2pos, vxpos, vxipos,
            TransvectionAtAlpha, ComputeAllTransvections;


#    ###############
#    Local Functions
#    ###############

    #####
    # TransvectionAtAlpha()
    #####

    # Let alpha in GF(p^f), alpha = sum a_ell omega^ell
    # where omega is a primitive element
    # Suppose further that Tipos is a list of transvections
    # of the form { t_{i,i-1}(omega^l) }, 2 <= i <= d, 0 <= ell < f.
    # Then this function computes t_{i,i-1}( alpha ) by (Lemma 4.2)
    # And saves the result in tvpos.

    TransvectionAtAlpha := function( i, alpha )

        local cc, ell;

        if IsOne( alpha ) then
            Add( slp , [ [Tipos[i][1],1] , tvpos ] );
            return true;
        fi;

        cc := CoefficientsPrimitiveElement( fld, alpha );
        instr := [];

        for ell in [ 1..Length(cc) ] do

            if not IsZero( cc[ell] ) then
                Append(    instr, [ Tipos[i][ell], Int( cc[ell] ) ] );
            fi;
        od;

        Add( slp, [ instr, tvpos ] );

        return true;

    end;

    #####
    # ComputeAllTransvections()
    #####

    ## We first compute all the Ti for i >= 3 and add them to the SLP
    ## This are eq (7) and (8) p12
    ## Used instead of Schift- and BackshiftTransvections

    ComputeAllTransvections := function()

        local i;

        for i in [ 3..d ] do

            if IsOddInt( d ) then
                # If d is Odd: Conjugate the previous Ti
                for ell in [ 1..f ] do
                    Add(slp,[ [4,1, Tipos[i-1][ell],1, 9,1],
                                    Tipos[i][ell] ] );
                od;
            elif i = 3 then
                # Compute T3 differently
                for ell in [ 1..f ] do
                    Add( slp, [ [ vxipos,1, Tipos[i-1][ell],1, vxpos,1],
                            Tipos[3][ell] ] );
                od;
            else
                # If d is Even: Conjugate the 2nd last Ti
                for ell in [ 1..f ] do
                    Add( slp , [ [ 9,1, Tipos[i-2][ell],1, 4,1 ],
                                    Tipos[i][ell] ] );
                od;
            fi;

        od;
    end;

#    ###############
#    Back to Function
#    ###############

    stdgens := arg[1];  # the LGO standard generators
    g := arg[2];

    if Length(arg) = 3 then

        # The first 10 entries are the stdgens and their inverses
        slp := arg[3];

    else
        # we write an SLP into the variable slp
        # The first 10 entries are the stdgens and inverses
        # s, t, del, v, x, s^-1, t^-1, del^-1, v^-1, x^-1
        slp := [    [1,1], [2,1], [3,1], [4,1], [5,1],
                    [1,-1],[2,-1],[3,-1],[4,-1],[5,-1]    ];
    fi;

    # the matrix
    g := MutableCopyMat(g); #ie Matrix can be modified
    d := Length(g);
    fld := FieldOfMatrixList(stdgens);

    # To create a MSLP, we allocate all the memory needed at the beginning.
    Add( slp, [4,1,10,1]);    vxpos    := Length(slp);    #11 v*x^-1
    Add( slp, [11,-1]);        vxipos     := Length(slp);    #12 (v*x^-1)^-1
    Add( slp, [1,0] );        u1pos     := Length(slp); #13
    Add( slp, [1,0] );        u2pos     := Length(slp); #14
    Add( slp, [1,0] );        tvpos     := Length(slp); #15

    # The implementation allows us to use the same slot for different purposes
    tir1pos    := 11; tirzpos := 12;
    tcj1pos := 11; tcjzpos := 12;

    # u1,u2 coincide with the Input used in paper p16 Alg1.
    u1 := MutableCopyMat( One(g));    #Copy of id_dxd
    u2 := MutableCopyMat( One(g));    #Copy of id_dxd

    # add lastline to the slp to display the memory contents u1,u2
    lastline := [ [u1pos,1], [u2pos,1] ];

    f := LogInt( Size(fld), Characteristic(fld) );

    # now we create the space for the T2 \{ t_{2,1}(w^l) \}
    T2pos := [ HighestSlotOfSLP(slp)+1 .. HighestSlotOfSLP(slp)+f ];

    for ell in [ 1..f ] do
        Add(slp, [1,0] );
    od;

    slp := Transvections2( stdgens, PrimitiveElement(fld), slp, T2pos );
    # Now slp computes T2 and the positions of the transvections
    # of T2 in the slp are in the list T2pos
    # now we create the space for all of the other Ti
    Tipos := [];
    Tipos[2] := T2pos;

    for i in [3 .. d] do

        Tipos[i] := [ HighestSlotOfSLP(slp)+1..HighestSlotOfSLP(slp)+f ];

        for ell in [ 1..f ] do
            Add(slp, [1,0]);
        od;
    od;

    # Up until here the slp and the memory agree.
    # From now on we only overwrite existing memory positions.
    Info( InfoBruhat, 2, "Memory Usage is: ",HighestSlotOfSLP(slp)," memory slots ",
                            "in UnipotentDecompositionWithTi()\n");

    ComputeAllTransvections();

    # Now we don't need vxpos and vxipos again,
    # we now use the slots alternating for tir1pos and tirzpos resp.
    # for tcj1pos and tcjzpos

    for i in [ 2..d ] do
        Append( lastline, List( Tipos[i], j -> [j,1] ) );
    od;

    if TestIfMonomialNC( g ) then
        Add( slp, lastline );
        return [ slp, [u1, g, u2] ];
    fi;
    # As described in the MSLP paper
    # We perform something like a GAUSS algorithm

    for c in [ d, d-1..2 ] do

        # find the first non-zero entry in column c
        j := 1; r := 0;
        while r <= d and r = 0 do

            if not IsZero( g[j][c] ) then
                r := j;
            fi;

            j := j + 1;
        od;

        # Now we clear all entries in column c apart from g[r][c]
        # if r is not the last row, we clear the rest of colum c
        # first we clear the entry g[r+1][c]

        a := g[r][c]^-1;

        if r <= d-1 then

            if not IsZero( g[r+1][c] ) then

                z := - g[r+1][c] * a;

                TransvectionAtAlpha( r+1, z );

                # add z times row r of g  to row r+1
                # add z times row r of u1  to row r+1
                 g[r+1] :=  g[r+1] + z *  g[r];
                u1[r+1] := u1[r+1] + z * u1[r];
                # This is just Gauß:

                Add(slp, [ [tvpos,1, u1pos, 1], u1pos] );
            fi;

            Add( slp, [ [Tipos[r+1][1],1], tir1pos ] );
            # we have now cleared the entry in g[r+1][c]

            # Now clear the rest of column c
            for i in [ r+2..d ] do
                if not IsZero( g[i][c] ) then

                    z := -g[i][c] * a;

                    TransvectionAtAlpha(i, z );

                    instr := [ tvpos,-1, tir1pos,-1,
                                tvpos,1, tir1pos,1 ];
                    Add(slp,[instr,tirzpos]); # tirz

                    # add z times row r of g  to row i
                    # add z times row r of u1  to row i
                     g[i] :=  g[i] + z *  g[r];
                    u1[i] := u1[i] + z * u1[r];

                    instr := [ tirzpos, 1, u1pos,1];
                    Add(slp,[instr, u1pos] );


                fi;

                # get tir1 ready for the next i
                instr := [ Tipos[i][1],-1,tir1pos,-1,
                            Tipos[i][1],1,tir1pos,1 ];

                Add(slp, [ instr, tir1pos ] );
            od;
        fi; # r <= d-1

        # Next we clear row r apart from g[r][c]
        if c >= 2 then
            # if c = d then Ti already contains t_d(d-1)
            # if c <= d-1 then we swap Ti and Ti-1 so that
            # initially Ti contains t_(d-1)(d-2) and
            # Ti_1 contains t_d(d-1) and then shift back
            # now Ti contains t_c(c-1)
            if not IsZero( g[r][c-1] ) then

                z := - g[r][c-1] * a;

                TransvectionAtAlpha( c, z );

                # Add z times column c of g  to column c-1,
                # add z times column c of u2 to column c-1
                 g{[1..d]}[c-1] :=  g{[1..d]}[c-1] + z *  g{[1..d]}[c];
                u2{[1..d]}[c-1] := u2{[1..d]}[c-1] + z * u2{[1..d]}[c];

                # Copy this in slp
                instr := [ u2pos, 1, tvpos,1];
                Add(slp,[ instr, u2pos ] ); # u2 overwritten



            fi;
            Add(slp, [ [Tipos[c][1],1 ], tcj1pos ] );

            # Now clear the rest of row r
            for j in [ c-2, c-3..1 ] do

                if not IsZero( g[r][j] ) then

                    z := - g[r][j] * a;

                    TransvectionAtAlpha( j+1, z );

                    instr := [ tcj1pos,-1, tvpos,-1, tcj1pos,1, tvpos,1 ];
                    Add(slp, [ instr, tcjzpos ] ); # tcjz

                    # add z times column c of g to column j
                    # add z times column c of u2 to column j
                     g{[1..d]}[j] :=  g{[1..d]}[j] + z *  g{[1..d]}[c];
                    u2{[1..d]}[j] := u2{[1..d]}[j] + z * u2{[1..d]}[c];

                    instr := [ u2pos, 1, tcjzpos,1 ];
                    Add( slp, [ instr, u2pos ] ); # u2 overwritten

                fi;

                # get tcj1 ready for the next iteration
                instr := [tcj1pos,-1, Tipos[j+1][1],-1,
                            tcj1pos,1, Tipos[j+1][1],1 ];
                Add( slp, [ instr, tcj1pos ] );
           od;
        fi;
    od;

    Add( slp, lastline );

    return [slp, [u1, g, u2] ];

end
);



#####################
# PART III
#    Decomposition of Permutation and Diagonal-Matrix
####################

#####
# PermutationMonomialMatrix()
#####
# Find the permutation (in Sym(d) corresponding to a monomial matrix

# Input:    M: A monomial matrix

# Output:    diag: The vector of non-zero entries, where diag[i] is the non-zero
#                entry of row i.
#            perm: The  permutation associated to M
#                     (ie i^perm = j if M_i,j not 0)

InstallGlobalFunction(  PermutationMonomialMatrix,
function( M )

    local zero, d, found, perm, diag, r, j;

    zero := Zero( M[1][1] );
    d := DimensionsMat(M);

    if d[1] <> d[2] then
        Error("Matrix must be square");
        return;
    fi;

    d := d[1];
    found:= BlistList( [1..d], [] );
    perm := [];
    diag := [];

    for r  in [ 1..d ] do

        j := PositionNot( M[r], zero );

        if d < j or found[j]  then
            return false;
        fi;

        diag[r] := M[r][j];

        if PositionNot( M[r], zero, j ) <= d  then
            return false;
        fi;

        found[j] := true;
        perm[r]  := j;

    od;

    return [ diag, PermList(perm) ];

end
);



#####
# PermutationMonomialMatrixNC()
#####
# Find the permutation (in Sym(d) corresponding to a monomial matrix

# Input:    M: A monomial matrix

# Output:    diag: The vector of non-zero entries, where diag[i] is the non-zero
#                entry of row i.
#            perm: The  permutation associated to M
#                     (ie i^perm = j if M_i,j not 0)

InstallGlobalFunction(  PermutationMonomialMatrixNC,
function( M )

    local zero, d, found, perm, diag, r, j;

    zero := Zero( M[1][1] );
    d := DimensionsMat(M);

    d := d[1];
    found:= BlistList( [1..d], [] );
    perm := [];
    diag := [];

    for r  in [ 1..d ] do

        j := PositionNot( M[r], zero );

        if d < j or found[j]  then
            return false;
        fi;

        diag[r] := M[r][j];

        if PositionNot( M[r], zero, j ) <= d  then
            return false;
        fi;

        found[j] := true;
        perm[r]  := j;

    od;

    return [ diag, PermList(perm) ];

end
);



#####
# PermSLP()
#####

# In this function we will transform a monomial matrix w \in SL(d,q) into
# a diagonal matrix diag. Using only the standard-generators s,v,x this
# will lead to a monomial matrix p_sign with only +-1 in non-zero entries
# and p_sign*diag = w (ie diag = p_sign^-1*w )
# Furthermore we will return list slp of instructions which will
# (when evaluated at the LGO standard-generators) yield diag.

# It is sufficient for diag to be diagonal, if the permutation associated
# with w (ie i^\pi_w = j if M_i,j not 0) is the inverse of the permutation
# associated to p_sign (again only to Sym(d) )

# In PermSLP we thus transform \pi_w to () using only { \pi_s, \pi_v, \pi_x }
# In order to know diag without computing all matrix multiplications,
# (we don't know the signs of p_sign), we compute a second permutation
# simultaneously (here using their identification with permutations in Sym(2d)
# and identifying { \pi_s, \pi_v, \pi_x } with {s,v,x} )

# Input:    stdgens:  The LGO standard-generators
#            mat:    A monomial matrix  (ie w)
#            slp:    An already existing list of instructions *optional

# Output:    slp: A list of instructions to evaluate p_sign
#                (if slp was Input then this instructions are added to slp)
#            p_sign: The signed permutation matrix
#            mat: the diagonal matrix diag

InstallGlobalFunction(  PermSLP,
function (arg)

    local    stdgens, s, t, v, vi, perm, slp, instr, cnt, pot, d, fld, i, j,
            spos, tpos, vpos, vipos, p_signpos, xpos, xnpos, x0, x0new,
            Ceiling, mat, p_sign, swr, vwr, viwr, x0wr, xnewwr, twr, p_signwr;

    # There is a Ceil Function in GAP
    # However the one in GAP doesnt work for integers
    Ceiling := function(x)

        if IsInt(x) then
            return x;
        fi;

        return Int(x) + 1;
    end;

    # Check for correct Input
    if Length(arg) >= 2 and IsList(arg[1]) and IsMatrix(arg[2]) then

        stdgens := arg[1];  # the LGO standard generators
        mat := arg[2];        # the monomial matrix

        # Compute the permutation in Sym(d) of mat
        perm := PermutationMonomialMatrix( mat );
        perm := perm[2];
        # Compute {I_d}wr
        p_signwr := MatToWreathProd( stdgens[1]^0 );

        # transforming perm -> () means I_d -> p_sign

        if Length(stdgens) < 1 or not IsMatrix( stdgens[1]) then
            Error("Input: first argument must be the LGO standard generators");
            return;
        fi;

    else

        Error("input: LGO standard generators and a matrix");
        return;
    fi;

    fld := FieldOfMatrixList( stdgens );

    if Length(arg) = 3 then

        # The first 10 entries are the stdgens and their inverses
        slp := arg[3];

        if not IsList(slp) then
            Error("Input: third argument must be a list");
            return;
        fi;

        cnt := HighestSlotOfSLP(slp);

        Info( InfoBruhat, 2, " and additional:  ",7," memory slots ",
                            "in PermSLP()\n");
    else

        # we write an SLP into the variable slp
        # The first 10 entries are the stdgens and the inverses
        # s, t, del, v, x, s^-1, t^-1, del^-1, v^-1, x^-1
        # The entries 11 (resAEM) and 12 (tmpAEM) are used to save AEM-values
        slp := [    [1, 1], [2, 1], [3, 1], [4, 1], [5, 1],
                    [1,-1], [2,-1], [3,-1], [4,-1], [5,-1],
                    [1, 0], [1, 0]    ];

        cnt := 12;

        Info( InfoBruhat, 2, "Memory Usage is: ",19,"  memory slots ",
                            "in PermSLP()\n");
    fi;

    # Initialize the additional memory quota
    Add(slp, [ [1,0], cnt + 1 ] );    p_signpos := cnt + 1;    #13 or 20+3f
    Add(slp, [ [4,1], cnt + 2 ] );    vpos    := cnt + 2;    #14 or 21+3f
    Add(slp, [ [1,0], cnt + 3 ] );    vipos     := cnt + 3;    #15 or 22+3f
    Add(slp, [ [1,1], cnt + 4 ] );    spos      := cnt + 4;    #16 or 23+3f
    Add(slp, [ [5,1], cnt + 5 ] );    xpos      := cnt + 5;    #17 or 24+3f
    Add(slp, [ [5,0], cnt + 6 ] );    xnpos     := cnt + 6;    #18 or 25+3f
    Add(slp, [ [1,0], cnt + 7 ] );    tpos      := cnt + 7;    #19 or 26+3f

    d := Length( stdgens[1] );

    # Define the permutation representations for matrix s in Sym(d) and Sym(2d)
    # We will denote the representation in Sym(d) by s
    s := (1,2);
    swr := MatToWreathProd( stdgens[1] );

    if IsDiagonalMat( mat ) then
        # In order to make it coincide with the other possible output.
        # This is ok since it is Id
        Add( slp, [ [p_signpos,-1] , p_signpos ] );
        return [ slp, [ stdgens[1]^0, mat ] ];
    fi;

    if IsOddInt(d) then
        # For d odd, v is a d-cycle
        v := [ 2..d ];
        Add( v, 1 );
        v := ( PermList(v) )^-1;

        vwr := MatToWreathProd( stdgens[4] );

        # vi is (1,d,d-1,....,2)
         vi  :=  v;
        viwr := vwr;

        Add( slp, [ [4,1], vipos ] );

        for i in [ 1 .. d ] do

            pot := i^perm - i;

            # Need to update perm since pi_{i-1} may change pos of i
              perm   :=   perm   *  vi ^pot;
            p_signwr := p_signwr * viwr^pot;

            # memory slots 11 and 12 are used for resAEM and tmpAEM
            instr := AEM( vipos, 11, 12, pot );
            Append( slp, instr );
            Add( slp, [ [p_signpos,1, 11,1 ], p_signpos ] ); # permpos

            #Compute v_i+1, save command in slp
             vi  :=  s    *  vi;
            viwr := swr * viwr;

            Add(slp,[ [spos,1, vipos,1 ], vipos ] ); # vipos
            # Don't be confused with notation in Paper
            # There we used v1 (which coincides with v^-1)

             s  :=   s ^(  v ^-1 );
            swr :=     swr^( vwr^-1 );
            Add(slp, [ [4,1, spos,1, 9,1 ], spos ] ); # spos

        od;

        p_sign := WreathProdToMat( p_signwr, d, fld );
        mat := p_sign * mat;    # diag

        # diag = p_sign * pm, so return p_sign^-1
        p_sign := p_sign^-1;    # p_sign
        Add(slp,[ [ p_signpos,-1 ], p_signpos ] ); # bpos

        return [slp, [ p_sign, mat ] ];

    else

        # If d is even we do not have a d-cycle in stdgens
        v := [ 3..d ];
        Add( v, 1 ); Add( v, 2 );
        v := PermList( v );
        vwr := MatToWreathProd( stdgens[4] );
        # This corresponds to v in stdgens

         x0  := (1,2,3,4);
        x0wr := MatToWreathProd( stdgens[5] );
        # This corresponds to x in stdgens

        # s and swr are independent from d odd or even, defined above if-case

        # v*s is the d-cycle (1,3,5,7, ...,2,4,6,8, ... d)
        # x0*s is (2,3,4)

        for i in [ 1..d ] do
            if IsOddInt(i) then

                x0new  :=  x0 ^( v  *  s );
                xnewwr := x0wr^(vwr * swr);

                Add( slp, [ [spos,-1, vpos,-1, xpos,1, vpos,1, spos,1 ],
                            xnpos ] );
            fi;

             t  :=  s ^( x0  *  s );
            twr := swr^(x0wr * swr);

            Add(slp, [ [spos,-1, xpos,-1, spos,1, xpos,1, spos,1 ], tpos ] );

             vi  := ( v  *  s  )^-1;
            viwr := (vwr * swr )^-1;

            Add( slp, [ [spos,-1,vpos,-1], vipos ] );

            if IsEvenInt( i^perm -i) then

                pot := (i^perm - i) / 2;

                  perm   :=   perm   *  vi ^pot;
                p_signwr := p_signwr * viwr^pot ;

                instr := AEM( vipos, 11, 12, pot );
                Append( slp, instr );
                Add(slp,[ [p_signpos,1, 11,1], p_signpos ] );

            else

                pot := ( i^perm - i - 1 ) / 2 + Ceiling( Order(vi) / 2 );

                  perm   :=   perm   *  vi ^pot;
                p_signwr := p_signwr * viwr^pot;

                # The memory slots 11 and 12 are res and tmp-slot for AEM
                instr := AEM( vipos, 11,12, pot );
                Append( slp, instr );
                Add(slp,[ [ p_signpos,1, 11,1 ], p_signpos ] );

            fi;

             s  :=  s ^ x0;
            swr := swr^x0wr;

            Add( slp, [ [ xpos,-1, spos,1, xpos,1 ], spos ] );

             v  :=  v  *  t;
            vwr := vwr * twr;

            Add( slp, [ [vpos,1, tpos,1 ], vpos ] );

            if IsEvenInt(i) then
                x0 := x0new;
                x0wr := xnewwr;

                j := xpos;
                xpos := xnpos;
                xnpos := j;
            fi;
        od;

        # We now transfer the permutation p_sign in Sym(2d) back
        # to the signed permutation matrix p_sign
        p_sign := WreathProdToMat( p_signwr, d, fld );
        mat := p_sign * mat;

        p_sign := p_sign^-1;
        Add(slp, [ [ p_signpos,-1 ], p_signpos ] ); # bpos

        return [slp, [ p_sign, mat ] ];
    fi;

end
);


InstallGlobalFunction(  PermSLPNC,
function ( arg )

    local    stdgens, s, t, v, vi, perm, slp, instr, cnt, pot, d, fld, i, j,
            spos, tpos, vpos, vipos, p_signpos, xpos, xnpos, AEMrespos, tmppos,
            x0, x0new, Ceiling, mat, p_sign,
            swr, vwr, viwr, x0wr, xnewwr, twr, p_signwr;

    # There is a Ceil Function in GAP
    # However the one in GAP doesnt work for integers
    Ceiling := function(x)

        if IsInt(x) then
            return x;
        fi;

        return Int(x) + 1;
    end;

    stdgens := arg[1];  # the LGO standard generators
    mat := arg[2];        # the monomial matrix

    # Compute the permutation in Sym(d) of mat
    perm := PermutationMonomialMatrixNC( mat );
    perm := perm[2];
    # Compute {I_d}wr
    p_signwr := MatToWreathProdNC( stdgens[1]^0 );

    # transforming perm -> () means I_d -> p_sign

    fld := FieldOfMatrixList( stdgens );

    if Length( arg ) = 3 then

        # The first 10 entries are the stdgens and their inverses
        slp := arg[3];

        cnt := HighestSlotOfSLP(slp);

        Info( InfoBruhat, 2, " and additional:  ",7," memory slots ",
                            "in PermSLP()\n");
    else

        # we write an SLP into the variable slp
        # The first 10 entries are the stdgens and the inverses
        # s, t, del, v, x, s^-1, t^-1, del^-1, v^-1, x^-1
        # The entries 11 = AEMrespos and 12 = tmppos save AEM-values
        slp := [    [1, 1], [2, 1], [3, 1], [4, 1], [5, 1],
                    [1,-1], [2,-1], [3,-1], [4,-1], [5,-1],
                    [1, 0], [1, 0]    ];

        cnt := 12;

        Info( InfoBruhat, 2, "Memory Usage is: ",19,"  memory slots ",
                            "in PermSLP()\n");
    fi;
    AEMrespos := 11; tmppos := 12;

    # Initialize the additional memory quota
    Add(slp, [ [1,0], cnt + 1 ] );    p_signpos     := cnt + 1;    #13 or 20+3f
    Add(slp, [ [4,1], cnt + 2 ] );    vpos        := cnt + 2;    #14 or 21+3f
    Add(slp, [ [1,0], cnt + 3 ] );    vipos         := cnt + 3;    #15 or 22+3f
    Add(slp, [ [1,1], cnt + 4 ] );    spos          := cnt + 4;    #16 or 23+3f
    Add(slp, [ [5,1], cnt + 5 ] );    xpos          := cnt + 5;    #17 or 24+3f
    Add(slp, [ [5,0], cnt + 6 ] );    xnpos         := cnt + 6;    #18 or 25+3f
    Add(slp, [ [1,0], cnt + 7 ] );    tpos          := cnt + 7;    #19 or 26+3f

    d := Length( stdgens[1] );

    # Define the permutation representations for matrix s in Sym(d) and Sym(2d)
    # We will denote the representation in Sym(d) by s
    s := (1,2);
    swr := MatToWreathProdNC( stdgens[1] );

    if IsDiagonalMat( mat ) then
        Add( slp, [ [ p_signpos,-1 ] , p_signpos ] );
        return [ slp, [ stdgens[1]^0, mat ] ];
    fi;

    if IsOddInt(d) then
        # For d odd, v is a d-cycle
        v := [ 2..d ];
        Add( v, 1 );
        v := ( PermList(v) )^-1;

        vwr := MatToWreathProdNC( stdgens[4] );

        # vi is (1,d,d-1,....,2)
         vi  :=  v;
        viwr := vwr;

        Add( slp, [ [4,1], vipos ] );

        for i in [ 1..d ] do

            pot := i^perm - i;

            # Need to update perm since pi_{i-1} may change pos of i
              perm   :=   perm   *  vi ^pot;
            p_signwr := p_signwr * viwr^pot;

            instr := AEM( vipos, AEMrespos, tmppos, pot );
            Append( slp, instr );
            Add( slp, [ [ p_signpos,1, AEMrespos,1 ], p_signpos ] );

            #Compute v_i+1, save command in slp
             vi  :=  s    *  vi;
            viwr := swr * viwr;

            Add(slp,[ [spos,1, vipos,1 ], vipos ] ); # vipos
            # Don't be confused with notation in Paper
            # There we used v1 (which coincides with v^-1)

             s  :=   s ^(  v ^-1 );
            swr :=     swr^( vwr^-1 );
            Add(slp, [ [4,1, spos,1, 9,1 ], spos ] ); # spos

        od;

        p_sign := WreathProdToMat( p_signwr, d, fld );
        mat := p_sign * mat;    # diag

        # diag = p_sign * pm, so return p_sign^-1
        p_sign := p_sign^-1;    # p_sign
        Add(slp,[ [ p_signpos,-1 ], p_signpos ] ); # bpos

        return [slp, [ p_sign, mat ] ];

    else

        # If d is even we do not have a d-cycle in stdgens
        v := [ 3..d ];
        Add( v, 1 ); Add( v, 2 );
        v := PermList( v );
        vwr := MatToWreathProdNC( stdgens[4] );
        # This corresponds to v in stdgens

         x0  := (1,2,3,4);
        x0wr := MatToWreathProdNC( stdgens[5] );
        # This corresponds to x in stdgens

        # s and swr are independent from d odd or even, defined above if-case

        # v*s is the d-cycle (1,3,5,7, ...,2,4,6,8, ... d)
        # x0*s is (2,3,4)

        for i in [ 1..d ] do
            if IsOddInt(i) then

                x0new  :=  x0 ^( v  *  s );
                xnewwr := x0wr^(vwr * swr);

                Add( slp, [ [spos,-1, vpos,-1, xpos,1, vpos,1, spos,1 ],
                            xnpos ] );
            fi;

             t  :=  s ^( x0  *  s );
            twr := swr^(x0wr * swr);

            Add(slp, [ [spos,-1, xpos,-1, spos,1, xpos,1, spos,1 ], tpos ] );

             vi  := ( v  *  s  )^-1;
            viwr := (vwr * swr )^-1;

            Add( slp, [ [spos,-1,vpos,-1], vipos ] );

            if IsEvenInt( i^perm -i) then

                pot := (i^perm - i) / 2;

                  perm   :=   perm   *  vi ^pot;
                p_signwr := p_signwr * viwr^pot ;

                instr := AEM( vipos, AEMrespos, tmppos, pot );
                Append( slp, instr );
                Add(slp,[ [p_signpos,1, AEMrespos,1], p_signpos ] );

            else

                pot := ( i^perm - i - 1 ) / 2 + Ceiling( Order(vi) / 2 );

                  perm   :=   perm   *  vi ^pot;
                p_signwr := p_signwr * viwr^pot;

                instr := AEM( vipos, AEMrespos,tmppos, pot );
                Append( slp, instr );
                Add(slp,[ [ p_signpos,1, AEMrespos,1 ], p_signpos ] );

            fi;

             s  :=  s ^ x0;
            swr := swr^x0wr;

            Add( slp, [ [ xpos,-1, spos,1, xpos,1 ], spos ] );

             v  :=  v  *  t;
            vwr := vwr * twr;

            Add( slp, [ [vpos,1, tpos,1 ], vpos ] );

            if IsEvenInt(i) then
                x0 := x0new;
                x0wr := xnewwr;

                j := xpos;
                xpos := xnpos;
                xnpos := j;
            fi;
        od;

        # We now transfer the permutation p_sign in Sym(2d) back
        # to the signed permutation matrix p_sign
        p_sign := WreathProdToMat( p_signwr, d, fld );
        mat := p_sign * mat;

        p_sign := p_sign^-1;
        Add(slp, [ [ p_signpos,-1 ], p_signpos ] );

        return [slp, [ p_sign, mat ] ];
    fi;

end
);



#####
# DiagonalDecomposition()
#####

# Writes a list of instructions which evaluated on LGO standard-generators
# yield the diagonal matrix of the input.

# Input:    stdgens:    The LGO standard-generators
#            diag:        A diagonal matrix  (eg diag)
#            slp:    An already existing list of instructions *optional

# Output:    slp: A list of instructions to evaluate diag
#                (if slp was Input then this instructions are added to slp)
#            hres: The the identity matrix

InstallGlobalFunction(  DiagonalDecomposition,
function(arg)

    local     stdgens, delta, x, v, h, hi, him, slp, d, fld, omega,
            lambdai, i, hipos, hiposm, temp, respos, hres, diag, cnt, instr;

    if Length(arg) >= 2 and IsList(arg[1]) and IsMatrix(arg[2]) then

        stdgens := arg[1];  # the LGO standard generators
        diag := arg[2];

        if Length(stdgens) < 1 or not IsMatrix( stdgens[1] ) then
            Error("Input: first argument must be the LGO standard generators");
            return;
        fi;

        if not IsDiagonalMat( diag ) then
            Error("Input: second argument must be a diagonal matrix");
            return;
        fi;
    else
        Error("Input: LGO standard generators and a diagonal matrix");
        return;
    fi;

    fld := FieldOfMatrixList( stdgens );

    if Length(arg) = 3 then

        # The first 10 entries are the stdgens and their inverses
        slp := arg[3];

        if not IsList(slp) then
            Error("Input: third argument must be a list");
            return fail;
        fi;

        cnt := HighestSlotOfSLP( slp );
        Info( InfoBruhat, 2, " and additional:  ",3," memory slots ",
                            "in DiagonalDecomposition()\n");

    else
        # We write an SLP into the variable slp
        # The first 10 entries are the stdgens and their inverses
        # s^-1 t^-1  del^-1    v^-1    x^-1
        # The entries #11 (resAEM),#12 (tmpAEM) are used to save AEM-values
        slp := [     [1, 1], [2, 1], [3, 1], [4, 1], [5, 1],
                    [1,-1], [2,-1], [3,-1], [4,-1], [5,-1],
                    [1, 0], [1, 0] ];

        cnt := 12;
        Info( InfoBruhat, 2, "Memory Usage is: ",3," memory slots ",
                            "in DiagonalDecomposition()\n");
    fi;

    # Define the LGO standard-generators given in the input
    delta     := stdgens[3];
    v        := stdgens[4];
    x        := stdgens[5];

    # Initialize the additional memory quota
    #hi-2
    Add(slp, [ [1,0], cnt + 1 ] );    hiposm := cnt + 1;     #13 or 27+3f
    #hi-1
    Add(slp, [ [1,0], cnt + 2 ] );    hipos := cnt + 2;     #14 or 28+3f
    # result
    Add(slp, [ [1,0], cnt + 3 ] );    respos := cnt + 3;     #15 or 29+3f

    d := Length( diag );
    omega := PrimitiveRoot( fld );

    if diag = One(diag) then
        Add( slp, [ [1,0], respos ] );
        Add( slp, [ respos, 1]);
        return [ slp, diag ];
    fi;

    lambdai := 0;
    hres := diag^0;

    for i in [ 1..d-1 ] do

        lambdai := lambdai + LogFFE( diag[i][i], omega );

        if i = 1 then
            # h_1 = delta
            hi := delta;
            Add(slp,[ [3,1], hipos ] );

        elif i = 2 and IsEvenInt(d) then
            # h_2 = xi * delta * x
            him := delta;
            hi := x^-1 * delta * x;

            Add(slp, [ [3,1], hiposm ] );
            Add(slp, [ [10,1, 3,1, 5,1 ], hipos ] );

        elif IsOddInt(d) then
            # h_i = v h_{i-1} v^-1
            hi := v * hi * v^-1;

            Add(slp, [ [4,1, hipos,1, 9,1 ], hipos ] );

        else
            # h_i = v^-1 h_{i-2} v
            # first we overwrite what is in hiposm
            # since we will not need hiposm any longer
            Add(slp, [ [9,1, hiposm,1, 4,1 ], hiposm ] );
            # now we swap meaning of hipos and hiposm
            temp := hipos;
            hipos := hiposm; # contains h_i
            hiposm := temp;    # contains h_{i-1}
            temp := hi;
            hi := v^-1 * him * v;
            him := temp;

        fi;

        # The memory slots 11 and 12 are res and tmp-slot for AEM
        instr := AEM( hipos, 11, 12, lambdai );
        Append( slp, instr );
        Add( slp, [ [respos,1, 11,1 ], respos ] );

        hres := hres * hi^lambdai;

    od;

    Add( slp, [ respos,1 ] );

    return [ slp, hres ];

end
);


InstallGlobalFunction(  DiagonalDecompositionNC,
function( arg )

    local     stdgens, delta, v, x, h, hi, him, slp, d, fld, omega,
            lambdai, i, temp, hres, diag, cnt, instr,
            hipos, hiposm, respos, AEMrespos, tmppos;

    stdgens := arg[1];  # the LGO standard generators
    diag := arg[2];

    fld := FieldOfMatrixList( stdgens );

    if Length(arg) = 3 then

        # The first 10 entries are the stdgens and their inverses
        slp := arg[3];

        cnt := HighestSlotOfSLP( slp );
        Info( InfoBruhat, 2, " and additional:  ",3," memory slots ",
                            "in DiagonalDecomposition()\n");

    else
        # We write an SLP into the variable slp
        # The first 10 entries are the stdgens and their inverses
        # s^-1 t^-1  del^-1    v^-1    x^-1
        # The entries 11 = AEMrespos and 12 = tmppos save AEM-values
        slp := [     [1, 1], [2, 1], [3, 1], [4, 1], [5, 1],
                    [1,-1], [2,-1], [3,-1], [4,-1], [5,-1],
                    [1, 0], [1, 0] ];

        cnt := 12;
        Info( InfoBruhat, 2, "Memory Usage is: ",3," memory slots ",
                            "in DiagonalDecomposition()\n");
    fi;
    AEMrespos := 11; tmppos := 12;

    # Define the LGO standard-generators given in the input

    delta     := stdgens[3];
    v        := stdgens[4];
    x        := stdgens[5];

    # Initialize the additional memory quota
    #hi-2
    Add(slp, [ [1,0], cnt + 1 ] );    hiposm := cnt + 1;     #13 or 27+3f
    #hi-1
    Add(slp, [ [1,0], cnt + 2 ] );    hipos := cnt + 2;     #14 or 28+3f
    # result
    Add(slp, [ [1,0], cnt + 3 ] );    respos := cnt + 3;     #15 or 29+3f

    d := Length( diag );
    omega := PrimitiveElement( fld );

    if diag = One( diag ) then
        Add( slp, [ [1,0], respos ] );
        Add( slp, [ respos, 1] );
        return [ slp, diag ];
    fi;

    lambdai := 0;
    hres := diag^0;

    for i in [ 1..d-1 ] do

        lambdai := lambdai + LogFFE( diag[i][i], omega );

        if i = 1 then
            # h_1 = delta
            hi := delta;
            Add(slp,[ [3,1], hipos ] );

        elif i = 2 and IsEvenInt( d ) then
            # h_2 = xi * delta * x
            him := delta;
            hi := x^-1 * delta * x;

            Add(slp, [ [3,1], hiposm ] );
            Add(slp, [ [10,1, 3,1, 5,1 ], hipos ] );

        elif IsOddInt( d ) then
            # h_i = v h_{i-1} v^-1
            hi := v * hi * v^-1;

            Add(slp, [ [4,1, hipos,1, 9,1 ], hipos ] );

        else
            # h_i = v^-1 h_{i-2} v
            # first we overwrite what is in hiposm
            # since we will not need hiposm any longer
            Add(slp, [ [9,1, hiposm,1, 4,1 ], hiposm ] );
            # now we swap meaning of hipos and hiposm
            temp := hipos;
            hipos := hiposm; # contains h_i
            hiposm := temp;    # contains h_{i-1}
            temp := hi;
            hi := v^-1 * him * v;
            him := temp;

        fi;

        instr := AEM( hipos, AEMrespos, tmppos, lambdai );
        Append( slp, instr );
        Add( slp, [ [respos,1, AEMrespos,1 ], respos ] );

        hres := hres * hi^lambdai;

    od;

    Add( slp, [ respos,1 ] );

    return [ slp, hres ];

end
);



####################
# PART IV
#    Main Functions. Constructs slp for the StraightLineProgram
#####################

#####
# BruhatDecompositionSL()
#####

# Uses UnipotentDecomposition(), PermSLP() and DiagonalDecomposition()
# to write a matrix g \in SL(d,q) as g = u1^-1*p_sign*diag*u2^-2
# where u1,u2 are lower unitriangular matrices, p_sign a monomial matrix
# with only +1 and -1 as non-zero entries and diag a diagonal matrix.
# It furthermore yields an SLP that reurns the above matrices if evaluated
# at the LGO standard-generators.

# Input: stdgens: The LGO standard-generators
#        g:    A matrix in SL(d,q)

# Output: pgr: A SLP to compute u1,u2,p_sign and diag
#        and the matrices u1, u2, p_sign and diag itself

InstallGlobalFunction(  BruhatDecompositionSL,
function(stdgens, g)

    local slp, u1, pm, u2, p_sign, diag, res1, res2, res3, lastline, line, pgr;

    # We write an SLP into the variable slp
    # The first 10 entries are the stdgens and their inverses
    # s, t, del, v, x, s^-1, t^-1, del^-1, v^-1, x^-1

    Info( InfoBruhat, 1,
            "returns an SLP to generate u1, u2, p_sign, diag\n"    );

    # Compute the matrices u1,u2 of Bruhat-Decomposition and the instructions
    # for an SLP that compute u1 and u2
    res1 := UnipotentDecomposition( stdgens, g);

    slp := res1[1];
    u1 := res1[2][1];
    pm := res1[2][2];    # the monomial matrix w
    u2 := res1[2][3];

    lastline := ShallowCopy( slp[ Length(slp) ] ); # remember famous last words
    # Since entries of the form [list1,list2] should only occur at the end
    Remove(slp);

    # Decompose w in to a signed Permutation-Matrix generated by <s,v,x>
    # and a Diagonal-Matrix diag.

    res2 := PermSLP(stdgens, pm, slp );

    slp := ShallowCopy(res2[1]);
    p_sign := res2[2][1];
    diag := res2[2][2];
    # Now w = p_sign * diag
    # and p_sign is can be evaluated as word in < s, v, x > using slp.

    # Make again all entries of slp admissible for SLP
    # We inverted a Monomial-Matrix in PermSLP to get the proper result.
    # Thus we have to copy a little variaton at the end of our final slp
    # (else we would display a twice inverted matrix where we wanted once)
    line := slp[ Length(slp) ];
    Append(lastline,[ [line[1][1], 1] ]);

    # Determine the SLP for the Diagonal-Matrix
    res3 := DiagonalDecomposition(stdgens, diag, slp);
    slp := res3[1];

    # Here the last entry is of admissible form. Just add it to the end.
    Append( lastline, [ slp[ Length(slp)] ] ); # remember famous last words
    Remove( slp );
    Append( slp, [lastline] );

    Info( InfoBruhat, 2, "The Total Memory Usage is: "
                        , HighestSlotOfSLP(slp), " memory slots\n" );

    pgr := MakeSLP(slp,5);

    # The result R of pgr satisfies:
    #    R[1]^-1*R[3]*R[4]*R[2]^-1    and
    #    R[1] = u1, R[2] = u2, R[3] = p_sign, R[4] = diag
    return [pgr, [ u1, u2, p_sign, diag ]];

end
);


InstallGlobalFunction(  BruhatDecompositionSLNC,
function(stdgens, g)

    local slp, u1, pm, u2, p_sign, diag, res1, res2, res3, lastline, line, pgr;

    # We write an SLP into the variable slp
    # The first 10 entries are the stdgens and their inverses
    # s, t, del, v, x, s^-1, t^-1, del^-1, v^-1, x^-1

    Info( InfoBruhat, 1,
            "returns an SLP to generate u1, u2, p_sign, diag\n"    );

    # Compute the matrices u1,u2 of Bruhat-Decomposition and the instructions
    # for an SLP that compute u1 and u2
    res1 := UnipotentDecompositionNC( stdgens, g);

    slp := res1[1];
    u1 := res1[2][1];
    pm := res1[2][2];    # the monomial matrix w
    u2 := res1[2][3];

    lastline := ShallowCopy( slp[ Length(slp) ] ); # remember famous last words
    # Since entries of the form [list1,list2] should only occur at the end
    Remove(slp);

    # Decompose w in to a signed Permutation-Matrix generated by <s,v,x>
    # and a Diagonal-Matrix diag.

    res2 := PermSLPNC(stdgens, pm, slp );

    slp := ShallowCopy( res2[1] );
    p_sign := res2[2][1];
    diag := res2[2][2];
    # Now w = p_sign * diag
    # and p_sign is can be evaluated as word in < s, v, x > using slp.

    # Make again all entries of slp admissible for SLP
    # We inverted a Monomial-Matrix in PermSLP to get the proper result.
    # Thus we have to copy a little variaton at the end of our final slp
    # (else we would display a twice inverted matrix where we wanted once)
    line := slp[ Length(slp) ];
    Append(lastline,[ [line[1][1], 1] ]);

    # Determine the SLP for the Diagonal-Matrix
    res3 := DiagonalDecompositionNC( stdgens, diag, slp );
    slp := res3[1];

    # Here the last entry is of admissible form. Just add it to the end.
    Append( lastline, [ slp[ Length(slp) ] ] ); # remember famous last words
    Remove( slp );
    Append( slp, [ lastline ] );

    Info( InfoBruhat, 2, "The Total Memory Usage is: "
                        , HighestSlotOfSLP(slp), " memory slots\n" );


    pgr := MakeSLPNC( slp, 5 );

    # The result R of pgr satisfies:
    #    R[1]^-1*R[3]*R[4]*R[2]^-1    and
    #    R[1] = u1, R[2] = u2, R[3] = p_sign, R[4] = diag
    return [pgr, [ u1, u2, p_sign, diag ] ];

end
);



#####
# BruhatDecompositionSLWithTi()
#####

# As BruhatDecompositionSL() but replace UnipotentDecomposition()
# by UnipotentDecompositionWithTi.

# Input: stdgens: The LGO standard-generators
#        g:    A matrix in SL(d,q)

# Output: pgr: A SLP to compute u1,u2,p_sign, diag
#                and all transvections t_{i,i-1}(omega^ell)
#            the matrices u1, u2, p_sign and diag itself

InstallGlobalFunction(  BruhatDecompositionSLWithTi,
function(stdgens, g)

    local     slp, u1, pm, u2, p_sign, diag, res1, res2, res3,
            lastline, line, transvections, pgr;

    # We write an SLP into the variable slp
    # The first 10 entries are the stdgens and their inverses
    # s, t, del, v, x, s^-1, t^-1, del^-1, v^-1, x^-1

    Info( InfoBruhat, 1,
            "returns an SLP to generate u1, u2, p_sign, diag\n"    );

    # Compute the matrices u1,u2 of Bruhat-Decomposition and the instructions
    # for an SLP that compute u1 and u2
    res1 := UnipotentDecompositionWithTi( stdgens, g);

    slp := res1[1];
    u1 := res1[2][1];
    pm := res1[2][2];    # the monomial matrix w
    u2 := res1[2][3];

    lastline := ShallowCopy( slp[ Length(slp) ] ); # remember famous last words
    transvections := ShallowCopy( lastline{[ 3..Length(lastline) ]} );
    lastline := lastline{[ 1..2 ]};

    # Since entries of the form [list1,list2] should only occur at the end
    Remove(slp);

    # Decompose w in to a signed Permutation-Matrix generated by <s,v,x>
    # and a Diagonal-Matrix diag.

    res2 := PermSLP(stdgens, pm, slp );

    slp := ShallowCopy(res2[1]);
    p_sign := res2[2][1];
    diag := res2[2][2];
    # Now w = p_sign * diag
    # and p_sign is can be evaluated as word in < s, v, x > using slp.

    # Make again all entries of slp admissible for SLP
    # We inverted a Monomial-Matrix in PermSLP to get the proper result.
    # Thus we have to copy a little variaton at the end of our final slp
    # (else we would display a twice inverted matrix where we wanted once)
    line := slp[ Length(slp) ];
    Append(lastline,[ [line[1][1], 1] ]);

    # Determine the SLP for the Diagonal-Matrix
    res3 := DiagonalDecomposition(stdgens, diag, slp);
    slp := res3[1];

    # Here the last entry is of admissible form. Just add it to the end.
    Append( lastline, [ slp[ Length(slp)] ] ); # remember famous last words
    Append( lastline, transvections );
    Remove( slp );
    Append( slp, [lastline] );

    Info( InfoBruhat, 2, "The Total Memory Usage is: "
                        , HighestSlotOfSLP(slp), " memory slots\n" );


    pgr := MakeSLP(slp,5);

    # The result R of pgr satisfies:
    #    R[1]^-1*R[3]*R[4]*R[2]^-1    and
    #    R[1] = u1, R[2] = u2, R[3] = p_sign, R[4] = diag
    # Furthermore R[5] ... R[ Length(R) ] are the transvections.
    return [pgr, [ u1, u2, p_sign, diag ]];

end
);


InstallGlobalFunction(  BruhatDecompositionSLWithTiNC,
function(stdgens, g)

    local     slp, u1, pm, u2, p_sign, diag, res1, res2, res3,
            lastline, line, transvections, pgr;

    # We write an SLP into the variable slp
    # The first 10 entries are the stdgens and their inverses
    # s, t, del, v, x, s^-1, t^-1, del^-1, v^-1, x^-1

    Info( InfoBruhat, 1,
            "returns an SLP to generate u1, u2, p_sign, diag\n"    );

    # Compute the matrices u1,u2 of Bruhat-Decomposition and the instructions
    # for an SLP that compute u1 and u2
    res1 := UnipotentDecompositionWithTiNC( stdgens, g);

    slp := res1[1];
    u1 := res1[2][1];
    pm := res1[2][2];    # the monomial matrix w
    u2 := res1[2][3];

    lastline := ShallowCopy( slp[ Length(slp) ] ); # remember famous last words
    transvections := ShallowCopy( lastline{[ 3..Length(lastline) ]} );
    lastline := lastline{[ 1..2 ]};

    # Since entries of the form [list1,list2] should only occur at the end
    Remove(slp);

    # Decompose w in to a signed Permutation-Matrix generated by <s,v,x>
    # and a Diagonal-Matrix diag.

    res2 := PermSLPNC(stdgens, pm, slp );

    slp := ShallowCopy(res2[1]);
    p_sign := res2[2][1];
    diag := res2[2][2];
    # Now w = p_sign * diag
    # and p_sign is can be evaluated as word in < s, v, x > using slp.

    # Make again all entries of slp admissible for SLP
    # We inverted a Monomial-Matrix in PermSLP to get the proper result.
    # Thus we have to copy a little variaton at the end of our final slp
    # (else we would display a twice inverted matrix where we wanted once)
    line := slp[ Length(slp) ];
    Append( lastline, [ [ line[1][1],1 ] ] );

    # Determine the SLP for the Diagonal-Matrix
    res3 := DiagonalDecompositionNC( stdgens, diag, slp );
    slp := res3[1];

    # Here the last entry is of admissible form. Just add it to the end.
    Append( lastline, [ slp[ Length(slp)] ] ); # remember famous last words
    Append( lastline, transvections );
    Remove( slp );
    Append( slp, [lastline] );

    Info( InfoBruhat, 2, "The Total Memory Usage is: "
                        , HighestSlotOfSLP(slp), " memory slots\n" );


    pgr := MakeSLPNC( slp, 5 );

    # The result R of pgr satisfies:
    #    R[1]^-1*R[3]*R[4]*R[2]^-1    and
    #    R[1] = u1, R[2] = u2, R[3] = p_sign, R[4] = diag
    # Furthermore R[5] ... R[ Length(R) ] are the transvections.
    return [pgr, [ u1, u2, p_sign, diag ]];

end
);

