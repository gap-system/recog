######################################
# BruhatDecompositionSU.gi
######################################

######################################
# Concept:
#    This implementation follows the ideas of
#    "Bruhat Decomposition in unitary and symplectic groups over finite fields"
#    by Daniel Rademacher.
#    In the following all references will mean this paper
#    and in case we differ from this paper (due to readability or bug-fixing)
#    this will also be remarked.
#
#    Let g \in SLp(d,p^f)
#    Bruhat Decomposition computes g = u1 * w * u2, where
#         - u1,u2 are lower triangular matrices
#         - w is monomial matrix
#
#    In this algorithm we want to compute the Bruhat-Decomposition of g
#    and give g (respectively u1,w and u2) as word in the so called
#    "LGO standard generators".
#
#    1) While computing u1 (resp u2) with some kind of Gauß-Algorithm,
#    we express the matrices as product of so called Siegel transformations
#
#    2) In a further step we will decompose the monomial Matrix w in
#    a monomial matrix p_sign and a diagonal Matrix diag.
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
# UnitriangularDecompositionSp
#####

InstallGlobalFunction(  UnitriangularDecompositionSp,
function( arg )

    local u1, u2, d, fld, f, alpha, c, r, j, a, z, i, Mul, g, ell, slp, hs, tmppos, AEMrespos, u1pos, u2pos, tvpos, T2pos, T3pos, T4pos, tmppos2, uipos, q, f2, TransvecAtAlpha2, TransvecAtAlpha3, TransvecAtAlpha4, test, ShiftTransvection3ByJ, ShiftTransvection3ByI, ShiftTransvection4, ShiftTransvection2ByJ, ShiftTransvection2ByI, stdgens;

    #####
    # TransvectionAtAlpha2()
    #####

    TransvecAtAlpha2 := function( alpha )

        local cc, ell, instr;

        # if omega = 1 then we overwrite the position for tv with Ti(1)
        if IsOne( alpha ) then
            Add(slp, [ [ T2pos[1], 1 ], tvpos ] );
            return;
        fi;

        cc := CoefficientsPrimitiveElement( fld, alpha );
        instr := [];

        for ell in [ 1..Length(cc) ] do

            if not IsZero( cc[ell] ) then
                Append( instr, [ T2pos[ell], Int(cc[ell]) ] );
            fi;
        od;

        if Length( instr ) = 0 then
            Error("TransvecAtAlpha2: this should not happen");
        fi;

        Add( slp, [ instr,tvpos ] );

        return;

    end;

    #####
    # ShiftTransvection2ByI()
    #####

    ShiftTransvection2ByI := function(i)

        local instr;

        instr := AEM( 4, AEMrespos, tmppos, i-2 );
        Append( slp, instr );
        Add( slp, [ [ AEMrespos, -1, tvpos , 1, AEMrespos, 1 ], tvpos ] );

    end;

    #####
    # ShiftTransvection2ByJ()
    #####

    ShiftTransvection2ByJ := function(i, abnr)

        local ui;

        ui := (d/2)-2;

        while ui-i+1-(d/2-abnr) > 0 do
            Add(slp, [[uipos[ui-(d/2-abnr)],1,tvpos,1,uipos[ui-(d/2-abnr)],1],tvpos]);
            ui := ui-1;
        od;

    end;

    #####
    # TransvectionAtAlpha3()
    #####

    TransvecAtAlpha3 := function( alpha )

        local cc, ell, instr;

        # if omega = 1 then we overwrite the position for tv with Ti(1)
        if IsOne( alpha ) then
            Add(slp, [ [ T3pos[1], 1 ], tvpos ] );
            return;
        fi;

        cc := CoefficientsPrimitiveElement( fld, alpha );
        instr := [];

        for ell in [ 1..Length(cc) ] do

            if not IsZero( cc[ell] ) then
                Append( instr, [ T3pos[ell], Int(cc[ell]) ] );
            fi;
        od;

        if Length( instr ) = 0 then
            Error("TransvecAtAlpha3: this should not happen");
        fi;

        Add( slp, [ instr,tvpos ] );

        return;

    end;

    #####
    # ShiftTransvection3ByI()
    #####

    ShiftTransvection3ByI := function(i)

        local ui;

        i := d-i+1;
        ui := 1;

        while ui < i do
            Add(slp, [[uipos[ui],1,tvpos,1,uipos[ui],1],tvpos]);
            ui := ui+1;
        od;

    end;

    #####
    # ShiftTransvection3ByJ()
    #####

    ShiftTransvection3ByJ := function(i)

        local instr;

        i := i-1;

        Add(slp,[[4,1,5,1],tmppos2]);
        instr := AEM( tmppos2, AEMrespos, tmppos, i-1 );
        Append( slp, instr );
        Add( slp, [ [ AEMrespos, -1, tvpos , 1, AEMrespos, 1 ], tvpos ] );

    end;

    #####
    # TransvectionAtAlpha4()
    #####

    TransvecAtAlpha4 := function( alpha )

        local cc, ell, instr, w, delta, specialalpha, VS, basis;

        delta := stdgens[3];
        w := delta[1][1];
        basis := [];
        for ell in [1..f] do
            Add(basis,w^(2*ell));
        od;

        VS := VectorSpace(GF(Characteristic(fld)),basis);

        cc := CoefficientsPrimitiveElementS( fld, alpha, Basis(VS,basis));
        instr := [];

        for ell in [ 1..Length(cc) ] do

            if not IsZero( cc[ell] ) then
                Append( instr, [ T4pos[ell], Int(cc[ell]) ] );
            fi;
        od;

        if Length( instr ) = 0 then
            Error("TransvecAtAlpha4: this should not happen");
        fi;

        Add( slp, [ instr,tvpos ] );

        return;

    end;

    #####
    # ShiftTransvection4()
    #####

    ShiftTransvection4 := function(i)
        local instr;

        i := d-i+1;

        if (i<d+1 ) then
            instr := AEM( 4, AEMrespos, tmppos, i-1 );
            Append( slp, instr );
            Add( slp, [ [ AEMrespos, -1, tvpos , 1, AEMrespos, 1 ], tvpos ] );
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
        # The first 12 entries are the stdgens and the inverses
        # s, t, del, v, x, s^-1, t^-1, del^-1, v^-1, x^-1
        slp := [    [1,1], [2,1], [3,1], [4,1], [5,1], [6,1],
                    [1,-1],[2,-1],[3,-1],[4,-1],[5,-1], [6,-1]   ];
    fi;

    d := Length( g );
    fld := FieldOfMatrixList( stdgens );

    # To create an MSLP, we allocate all the memory needed at the beginning.
    Add( slp, [1,0] );        tmppos       := Length(slp);    #15
    Add( slp, [1,0] );        AEMrespos    := Length(slp);    #16
    Add( slp, [1,0] );        u1pos        := Length(slp);    #17
    Add( slp, [1,0] );        u2pos        := Length(slp);    #18
    Add( slp, [1,0] );        tvpos        := Length(slp);    #19
    Add( slp, [1,0] );        tmppos2      := Length(slp);    #20


    u1 := MutableCopyMat( One(g) );
    u2 := MutableCopyMat( One(g) );

    # If g is already a monomial matrix return u_1 = u_2 = I_d
    if TestIfMonomial( g ) then
        Add( slp, [ [1,0],[1,0] ] );
        return [ slp, [u1,g,u2] ];
    fi;

    f := LogInt(Size(fld), Characteristic(fld)); #ie q=p^f

    hs := HighestSlotOfSLP(slp);

    # We create the help variables for the block top left or bottom right
    T2pos := [ hs + 1 .. hs + f ];

    hs := hs + f;

    for ell in [ 1..f ] do
        Add(slp, [1,0] );
    od;

    for ell in [0..f-1] do

        Add(slp, [ [3, -ell, 4, -2, 3, ell, 4 ,2 ], tmppos ] );
        Add(slp, [ [5,1,1,1,tmppos, 1, 6, 1, tmppos, -1,1,-1,5,-1 ], T2pos[ell+1] ] );

    od;

    # We create the help variables for the block in the bottom left
    T3pos := [ hs + 1 .. hs + f ];

    hs := hs + f;

    for ell in [ 1..f ] do
        Add(slp, [1,0] );
    od;

    for ell in [0..f-1] do

        Add(slp, [ [3, -ell, 4, -2, 3, ell, 4 ,2 ], tmppos ] );
        Add(slp, [ [tmppos, 1, 6, 1, tmppos, -1], T3pos[ell+1] ] );

    od;

    # We create the help variables for the diagonal
    T4pos := [ hs + 1 .. hs + f ];

    hs := hs + f ;

    for ell in [ 1..f ] do
        Add(slp, [1,0] );
    od;

    for ell in [1..f] do

        Add(slp, [ [1,-1,3,ell,2,-1,3,-ell,1,1], T4pos[ell] ] );

    od;

    # We create the help variables for the shift

    uipos := [ hs + 1 .. (hs + (d/2)-2) ];

    hs := hs + ((d/2)-2) ;

    for ell in [ 1 .. ((d/2)-2)  ] do
        Add(slp, [1,0] );
    od;

    Add( slp, [[5,1],uipos[1]]);

    for ell in [2..((d/2)-2) ] do
            Add( slp, [ [ 4, -1, uipos[ell-1] , 1, 4, 1 ], uipos[ell] ] );
    od;

    ############
    # Tests
    ############

    #test :=PseudoRandom(fld);

    #Display(test);

    #TransvecAtAlpha2(test);
    #ShiftTransvection2ByI(5);
    #ShiftTransvection2ByJ(2, 5);

    #TransvecAtAlpha4(test);
    #ShiftTransvection4(7);

    #TransvecAtAlpha3(test);
    #ShiftTransvection3ByJ(4);
    #ShiftTransvection3ByI(10);

    #Add(slp, [[tvpos,1],tvpos]);

    #return MakeSLP(slp,7);

    ############
    # Main
    ############

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

        a := g[r][c]^-1;

        if r <= d-1 then

            if not IsZero( g[r+1][c] ) then

                z := - g[r+1][c] * a;

                # add z times row r of g  to row r+1
                # add z times row r of u1  to row r+1
                # g[r+1] :=  g[r+1] + z *  g[r];
                # u1[r+1] := u1[r+1] + z * u1[r];
                # Mul := List( One(SU(d,Size(fld))), ShallowCopy );

                if (r+r+1 <> d+1) then

                    if r in [1..d/2] and r+1 in [1..d/2] then
                        TransvecAtAlpha2(z);
                        ShiftTransvection2ByI(r+1);
                        ShiftTransvection2ByJ(r, r+1);
                    else
                        TransvecAtAlpha2(-z);
                        ShiftTransvection2ByI(d-r+1);
                        ShiftTransvection2ByJ(d-r,d-r+1);
                    fi;

                    #Mul[r+1][r] := z;
                    g[r+1] :=  g[r+1] + z *  g[r];
                    u1[r+1] := u1[r+1] + z * u1[r];

                    #Mul[d-r+1][d-r] := -z;
                    g[d-r+1] :=  g[d-r+1] + (-z) *  g[d-r];
                    u1[d-r+1] := u1[d-r+1] + (-z) * u1[d-r];
                else

                    TransvecAtAlpha4(z);
                    ShiftTransvection4(r+1);

                    # Mul[r+1][r] := z;
                    g[r+1] :=  g[r+1] + z *  g[r];
                    u1[r+1] := u1[r+1] + z * u1[r];
                fi;

                Add(slp,[[tvpos,1,u1pos,1],u1pos]);

                #g := Mul * g;
                #u1 := Mul * u1;

            fi;


            # Second: Clear the rest of column c
            for i in [ r+2..d ] do

                if not IsZero(g[i][c]) then

                    z := -g[i][c] * a;

                    # add z times row r of g  to row i
                    # add z times row r of u1  to row i
                    #g[i] := g[i] + z*g[r];
                    #u1[i] := u1[i] + z*u1[r];
                    #Mul := List( One(SU(d,Size(fld))), ShallowCopy );

                    if (i+r <> d+1) then
                        if(r <= d/2) then
                            if (i <= d/2) then

                                if i in [1..d/2] and r in [1..d/2] then
                                    TransvecAtAlpha2(z);
                                    ShiftTransvection2ByI(i);
                                    ShiftTransvection2ByJ(r, i);
                                elif i in [((d/2)+1)..d] and r in [((d/2)+1)..d] then
                                    TransvecAtAlpha2(-z);
                                    ShiftTransvection2ByJ(d-r+1);
                                    ShiftTransvection2ByI(d-i+1,d-r+1);
                                elif i+r < d+1 then
                                    TransvecAtAlpha3(z);
                                    ShiftTransvection3ByJ(d-i+1);
                                    ShiftTransvection3ByI(d-r+1);
                                else
                                    TransvecAtAlpha3(z);
                                    ShiftTransvection3ByJ(r);
                                    ShiftTransvection3ByI(i);
                                fi;

                                #Mul[i][r] := z;
                                g[i] := g[i] + z*g[r];
                                u1[i] := u1[i] + z*u1[r];

                                #Mul[d-r+1][d-i+1] := -z;
                                g[d-r+1] := g[d-r+1] + (-z)*g[d-i+1];
                                u1[d-r+1] := u1[d-r+1] + (-z)*u1[d-i+1];
                            else

                                if i in [1..d/2] and r in [1..d/2] then
                                    TransvecAtAlpha2(z);
                                    ShiftTransvection2ByI(i);
                                    ShiftTransvection2ByJ(r, i);
                                elif i in [((d/2)+1)..d] and r in [((d/2)+1)..d] then
                                    TransvecAtAlpha2(-z);
                                    ShiftTransvection2ByJ(d-r+1);
                                    ShiftTransvection2ByI(d-i+1,d-r+1);
                                elif i+r < d+1 then
                                    TransvecAtAlpha3(z);
                                    ShiftTransvection3ByJ(d-i+1);
                                    ShiftTransvection3ByI(d-r+1);
                                else
                                    TransvecAtAlpha3(z);
                                    ShiftTransvection3ByJ(r);
                                    ShiftTransvection3ByI(i);
                                fi;

                                #Mul[i][r] := z;
                                g[i] := g[i] + z*g[r];
                                u1[i] := u1[i] + z*u1[r];

                                #Mul[d-r+1][d-i+1] := z;
                                g[d-r+1] := g[d-r+1] + z*g[d-i+1];
                                u1[d-r+1] := u1[d-r+1] + z*u1[d-i+1];
                            fi;
                        else

                            if i in [1..d/2] and r in [1..d/2] then
                                TransvecAtAlpha2(z);
                                ShiftTransvection2ByI(i);
                                ShiftTransvection2ByJ(r, i);
                            elif i in [((d/2)+1)..d] and r in [((d/2)+1)..d] then
                                TransvecAtAlpha2(-z);
                                ShiftTransvection2ByI(d-r+1);
                                ShiftTransvection2ByJ(d-i+1,d-r+1);
                            elif i+r < d+1 then
                                TransvecAtAlpha3(z);
                                ShiftTransvection3ByJ(d-i+1);
                                ShiftTransvection3ByI(d-r+1);
                            else
                                TransvecAtAlpha3(z);
                                ShiftTransvection3ByJ(r);
                                ShiftTransvection3ByI(i);
                            fi;

                            #Mul[i][r] := z;
                            g[i] := g[i] + z*g[r];
                            u1[i] := u1[i] + z*u1[r];

                            #Mul[d-r+1][d-i+1] := -z;
                            g[d-r+1] := g[d-r+1] + (-z)*g[d-i+1];
                            u1[d-r+1] := u1[d-r+1] + (-z)*u1[d-i+1];

                        fi;
                    else

                        TransvecAtAlpha4(z);

                        if i > r then
                            ShiftTransvection4(i);
                        else
                            ShiftTransvection4(r);
                        fi;

                        #Mul[i][r] := z;
                        g[i] := g[i] + z*g[r];
                        u1[i] := u1[i] + z*u1[r];
                    fi;

                    Add(slp,[[tvpos,1,u1pos,1],u1pos]);

                    #g := Mul * g;
                    #u1 := Mul * u1;

                fi;


            od;

        fi;


        # Step Two: Clear all entries in row r apart from g[r][c]
        # This coincides with multiplying t_{c,j} from right.
        if c >= 2 then

            if not IsZero( g[r][c-1] ) then

                z := -g[r][c-1] * a;

                # add z times column c of g to column c-1
                # add z times column c of u2 to column c-1
                #g{[ 1..d ]}[ c-1 ] := g{[ 1..d ]}[ c-1 ] + z * g{[1..d]}[c];
                #u2{[1..d]}[c-1] := u2{[1..d]}[c-1] + z * u2{[1..d]}[c];

                #Mul := List( One(G), ShallowCopy );

                if (c+c-1 <>  d+1) then
                    if (c-1 > d/2) then
                        #Mul[c][c-1] := z;
                        if c in [1..d/2] and c-1 in [1..d/2] then
                            TransvecAtAlpha2(z);
                            ShiftTransvection2ByI(c);
                            ShiftTransvection2ByJ(c-1, c);
                        else
                            TransvecAtAlpha2(-z);
                            ShiftTransvection2ByI(d-c+2);
                            ShiftTransvection2ByJ(d-c+1,d-c+2);
                        fi;

                        g{[ 1..d ]}[ c-1 ] := g{[ 1..d ]}[ c-1 ] + z * g{[1..d]}[c];
                        u2{[1..d]}[c-1] := u2{[1..d]}[c-1] + z * u2{[1..d]}[c];

                        #Mul[d-c+2][d-c+1] := -z;
                        g{[ 1..d ]}[ d-c+1 ] := g{[ 1..d ]}[ d-c+1 ] + (-z) * g{[1..d]}[d-c+2];
                        u2{[1..d]}[d-c+1] := u2{[1..d]}[d-c+1] + (-z) * u2{[1..d]}[d-c+2];
                    else
                        #Mul[c][c-1] := z;
                        g{[ 1..d ]}[ c-1 ] := g{[ 1..d ]}[ c-1 ] + z * g{[1..d]}[c];
                        u2{[1..d]}[c-1] := u2{[1..d]}[c-1] + z * u2{[1..d]}[c];

                        #Mul[d-c+2][d-c+1] := z;
                        g{[ 1..d ]}[ d-c+1 ] := g{[ 1..d ]}[ d-c+1 ] + z * g{[1..d]}[d-c+2];
                        u2{[1..d]}[d-c+1] := u2{[1..d]}[d-c+1] + z * u2{[1..d]}[d-c+2];
                    fi;
                else
                    TransvecAtAlpha4(z);
                    ShiftTransvection4(c);

                    #Mul[c][c-1] := z;
                    g{[ 1..d ]}[ c-1 ] := g{[ 1..d ]}[ c-1 ] + z * g{[1..d]}[c];
                    u2{[1..d]}[c-1] := u2{[1..d]}[c-1] + z * u2{[1..d]}[c];
                fi;

                Add(slp,[[u2pos,1,tvpos,1],u2pos]);

                #g := g * Mul;
                #u2 := u2 * Mul;

            fi;


            # Now clear the rest of row r
            for j in [ c-2, c-3..1 ] do

                if not IsZero( g[r][j] ) then

                    z := - g[r][j] * a;

                    # add z times column c of g to column j
                    # add z times column c of u2 to column j
                    # g{[1..d]}[j] :=  g{[1..d]}[j] + z *  g{[1..d]}[c];
                    #u2{[1..d]}[j] := u2{[1..d]}[j] + z * u2{[1..d]}[c];

                    #Mul := List( One(G), ShallowCopy );

                    if (c+j <>  d+1) then
                        if (j > d/2) then

                            if c in [1..d/2] and j in [1..d/2] then
                                TransvecAtAlpha2(z);
                                ShiftTransvection2ByI(c);
                                ShiftTransvection2ByJ(j, c);
                            elif c in [((d/2)+1)..d] and j in [((d/2)+1)..d] then
                                TransvecAtAlpha2(-z);
                                ShiftTransvection2ByI(d-j+1);
                                ShiftTransvection2ByJ(d-c+1,d-j+1);
                            elif c+j < d+1 then
                                TransvecAtAlpha3(z);
                                ShiftTransvection3ByJ(d-c+1);
                                ShiftTransvection3ByI(d-j+1);
                            else
                                TransvecAtAlpha3(z);
                                ShiftTransvection3ByJ(j);
                                ShiftTransvection3ByI(c);
                            fi;

                            #Mul[c][j] := z;
                            g{[1..d]}[j] :=  g{[1..d]}[j] + z *  g{[1..d]}[c];
                            u2{[1..d]}[j] := u2{[1..d]}[j] + z * u2{[1..d]}[c];

                            #Mul[d-j+1][d-c+1] := -z;
                            g{[1..d]}[d-c+1] :=  g{[1..d]}[d-c+1] + (-z) *  g{[1..d]}[d-j+1];
                            u2{[1..d]}[d-c+1] := u2{[1..d]}[d-c+1] + (-z) * u2{[1..d]}[d-j+1];
                        else

                            if c in [1..d/2] and j in [1..d/2] then
                                TransvecAtAlpha2(z);
                                ShiftTransvection2ByI(c);
                                ShiftTransvection2ByJ(j, c);
                            elif c in [((d/2)+1)..d] and j in [((d/2)+1)..d] then
                                TransvecAtAlpha2(-z);
                                ShiftTransvection2ByI(d-j+1);
                                ShiftTransvection2ByJ(d-c+1,d-j+1);
                            elif c+j < d+1 then
                                TransvecAtAlpha3(z);
                                ShiftTransvection3ByJ(d-c+1);
                                ShiftTransvection3ByI(d-j+1);
                            else
                                TransvecAtAlpha3(z);
                                ShiftTransvection3ByJ(j);
                                ShiftTransvection3ByI(c);
                            fi;

                            #Mul[c][j] := z;
                            g{[1..d]}[j] :=  g{[1..d]}[j] + z *  g{[1..d]}[c];
                            u2{[1..d]}[j] := u2{[1..d]}[j] + z * u2{[1..d]}[c];

                            #Mul[d-j+1][d-c+1] := z;
                            g{[1..d]}[d-c+1] :=  g{[1..d]}[d-c+1] + z *  g{[1..d]}[d-j+1];
                            u2{[1..d]}[d-c+1] := u2{[1..d]}[d-c+1] + z * u2{[1..d]}[d-j+1];
                        fi;
                    else

                        TransvecAtAlpha4(z);

                        if c > j then
                            ShiftTransvection4(c);
                        else
                            ShiftTransvection4(j);
                        fi;

                        #Mul[c][j] := z;
                        g{[1..d]}[j] :=  g{[1..d]}[j] + z *  g{[1..d]}[c];
                        u2{[1..d]}[j] := u2{[1..d]}[j] + z * u2{[1..d]}[c];
                    fi;

                    Add(slp,[[u2pos,1,tvpos,1],u2pos]);

                    #g := g * Mul;
                    #u2 := u2 * Mul;

                fi;

            od;

        fi;
    od;

    #Add(slp,[[u2pos,1],u2pos]);
    #test := MakeSLP(slp,6);
    #Display(ResultOfStraightLineProgram(slp,stdgens));
    # if not (ResultOfStraightLineProgram(test,stdgens)= u2) then
    #    Error("U2");
    # fi;
    #Add(slp,[[u1pos,1],u1pos]);
    #test := MakeSLP(slp,6);
    #if not (ResultOfStraightLineProgram(test,stdgens)= u1) then
    #    Error("U1");
    #fi;
    #return slp;
    #Display(g);
    #Display(g);

    Add( slp, [ [u1pos,1], [u2pos,1] ]);

    # Now u1^-1 * g * u2^-1 is the input matrix
    return [slp,[g, u1, u2], hs];
    
end
);



InstallGlobalFunction(  UnitriangularDecompositionSpEvenChar,
function( arg )

    local u1, u2, d, fld, f, alpha, c, r, j, a, z, i, Mul, g, ell, slp, hs, tmppos, AEMrespos, u1pos, u2pos, tvpos, T2pos, T3pos, T4pos, tmppos2, uipos, q, f2, TransvecAtAlpha2, TransvecAtAlpha3, TransvecAtAlpha4, test, ShiftTransvection3ByJ, ShiftTransvection3ByI, ShiftTransvection4, ShiftTransvection2ByJ, ShiftTransvection2ByI, stdgens;
    
    #    ###############
    #    Local Functions
    #    ###############

    #    The following five functions are local as they have side effects.
    #    In particular, they modify the global variables T_i and Ti_1

    # Let alpha in GF(p^f), alpha = Sum a_l omega^l, omega a primitive element
    # Let slp be the list of instructions in UnipotentDecomposition and Tipos
    # denote the slots where transvections t_{i,j}(omega^ell) 0 <= ell < f
    # are saved. This function computes
    # t_{i,j}(alpha) = product t_{i,j}(omega^ell)^{a_ell}  (see Theorem 5.22)
    # where the exponents a_ell are given by CoefficientsPrimitiveElement.
    
    #####
    # TransvectionAtAlpha2()
    #####

    TransvecAtAlpha2 := function( alpha )

        local cc, ell, instr;

        # if omega = 1 then we overwrite the position for tv with Ti(1)
        if IsOne( alpha ) then
            Add(slp, [ [ T2pos[1], 1 ], tvpos ] );
            return;
        fi;

        cc := CoefficientsPrimitiveElement( fld, alpha );
        instr := [];

        for ell in [ 1..Length(cc) ] do

            if not IsZero( cc[ell] ) then
                Append( instr, [ T2pos[ell], Int(cc[ell]) ] );
            fi;
        od;

        if Length( instr ) = 0 then
            Error("TransvecAtAlpha2: this should not happen");
        fi;

        Add( slp, [ instr,tvpos ] );

        return;

    end;

    #####
    # ShiftTransvection2ByI()
    #####

    ShiftTransvection2ByI := function(i)

        local instr;

        instr := AEM( 4, AEMrespos, tmppos, i-2 );
        Append( slp, instr );
        Add( slp, [ [ AEMrespos, -1, tvpos , 1, AEMrespos, 1 ], tvpos ] );

    end;

    #####
    # ShiftTransvection2ByJ()
    #####

    ShiftTransvection2ByJ := function(i, abnr)

        local ui;

        ui := (d/2)-2;

        while ui-i+1-(d/2-abnr) > 0 do
            Add(slp, [[uipos[ui-(d/2-abnr)],1,tvpos,1,uipos[ui-(d/2-abnr)],1],tvpos]);
            ui := ui-1;
        od;

    end;

    #####
    # TransvectionAtAlpha3()
    #####

    TransvecAtAlpha3 := function( alpha )

        local cc, ell, instr;

        # if omega = 1 then we overwrite the position for tv with Ti(1)
        if IsOne( alpha ) then
            Add(slp, [ [ T3pos[1], 1 ], tvpos ] );
            return;
        fi;

        cc := CoefficientsPrimitiveElement( fld, alpha );
        instr := [];

        for ell in [ 1..Length(cc) ] do

            if not IsZero( cc[ell] ) then
                Append( instr, [ T3pos[ell], Int(cc[ell]) ] );
            fi;
        od;

        if Length( instr ) = 0 then
            Error("TransvecAtAlpha3: this should not happen");
        fi;

        Add( slp, [ instr,tvpos ] );

        return;

    end;

    #####
    # ShiftTransvection3ByI()
    #####

    ShiftTransvection3ByI := function(i)

        local ui;

        i := d-i+1;
        ui := 1;

        while ui < i do
            Add(slp, [[uipos[ui],1,tvpos,1,uipos[ui],1],tvpos]);
            ui := ui+1;
        od;

    end;

    #####
    # ShiftTransvection3ByJ()
    #####

    ShiftTransvection3ByJ := function(i)

        local instr;

        i := i-1;

        Add(slp,[[4,1,5,1],tmppos2]);
        instr := AEM( tmppos2, AEMrespos, tmppos, i-1 );
        Append( slp, instr );
        Add( slp, [ [ AEMrespos, -1, tvpos , 1, AEMrespos, 1 ], tvpos ] );

    end;

    #####
    # TransvectionAtAlpha4()
    #####

    TransvecAtAlpha4 := function( alpha )

        local cc, ell, instr, w, delta, specialalpha, VS, basis;

        delta := stdgens[3];
        w := delta[1][1];
        basis := [];
        for ell in [1..f] do
            Add(basis,w^(2*ell));
        od;

        VS := VectorSpace(GF(Characteristic(fld)),basis);

        cc := CoefficientsPrimitiveElementS( fld, alpha, Basis(VS,basis));
        instr := [];

        for ell in [ 1..Length(cc) ] do

            if not IsZero( cc[ell] ) then
                Append( instr, [ T4pos[ell], Int(cc[ell]) ] );
            fi;
        od;

        if Length( instr ) = 0 then
            Error("TransvecAtAlpha4: this should not happen");
        fi;

        Add( slp, [ instr,tvpos ] );

        return;

    end;

    #####
    # ShiftTransvection4()
    #####

    ShiftTransvection4 := function(i)
        local instr;

        i := d-i+1;

        if (i<d+1 ) then
            instr := AEM( 4, AEMrespos, tmppos, i-1 );
            Append( slp, instr );
            Add( slp, [ [ AEMrespos, -1, tvpos , 1, AEMrespos, 1 ], tvpos ] );
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
        # The first 12 entries are the stdgens and the inverses
        # s, t, del, v, x, s^-1, t^-1, del^-1, v^-1, x^-1
        slp := [    [1,1], [2,1], [3,1], [4,1], [5,1], [6,1],
                    [1,-1],[2,-1],[3,-1],[4,-1],[5,-1], [6,-1]   ];
    fi;

    d := Length( g );
    fld := FieldOfMatrixList( stdgens );

    # To create an MSLP, we allocate all the memory needed at the beginning.
    Add( slp, [1,0] );        tmppos       := Length(slp);    #15
    Add( slp, [1,0] );        AEMrespos    := Length(slp);    #16
    Add( slp, [1,0] );        u1pos        := Length(slp);    #17
    Add( slp, [1,0] );        u2pos        := Length(slp);    #18
    Add( slp, [1,0] );        tvpos        := Length(slp);    #19
    Add( slp, [1,0] );        tmppos2      := Length(slp);    #20


    u1 := MutableCopyMat( One(g) );
    u2 := MutableCopyMat( One(g) );

    # If g is already a monomial matrix return u_1 = u_2 = I_d
    if TestIfMonomial( g ) then
        Add( slp, [ [1,0],[1,0] ] );
        return [ slp, [u1,g,u2] ];
    fi;

    f := LogInt(Size(fld), Characteristic(fld)); #ie q=p^f

    hs := HighestSlotOfSLP(slp);

    # We create the help variables for the block top left or bottom right
    T2pos := [ hs + 1 .. hs + f ];

    hs := hs + f;

    for ell in [ 1..f ] do
        Add(slp, [1,0] );
    od;

    for ell in [0..f-1] do

        Add(slp, [ [3, -ell, 4, -2, 3, ell, 4 ,2 ], tmppos ] );
        Add(slp, [ [5,1,1,1,tmppos, 1, 6, 1, tmppos, -1,1,-1,5,-1 ], T2pos[ell+1] ] );

    od;

    # We create the help variables for the block in the bottom left
    T3pos := [ hs + 1 .. hs + f ];

    hs := hs + f;

    for ell in [ 1..f ] do
        Add(slp, [1,0] );
    od;

    for ell in [0..f-1] do

        Add(slp, [ [3, -ell, 4, -2, 3, ell, 4 ,2 ], tmppos ] );
        Add(slp, [ [tmppos, 1, 6, 1, tmppos, -1], T3pos[ell+1] ] );

    od;

    # We create the help variables for the diagonal
    T4pos := [ hs + 1 .. hs + f ];

    hs := hs + f ;

    for ell in [ 1..f ] do
        Add(slp, [1,0] );
    od;

    for ell in [1..f] do

        Add(slp, [ [1,-1,3,ell,2,-1,3,-ell,1,1], T4pos[ell] ] );

    od;

    # We create the help variables for the shift

    uipos := [ hs + 1 .. (hs + (d/2)-2) ];

    hs := hs + ((d/2)-2) ;

    for ell in [ 1 .. ((d/2)-2)  ] do
        Add(slp, [1,0] );
    od;

    Add( slp, [[5,1],uipos[1]]);

    for ell in [2..((d/2)-2) ] do
            Add( slp, [ [ 4, -1, uipos[ell-1] , 1, 4, 1 ], uipos[ell] ] );
    od;

    ############
    # Tests
    ############

    #test :=PseudoRandom(fld);

    #Display(test);

    #TransvecAtAlpha2(test);
    #ShiftTransvection2ByI(5);
    #ShiftTransvection2ByJ(2, 5);

    #TransvecAtAlpha4(test);
    #ShiftTransvection4(7);

    #TransvecAtAlpha3(test);
    #ShiftTransvection3ByJ(4);
    #ShiftTransvection3ByI(10);

    #Add(slp, [[tvpos,1],tvpos]);

    #return MakeSLP(slp,7);

    ############
    # Main
    ############

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

        a := g[r][c]^-1;

        if r <= d-1 then

            if not IsZero( g[r+1][c] ) then

                z := - g[r+1][c] * a;

                # add z times row r of g  to row r+1
                # add z times row r of u1  to row r+1
                # g[r+1] :=  g[r+1] + z *  g[r];
                # u1[r+1] := u1[r+1] + z * u1[r];
                # Mul := List( One(SU(d,Size(fld))), ShallowCopy );

                if (r+r+1 <> d+1) then

                    if r in [1..d/2] and r+1 in [1..d/2] then
                        TransvecAtAlpha2(z);
                        ShiftTransvection2ByI(r+1);
                        ShiftTransvection2ByJ(r, r+1);
                    else
                        TransvecAtAlpha2(-z);
                        ShiftTransvection2ByI(d-r+1);
                        ShiftTransvection2ByJ(d-r,d-r+1);
                    fi;

                    #Mul[r+1][r] := z;
                    g[r+1] :=  g[r+1] + z *  g[r];
                    u1[r+1] := u1[r+1] + z * u1[r];

                    #Mul[d-r+1][d-r] := -z;
                    g[d-r+1] :=  g[d-r+1] + (-z) *  g[d-r];
                    u1[d-r+1] := u1[d-r+1] + (-z) * u1[d-r];
                else

                    TransvecAtAlpha4(z);
                    ShiftTransvection4(r+1);

                    # Mul[r+1][r] := z;
                    g[r+1] :=  g[r+1] + z *  g[r];
                    u1[r+1] := u1[r+1] + z * u1[r];
                fi;

                Add(slp,[[tvpos,1,u1pos,1],u1pos]);

                #g := Mul * g;
                #u1 := Mul * u1;

            fi;


            # Second: Clear the rest of column c
            for i in [ r+2..d ] do

                if not IsZero(g[i][c]) then

                    z := -g[i][c] * a;

                    # add z times row r of g  to row i
                    # add z times row r of u1  to row i
                    #g[i] := g[i] + z*g[r];
                    #u1[i] := u1[i] + z*u1[r];
                    #Mul := List( One(SU(d,Size(fld))), ShallowCopy );

                    if (i+r <> d+1) then
                        if(r <= d/2) then
                            if (i <= d/2) then

                                if i in [1..d/2] and r in [1..d/2] then
                                    TransvecAtAlpha2(z);
                                    ShiftTransvection2ByI(i);
                                    ShiftTransvection2ByJ(r, i);
                                elif i in [((d/2)+1)..d] and r in [((d/2)+1)..d] then
                                    TransvecAtAlpha2(-z);
                                    ShiftTransvection2ByJ(d-r+1);
                                    ShiftTransvection2ByI(d-i+1,d-r+1);
                                elif i+r < d+1 then
                                    TransvecAtAlpha3(z);
                                    ShiftTransvection3ByJ(d-i+1);
                                    ShiftTransvection3ByI(d-r+1);
                                else
                                    TransvecAtAlpha3(z);
                                    ShiftTransvection3ByJ(r);
                                    ShiftTransvection3ByI(i);
                                fi;

                                #Mul[i][r] := z;
                                g[i] := g[i] + z*g[r];
                                u1[i] := u1[i] + z*u1[r];

                                #Mul[d-r+1][d-i+1] := -z;
                                g[d-r+1] := g[d-r+1] + (-z)*g[d-i+1];
                                u1[d-r+1] := u1[d-r+1] + (-z)*u1[d-i+1];
                            else

                                if i in [1..d/2] and r in [1..d/2] then
                                    TransvecAtAlpha2(z);
                                    ShiftTransvection2ByI(i);
                                    ShiftTransvection2ByJ(r, i);
                                elif i in [((d/2)+1)..d] and r in [((d/2)+1)..d] then
                                    TransvecAtAlpha2(-z);
                                    ShiftTransvection2ByJ(d-r+1);
                                    ShiftTransvection2ByI(d-i+1,d-r+1);
                                elif i+r < d+1 then
                                    TransvecAtAlpha3(z);
                                    ShiftTransvection3ByJ(d-i+1);
                                    ShiftTransvection3ByI(d-r+1);
                                else
                                    TransvecAtAlpha3(z);
                                    ShiftTransvection3ByJ(r);
                                    ShiftTransvection3ByI(i);
                                fi;

                                #Mul[i][r] := z;
                                g[i] := g[i] + z*g[r];
                                u1[i] := u1[i] + z*u1[r];

                                #Mul[d-r+1][d-i+1] := z;
                                g[d-r+1] := g[d-r+1] + z*g[d-i+1];
                                u1[d-r+1] := u1[d-r+1] + z*u1[d-i+1];
                            fi;
                        else

                            if i in [1..d/2] and r in [1..d/2] then
                                TransvecAtAlpha2(z);
                                ShiftTransvection2ByI(i);
                                ShiftTransvection2ByJ(r, i);
                            elif i in [((d/2)+1)..d] and r in [((d/2)+1)..d] then
                                TransvecAtAlpha2(-z);
                                ShiftTransvection2ByI(d-r+1);
                                ShiftTransvection2ByJ(d-i+1,d-r+1);
                            elif i+r < d+1 then
                                TransvecAtAlpha3(z);
                                ShiftTransvection3ByJ(d-i+1);
                                ShiftTransvection3ByI(d-r+1);
                            else
                                TransvecAtAlpha3(z);
                                ShiftTransvection3ByJ(r);
                                ShiftTransvection3ByI(i);
                            fi;

                            #Mul[i][r] := z;
                            g[i] := g[i] + z*g[r];
                            u1[i] := u1[i] + z*u1[r];

                            #Mul[d-r+1][d-i+1] := -z;
                            g[d-r+1] := g[d-r+1] + (-z)*g[d-i+1];
                            u1[d-r+1] := u1[d-r+1] + (-z)*u1[d-i+1];

                        fi;
                    else

                        TransvecAtAlpha4(z);

                        if i > r then
                            ShiftTransvection4(i);
                        else
                            ShiftTransvection4(r);
                        fi;

                        #Mul[i][r] := z;
                        g[i] := g[i] + z*g[r];
                        u1[i] := u1[i] + z*u1[r];
                    fi;

                    Add(slp,[[tvpos,1,u1pos,1],u1pos]);

                    #g := Mul * g;
                    #u1 := Mul * u1;

                fi;


            od;

        fi;


        # Step Two: Clear all entries in row r apart from g[r][c]
        # This coincides with multiplying t_{c,j} from right.
        if c >= 2 then

            if not IsZero( g[r][c-1] ) then

                z := -g[r][c-1] * a;

                # add z times column c of g to column c-1
                # add z times column c of u2 to column c-1
                #g{[ 1..d ]}[ c-1 ] := g{[ 1..d ]}[ c-1 ] + z * g{[1..d]}[c];
                #u2{[1..d]}[c-1] := u2{[1..d]}[c-1] + z * u2{[1..d]}[c];

                #Mul := List( One(G), ShallowCopy );

                if (c+c-1 <>  d+1) then
                    if (c-1 > d/2) then
                        #Mul[c][c-1] := z;
                        if c in [1..d/2] and c-1 in [1..d/2] then
                            TransvecAtAlpha2(z);
                            ShiftTransvection2ByI(c);
                            ShiftTransvection2ByJ(c-1, c);
                        else
                            TransvecAtAlpha2(-z);
                            ShiftTransvection2ByI(d-c+2);
                            ShiftTransvection2ByJ(d-c+1,d-c+2);
                        fi;

                        g{[ 1..d ]}[ c-1 ] := g{[ 1..d ]}[ c-1 ] + z * g{[1..d]}[c];
                        u2{[1..d]}[c-1] := u2{[1..d]}[c-1] + z * u2{[1..d]}[c];

                        #Mul[d-c+2][d-c+1] := -z;
                        g{[ 1..d ]}[ d-c+1 ] := g{[ 1..d ]}[ d-c+1 ] + (-z) * g{[1..d]}[d-c+2];
                        u2{[1..d]}[d-c+1] := u2{[1..d]}[d-c+1] + (-z) * u2{[1..d]}[d-c+2];
                    else
                        #Mul[c][c-1] := z;
                        g{[ 1..d ]}[ c-1 ] := g{[ 1..d ]}[ c-1 ] + z * g{[1..d]}[c];
                        u2{[1..d]}[c-1] := u2{[1..d]}[c-1] + z * u2{[1..d]}[c];

                        #Mul[d-c+2][d-c+1] := z;
                        g{[ 1..d ]}[ d-c+1 ] := g{[ 1..d ]}[ d-c+1 ] + z * g{[1..d]}[d-c+2];
                        u2{[1..d]}[d-c+1] := u2{[1..d]}[d-c+1] + z * u2{[1..d]}[d-c+2];
                    fi;
                else
                    TransvecAtAlpha4(z);
                    ShiftTransvection4(c);

                    #Mul[c][c-1] := z;
                    g{[ 1..d ]}[ c-1 ] := g{[ 1..d ]}[ c-1 ] + z * g{[1..d]}[c];
                    u2{[1..d]}[c-1] := u2{[1..d]}[c-1] + z * u2{[1..d]}[c];
                fi;

                Add(slp,[[u2pos,1,tvpos,1],u2pos]);

                #g := g * Mul;
                #u2 := u2 * Mul;

            fi;


            # Now clear the rest of row r
            for j in [ c-2, c-3..1 ] do

                if not IsZero( g[r][j] ) then

                    z := - g[r][j] * a;

                    # add z times column c of g to column j
                    # add z times column c of u2 to column j
                    # g{[1..d]}[j] :=  g{[1..d]}[j] + z *  g{[1..d]}[c];
                    #u2{[1..d]}[j] := u2{[1..d]}[j] + z * u2{[1..d]}[c];

                    #Mul := List( One(G), ShallowCopy );

                    if (c+j <>  d+1) then
                        if (j > d/2) then

                            if c in [1..d/2] and j in [1..d/2] then
                                TransvecAtAlpha2(z);
                                ShiftTransvection2ByI(c);
                                ShiftTransvection2ByJ(j, c);
                            elif c in [((d/2)+1)..d] and j in [((d/2)+1)..d] then
                                TransvecAtAlpha2(-z);
                                ShiftTransvection2ByI(d-j+1);
                                ShiftTransvection2ByJ(d-c+1,d-j+1);
                            elif c+j < d+1 then
                                TransvecAtAlpha3(z);
                                ShiftTransvection3ByJ(d-c+1);
                                ShiftTransvection3ByI(d-j+1);
                            else
                                TransvecAtAlpha3(z);
                                ShiftTransvection3ByJ(j);
                                ShiftTransvection3ByI(c);
                            fi;

                            #Mul[c][j] := z;
                            g{[1..d]}[j] :=  g{[1..d]}[j] + z *  g{[1..d]}[c];
                            u2{[1..d]}[j] := u2{[1..d]}[j] + z * u2{[1..d]}[c];

                            #Mul[d-j+1][d-c+1] := -z;
                            g{[1..d]}[d-c+1] :=  g{[1..d]}[d-c+1] + (-z) *  g{[1..d]}[d-j+1];
                            u2{[1..d]}[d-c+1] := u2{[1..d]}[d-c+1] + (-z) * u2{[1..d]}[d-j+1];
                        else

                            if c in [1..d/2] and j in [1..d/2] then
                                TransvecAtAlpha2(z);
                                ShiftTransvection2ByI(c);
                                ShiftTransvection2ByJ(j, c);
                            elif c in [((d/2)+1)..d] and j in [((d/2)+1)..d] then
                                TransvecAtAlpha2(-z);
                                ShiftTransvection2ByI(d-j+1);
                                ShiftTransvection2ByJ(d-c+1,d-j+1);
                            elif c+j < d+1 then
                                TransvecAtAlpha3(z);
                                ShiftTransvection3ByJ(d-c+1);
                                ShiftTransvection3ByI(d-j+1);
                            else
                                TransvecAtAlpha3(z);
                                ShiftTransvection3ByJ(j);
                                ShiftTransvection3ByI(c);
                            fi;

                            #Mul[c][j] := z;
                            g{[1..d]}[j] :=  g{[1..d]}[j] + z *  g{[1..d]}[c];
                            u2{[1..d]}[j] := u2{[1..d]}[j] + z * u2{[1..d]}[c];

                            #Mul[d-j+1][d-c+1] := z;
                            g{[1..d]}[d-c+1] :=  g{[1..d]}[d-c+1] + z *  g{[1..d]}[d-j+1];
                            u2{[1..d]}[d-c+1] := u2{[1..d]}[d-c+1] + z * u2{[1..d]}[d-j+1];
                        fi;
                    else

                        TransvecAtAlpha4(z);

                        if c > j then
                            ShiftTransvection4(c);
                        else
                            ShiftTransvection4(j);
                        fi;

                        #Mul[c][j] := z;
                        g{[1..d]}[j] :=  g{[1..d]}[j] + z *  g{[1..d]}[c];
                        u2{[1..d]}[j] := u2{[1..d]}[j] + z * u2{[1..d]}[c];
                    fi;

                    Add(slp,[[u2pos,1,tvpos,1],u2pos]);

                    #g := g * Mul;
                    #u2 := u2 * Mul;

                fi;

            od;

        fi;
    od;

    #Add(slp,[[u2pos,1],u2pos]);
    #test := MakeSLP(slp,6);
    #Display(ResultOfStraightLineProgram(slp,stdgens));
    # if not (ResultOfStraightLineProgram(test,stdgens)= u2) then
    #    Error("U2");
    # fi;
    #Add(slp,[[u1pos,1],u1pos]);
    #test := MakeSLP(slp,6);
    #if not (ResultOfStraightLineProgram(test,stdgens)= u1) then
    #    Error("U1");
    #fi;
    #return slp;
    #Display(g);
    #Display(g);

    Add( slp, [ [u1pos,1], [u2pos,1] ]);

    # Now u1^-1 * g * u2^-1 is the input matrix
    return [slp,[g, u1, u2], hs];
    
end
);



#####
# LGOStandardGensSp
#####

InstallGlobalFunction(  LGOStandardGensSp,
function( d, q )

    local w,s, t, delta, u, v, x, J, fld;
    
    if d < 6 then
        Error("LGOStandardGens: d has to be at least 6\n");
        return;
    fi;
    
    if (q mod 2 = 0) then
        return LGOStandardGensSpEvenChar(d,q);
    fi;

    fld := GF(q);
    w := PrimitiveElement(fld);

    s := IdentityMat( d, fld );
    s[1][1] := Zero(fld);
    s[d][d] := Zero(fld);
    s[1][d] := One(fld);
    s[d][1] := -One(fld);

    t := IdentityMat( d, fld );
    t[1][d] := One(fld);

    delta := IdentityMat( d, fld );
    delta[1][1] := w;
    delta[d][d] := w^(-1);

    v := 0 * IdentityMat( d, fld );
    v[d/2][1] := One(fld);
    v{[1..(d/2)-1]}{[2..d/2]} := IdentityMat((d/2)-1, fld);
    v[d/2+1][d] := One(fld);
    v{[(d/2)+2..d]}{[(d/2)+1..d-1]} := IdentityMat((d/2)-1, fld);

    u := IdentityMat( d, fld );
    J := [[Zero(fld),One(fld)],[One(fld),Zero(fld)]];
    u{[1,2]}{[1,2]} := J;
    u{[d-1,d]}{[d-1,d]} := J;

    x := IdentityMat( d, fld );
    x[d-1][1] := One(fld);
    x[d][2] := One(fld);

    return [s,t,delta,v,u,x];

end
);



#####
# LGOStandardGensSpEvenChar
#####

InstallGlobalFunction(  LGOStandardGensSpEvenChar,
function( d, q )

    local w,s, t, delta, u, v, x, J, fld;

    fld := GF(q);
    w := PrimitiveElement(fld);

    s := IdentityMat( d, fld );
    s[1][1] := Zero(fld);
    s[d][d] := Zero(fld);
    s[1][d] := One(fld);
    s[d][1] := One(fld);

    t := IdentityMat( d, fld );
    t[1][d] := One(fld);

    delta := IdentityMat( d, fld );
    delta[1][1] := w;
    delta[d][d] := w^(-1);

    v := 0 * IdentityMat( d, fld );
    v[d/2][1] := One(fld);
    v{[1..(d/2)-1]}{[2..d/2]} := IdentityMat((d/2)-1, fld);
    v[d/2+1][d] := One(fld);
    v{[(d/2)+2..d]}{[(d/2)+1..d-1]} := IdentityMat((d/2)-1, fld);

    u := IdentityMat( d, fld );
    J := [[Zero(fld),One(fld)],[One(fld),Zero(fld)]];
    u{[1,2]}{[1,2]} := J;
    u{[d-1,d]}{[d-1,d]} := J;

    x := IdentityMat( d, fld );
    x[d-1][1] := One(fld);
    x[d][2] := One(fld);

    return [s,t,delta,v,u,x];
    
end
);



#####
#   MonomialSLPSp
#####

InstallGlobalFunction(  MonomialSLPSp,
function( arg )

    local slp, c, n, m, result, i, k, u1, u2, result2, test, g, stdgens, mat, perm, fld, p_signpos, vpos, vipos, spos, upos, unpos, tpos, left, right, cnt, v, vf, s, pot, p_signwr, instr, p_sign, leftma, rightma, L, R, diag, w, alpha, tmpvalue, rowlist, L2, R2, tmpSave, perm2, perm3;

    # Check for correct Input
    if Length(arg) >= 2 and IsList(arg[1]) and IsMatrix(arg[2]) then

        stdgens := arg[1];  # the LGO standard generators
        mat := arg[2];        # the monomial matrix
        n := Length(stdgens[1]);
        m := n/2;

        # Compute the permutation in Sym(n) of mat
        perm := PermutationMonomialMatrix( mat );
        diag := perm[1];
        perm := perm[2];
        p_signwr := (stdgens[1]^0);

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
        # The first 12 entries are the stdgens and the inverses
        # s, t, del, v, x, s^-1, t^-1, del^-1, v^-1, x^-1
        # The entries 13 (resAEM) and 14 (tmpAEM) are used to save AEM-values
        slp := [    [1, 1], [2, 1], [3, 1], [4, 1], [5, 1], [6, 1],
                    [1,-1], [2,-1], [3,-1], [4,-1], [5,-1], [6,-1],
                    [1, 0], [1, 0]    ];

        cnt := 14;

        Info( InfoBruhat, 2, "Memory Usage is: ",19,"  memory slots ",
                            "in PermSLP()\n");
    fi;

    # Initialize the additional memory quota
    Add(slp, [ [1,0], cnt + 1 ] );    p_signpos := cnt + 1;    #13 or 20+3f
    Add(slp, [ [4,-1], cnt + 2 ] );    vpos      := cnt + 2;    #14 or 21+3f
    Add(slp, [ [4,-1], cnt + 3 ] );    vipos     := cnt + 3;    #15 or 22+3f
    Add(slp, [ [1,1], cnt + 4 ] );    spos      := cnt + 4;    #16 or 23+3f
    Add(slp, [ [5,1], cnt + 5 ] );    upos      := cnt + 5;    #17 or 24+3f
    Add(slp, [ [5,0], cnt + 6 ] );    unpos     := cnt + 6;    #18 or 25+3f
    Add(slp, [ [1,0], cnt + 7 ] );    tpos      := cnt + 7;    #19 or 26+3f
    Add(slp, [ [1,0], cnt + 8 ] );    left      := cnt + 8;    #20 or 27+3f
    Add(slp, [ [1,0], cnt + 9 ] );    right     := cnt + 9;    #21 or 28+3f

    if IsDiagonalMat( mat ) then
        # In order to make it coincide with the other possible output.
        # This is ok since it is Id
        Add( slp, [ [p_signpos,-1] , p_signpos ] );
        return [ slp, [ stdgens[1]^0, mat ] ];
    fi;

    c := CycleFromPermutation(perm);
    u1 := One(SymmetricGroup(n));
    u2 := One(SymmetricGroup(n));
    result := [];
    result2 := [];
    m := n/2;
    L2 := IdentityMat(n,fld);
    R2 := IdentityMat(n,fld);
    w := PrimitiveElement(fld);
    # set alpha in SU
    while (CheckContinue(perm,m)) do
        c := CycleFromPermutation(perm);
        for i in c do
            k := LargestMovedPoint(i);
            if k <= m then
                Add(result, i);
            elif SmallestMovedPoint(i) > m then

            elif (n-k+1)^i = n-k+1 then
                tmpvalue := L2[k];
                L2[k] := L2[n-k+1];
                L2[n-k+1] := (-1)* tmpvalue;
                tmpvalue := R2{[1..n]}[k];
                R2{[1..n]}[k] := R2{[1..n]}[n-k+1];
                R2{[1..n]}[n-k+1] := (-1)*tmpvalue;
                perm := perm^(k,n-k+1);
                u1 := (k,n-k+1) * u1;
                Add( slp, [ [vpos,-k,spos,1,vpos,k] , tpos ] );
                Add( slp, [ [tpos,-1,left,1] , left ] );
                Add( slp, [ [right,1,tpos,1] , right] );
                u2 := u2 * (k,n-k+1);

                break;
            else
                tmpvalue := L2[k];
                L2[k] := (-1)* L2[n-k+1];
                L2[n-k+1] := tmpvalue;
                perm := (k,n-k+1)*perm;
                u1 := (k,n-k+1) * u1;
                Add( slp, [ [vpos,-k,spos,1,vpos,k] , tpos ] );
                Add( slp, [ [tpos,1,left,1] , left ] );

                break;
            fi;
        od;
    od;

    c := CycleFromPermutation(perm);
    for i in c do
        k := LargestMovedPoint(i);
        if k <= m then
            Add(result, i);
        else
            Add(result2, i);
        fi;
    od;

    result := Set(result);
    result2 := Set(result2);

    Add( slp, [ [left,-1] , left ] );
    Add( slp, [ [right,-1] , right ] );

    perm := One(SymmetricGroup(n));
    for i in [1..Size(result)] do
        perm := perm * result[i];
    od;

    perm2 := One(SymmetricGroup(n));
    for i in [1..Size(result2)] do
        perm2 := perm2 * result2[i];
    od;

    v := (CycleFromPermutation(PermutationMonomialMatrix(stdgens[4])[2])[1])^(-1);
    vf := (CycleFromPermutation(PermutationMonomialMatrix(stdgens[4])[2])[1])^(-1);
    s := CycleFromPermutation(PermutationMonomialMatrix(stdgens[5])[2])[1];

    Add( slp, [ [4,1], vpos ] );
    Add( slp, [ [4,-1], vipos ] );
    Add( slp, [ [5,1], spos ] );

    perm3 := perm;

    for i in [ 1 .. m ] do

        pot := i^perm - i;

        # Need to update perm since pi_{i-1} may change pos of i
        perm   :=   perm   *  v ^pot;

        # memory slots 13 and 14 are used for resAEM and tmpAEM
        instr := AEM( vipos, 13, 14, pot );
        Append( slp, instr );
        Add( slp, [ [p_signpos,1, 13,1 ], p_signpos ] ); # permpos

        #Compute v_i+1, save command in slp
        v  :=    s    *  v;

        Add(slp,[ [spos,1, vipos,1 ], vipos ] ); # vipos
        # Don't be confused with notation in Paper
        # There we used v1 (which coincides with v^-1)

        s  :=   s ^(  vf ^-1 );
        Add(slp, [ [10, 1, spos,1, 4,1 ], spos ] ); # spos


    od;

    Add(slp,[ [ p_signpos,-1 ], p_signpos ] );

    tmpvalue := PermutationMat(perm2^(-1),n, fld);
    tmpvalue{[1..n/2]}{[1..n/2]} := PermutationMat(perm3^(-1),n/2, fld);

    Add( slp, [ [left,1,p_signpos,1,right,1] , p_signpos ] );

    Add( slp, [ p_signpos ,1 ] );

    tmpvalue :=R2*tmpvalue*L2;
    mat := tmpvalue*mat;

    return [slp, [ tmpvalue, mat ] ];
    
end
);



#####
#   DiagSLPSp
#####

InstallGlobalFunction(  DiagSLPSp,
function( arg )

    local stdgens, diag, fld, slp, a_i, d, omega, delta, u, v, cnt, hiposm, hipos, respos, hres, instr, i;

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

    if Length(arg) >= 3  and Length(arg) <= 4  then

        # The first 12 entries are the stdgens and their inverses
        slp := arg[3];

        if not IsList(slp) then
            Error("Input: third argument must be a list");
            return fail;
        fi;

        cnt := arg[4];
        # <--- Laesst sich das umgehen? Jeweils den hoechsten Slot mitzaehlen?
        Info( InfoBruhat, 2, " and additional:  ",3," memory slots ",
                            "in DiagonalDecomposition()\n");

    else
        # We write an SLP into the variable slp
        # The first 10 entries are the stdgens and their inverses
        # s^-1 t^-1  del^-1    v^-1    x^-1
        # The entries #13 (resAEM),#14 (tmpAEM) are used to save AEM-values
        slp := [     [1, 1], [2, 1], [3, 1], [4, 1], [5, 1], [6, 1],
                    [1,-1], [2,-1], [3,-1], [4,-1], [5,-1], [6,-1],
                    [1, 0], [1, 0] ];

        cnt := 14;
        Info( InfoBruhat, 2, "Memory Usage is: ",4," memory slots ",
                            "in DiagonalDecomposition()\n");
    fi;

    # Define the LGO standard-generators given in the input
    delta    := stdgens[3];
    v        := stdgens[4];
    u        := stdgens[5];

    # Initialize the additional memory quota
    #hi-2
    Add(slp, [ [1,0], cnt + 1 ] );    hiposm := cnt + 1;     #15 or 27+3f
    #hi-1
    Add(slp, [ [1,0], cnt + 2 ] );    hipos := cnt + 2;     #16 or 28+3f
    # result
    Add(slp, [ [1,0], cnt + 3 ] );    respos := cnt + 3;     #17 or 29+3f

    d := Length( diag );
    omega := delta[1][1];

    if diag = One(diag) then
        Add( slp, [ [1,0], respos ] );
        Add( slp, [ respos, 1]);
        return [ slp, diag ];
    fi;

    hres := diag^0;
    Add( slp, [ [5,1], hiposm ] );
    Add( slp, [ [3,1], hipos ] );

    for i in [ 1..(d/2) ] do

        a_i := LogFFE( diag[i][i], omega );
        # The memory slots 13 and 14 are res and tmp-slot for AEM
        instr := AEM( hipos, 13, 14, a_i );
        Append( slp, instr );
        Add( slp, [ [respos, 1, 13, 1 ], respos ] );
        Add( slp, [ [hiposm, -1 , hipos, 1, hiposm,1 ], hipos ] );
        Add( slp, [ [4, -1 , hiposm, 1, 4, 1], hiposm ] );

    od;

    Add( slp, [ respos ,1 ] );

    return [slp];

end
);



#####
#   BruhatDecompositionSp
#####

InstallGlobalFunction(  BruhatDecompositionSp,
function( stdgens, g )

    local slp, u1, pm, u2, p_sign, diag, res1, res2, res3, lastline, line, pgr, fld, q;

    # We write an SLP into the variable slp
    # The first 12 entries are the stdgens and their inverses
    # s, t, del, v, u, x, s^-1, t^-1, del^-1, v^-1, u^-1, x^-1

    Info( InfoBruhat, 1,
            "returns an SLP to generate u1, u2, p_sign, diag\n"    );
            
    fld := FieldOfMatrixList( [g] );
    q := Size(fld);

    # Compute the matrices u1,u2 of Bruhat-Decomposition and the instructions
    # for an SLP that compute u1 and u2
    if q mod 2 = 0 then
        res1 := UnitriangularDecompositionSpEvenChar( stdgens, g);
    else
        res1 := UnitriangularDecompositionSp( stdgens, g);
    fi;

    slp := res1[1];
    u1 := res1[2][2];
    pm := res1[2][1];    # the monomial matrix w
    u2 := res1[2][3];

    lastline := ShallowCopy( slp[ Length(slp) ] ); # remember famous last words
    # Since entries of the form [list1,list2] should only occur at the end
    Remove(slp);

    # Decompose w in to a signed Permutation-Matrix generated by <s,v,x>
    # and a Diagonal-Matrix diag.

    res2 := MonomialSLPSp(stdgens, pm, slp );

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
    Append(lastline, [ slp[ Length(slp)] ]);

    # Determine the SLP for the Diagonal-Matrix
    res3 := DiagSLPSp(stdgens, diag, slp, res1[3]+10);
    slp := res3[1];

    # Here the last entry is of admissible form. Just add it to the end.
    Append( lastline, [ slp[ Length(slp)] ] ); # remember famous last words
    Remove( slp );
    Append( slp, [lastline] );

    Info( InfoBruhat, 2, "The Total Memory Usage is: "
                        , res1[3]+9+14, " memory slots\n" );

    pgr := MakeSLP(slp,6);

    # The result R of pgr satisfies:
    #    R[1]^-1*R[3]*R[4]*R[2]^-1    and
    #    R[1] = u1, R[2] = u2, R[3] = p_sign, R[4] = diag
    return [pgr, [ u1, u2, p_sign^(-1), diag ]];

end
);
