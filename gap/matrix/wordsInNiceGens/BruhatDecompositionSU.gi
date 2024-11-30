######################################
# BruhatDecompositionSU.gi
######################################

####################
# PART I - a)
#    Originally implemented subfunctions
####################

InfoBruhat := NewInfoClass("InfoBruhat");;
SetInfoLevel( InfoBruhat, 2 );

#####
# MakePermutationMat()
#####

InstallGlobalFunction(  MakePermutationMat,
function(perm, dim, fld)

    local res;

    res := PermutationMat(perm, dim) * One(fld);
    ConvertToMatrixRep(res);

    return res;

end
);



#####
# CoefficientsPrimitiveElementS()
#####

InstallGlobalFunction(  CoefficientsPrimitiveElementS,
function(fld, alpha, basis)

    return Coefficients( basis, alpha );

end
);



#####
# UnitriangularDecompositionSUEven
#####

InstallGlobalFunction(  UnitriangularDecompositionSUEven,
function(arg)
    local u1, u2, d, fld, f, alpha, c, r, j, a, z, i, Galois, phi, stdgens, g, ell, slp, hs, tmppos, AEMrespos, u1pos, u2pos, tvpos, T2pos, T3pos, T4pos, tmppos2, uipos, q, f2, TransvecAtAlpha2, TransvecAtAlpha3, TransvecAtAlpha4, test, ShiftTransvection3ByJ, ShiftTransvection3ByI, ShiftTransvection4, ShiftTransvection2ByJ, ShiftTransvection2ByI;

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

        i := i-1;

        instr := AEM( 4, AEMrespos, tmppos, i-1 );
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

        local cc, ell, instr, w, y, specialalpha, VS, basis;

        y := stdgens[7];
        w := y[1][1];
        specialalpha := w^((q+1)/2);
        basis := [];
        for ell in [1..f2] do
            Add(basis,specialalpha^(-q)*(w^(q+1))^ell);
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
        # The first 14 entries are the stdgens and the inverses
        # s, t, del, v, x, s^-1, t^-1, del^-1, v^-1, x^-1
        slp := [    [1,1], [2,1], [3,1], [4,1], [5,1], [6,1], [7,1],
                    [1,-1],[2,-1],[3,-1],[4,-1],[5,-1], [6,-1], [7,-1]    ];
    fi;

    d := Length( g );
    fld := FieldOfMatrixList( stdgens );
    Galois := GaloisGroup(fld);
    Galois := Filtered(Galois, x -> Order(x) = 2);
    phi := Galois[1];

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
    q := RootInt(Characteristic(fld)^f);

    hs := HighestSlotOfSLP(slp);

    # We create the help variables for the block top left or bottom right
    T2pos := [ hs + 1 .. hs + f ];

    hs := hs + f;

    for ell in [ 1..f ] do
        Add(slp, [1,0] );
    od;

    for ell in [0..f-1] do

        Add(slp, [ [7, -ell, 4, -1, 7, -ell, 4 ,1 ], tmppos ] );
        Add(slp, [ [tmppos, 1, 5, -1, 6, 1, 5, 1, tmppos, -1 ], T2pos[ell+1] ] );

    od;

    # We create the help variables for the block in the bottom left
    T3pos := [ hs + 1 .. hs + f ];

    hs := hs + f;

    for ell in [ 1..f ] do
        Add(slp, [1,0] );
    od;

    for ell in [0..f-1] do

        Add(slp, [ [7, -(ell+ (q+1)/2 ) , 4, -1, 7, -(ell+ (q+1)/2 ), 4 ,1 ], tmppos ] );
        Add(slp, [ [1, -1, 5, -1, tmppos, 1, 5, -1, 6, 1, 5, 1, tmppos, -1 , 5, 1, 1, 1], T3pos[ell+1] ] );

    od;

    # We create the help variables for the diagonal
    f2 := Int((f * 0.5));
    T4pos := [ hs + 1 .. hs + f2 ];

    hs := hs + f2 ;

    for ell in [ 1..f2 ] do
        Add(slp, [1,0] );
    od;

    for ell in [1..f2] do

        Add(slp, [ [7, -ell, 1, -1, 2, 1, 1, 1 , 7, ell], T4pos[ell] ] );

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
    #ShiftTransvection2ByI(3);
    #ShiftTransvection2ByJ(2, 3);

    #y := stdgens[7];
    #w := y[1][1];
    #specialalpha := w^((q+1)/2);
    #basis := [];
    #for ell in [1..f2] do
    #    Add(basis,specialalpha^(-q)*(w^(q+1))^ell);
    #od;

    #VS := VectorSpace(GF(Characteristic(fld)),basis);
    #test := PseudoRandom(VS);

    #Display(test);
    #TransvecAtAlpha4(test);
    #ShiftTransvection4(7);

    #TransvecAtAlpha3(test);
    #ShiftTransvection3ByJ(4);
    #ShiftTransvection3ByI(10);

    #Add(slp, [[tvpos,1],tvpos]);

    #return MakeSLP(slp,7);

    ############
    # Start function
    ############

    g := MutableCopyMat(g);

    for c in [ d, d-1.. (d/2)+1 ] do

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
                #Mul := MutableCopyMat( One(g) );

                if (r+r+1 <> d+1) then

                    if r in [1..d/2] and r+1 in [1..d/2] then
                        TransvecAtAlpha2(z);
                        ShiftTransvection2ByI(r+1);
                        ShiftTransvection2ByJ(r, r+1);
                    else
                        TransvecAtAlpha2(-z^phi);
                        ShiftTransvection2ByI(d-r+1);
                        ShiftTransvection2ByJ(d-r,d-r+1);
                    fi;

                    #Mul[r+1][r] := z;
                    g[r+1] :=  g[r+1] + z *  g[r];
                    u1[r+1] := u1[r+1] + z * u1[r];

                    #Mul[d-r+1][d-r] := -z^phi;
                    g[d-r+1] :=  g[d-r+1] + -z^phi *  g[d-r];
                    u1[d-r+1] := u1[d-r+1] + -z^phi * u1[d-r];

                else
                    # Mul[r+1][r] := z;

                    TransvecAtAlpha4(z);
                    ShiftTransvection4(r+1);

                    g[r+1] :=  g[r+1] + z *  g[r];
                    u1[r+1] := u1[r+1] + z * u1[r];
                fi;

                Add(slp,[[tvpos,1,u1pos,1],u1pos]);

                #g := Mul * g;
                #u1 := Mul * u1;

            fi;


            # Second: Clear the rest of column c
            for i in [ r+1..d ] do

                if not IsZero(g[i][c]) then

                    z := -g[i][c] * a;

                    # add z times row r of g  to row i
                    # add z times row r of u1  to row i
                    #g[i] := g[i] + z*g[r];
                    #u1[i] := u1[i] + z*u1[r];
                    #Mul := MutableCopyMat( One(g) );

                    if (i+r <> d+1) then

                        if i in [1..d/2] and r in [1..d/2] then
                            TransvecAtAlpha2(z);
                            ShiftTransvection2ByI(i);
                            ShiftTransvection2ByJ(r, i);
                        elif i in [((d/2)+1)..d] and r in [((d/2)+1)..d] then
                            TransvecAtAlpha2(-z^phi);
                            ShiftTransvection2ByI(d-r+1);
                            ShiftTransvection2ByJ(d-i+1,d-r+1);  # Davor d-r in erster Komponente
                        elif i+r < d+1 then
                            TransvecAtAlpha3(-z^phi);
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

                        #Mul[d-r+1][d-i+1] := -z^phi;
                        g[d-r+1] := g[d-r+1] + -z^phi * g[d-i+1];
                        u1[d-r+1] := u1[d-r+1] + -z^phi * u1[d-i+1];
                    else
                        #Mul[i][r] := z;

                        TransvecAtAlpha4(z);

                        if i > r then
                            ShiftTransvection4(i);
                        else
                            ShiftTransvection4(r);
                        fi;

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
                #Mul := MutableCopyMat( One(g) );

                if (c+c-1 <>  d+1) then

                    if c in [1..d/2] and c-1 in [1..d/2] then
                        TransvecAtAlpha2(z);
                        ShiftTransvection2ByI(c);
                        ShiftTransvection2ByJ(c-1, c);
                    else
                        TransvecAtAlpha2(-z^phi);
                        ShiftTransvection2ByI(d-c+2);
                        ShiftTransvection2ByJ(d-c+1,d-c+2);
                    fi;

                    #Mul[c][c-1] := z;
                    g{[ 1..d ]}[ c-1 ] := g{[ 1..d ]}[ c-1 ] + z * g{[1..d]}[c];
                    u2{[1..d]}[c-1] := u2{[1..d]}[c-1] + z * u2{[1..d]}[c];

                    #Mul[d-c+2][d-c+1] := -z^phi;
                    g{[ 1..d ]}[ d-c+1 ] := g{[ 1..d ]}[ d-c+1 ] + (-z^phi) * g{[1..d]}[d-c+2];
                    u2{[1..d]}[d-c+1] := u2{[1..d]}[d-c+1] + (-z^phi) * u2{[1..d]}[d-c+2];
                else
                    #Mul[c][c-1] := z;

                    TransvecAtAlpha4(z);
                    ShiftTransvection4(c);

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
                    #Mul := MutableCopyMat( One(g) );

                    if (c+j <>  d+1) then

                        if c in [1..d/2] and j in [1..d/2] then
                            TransvecAtAlpha2(z);
                            ShiftTransvection2ByI(c);
                            ShiftTransvection2ByJ(j, c);
                        elif c in [((d/2)+1)..d] and j in [((d/2)+1)..d] then
                            TransvecAtAlpha2(-z^phi);
                            ShiftTransvection2ByI(d-j+1);
                            ShiftTransvection2ByJ(d-c+1,d-j+1);
                        elif c+j < d+1 then
                            TransvecAtAlpha3(-z^phi);
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

                        #Mul[d-j+1][d-c+1] := -z^phi;
                        g{[1..d]}[d-c+1] :=  g{[1..d]}[d-c+1] + (-z^phi) *  g{[1..d]}[d-j+1];
                        u2{[1..d]}[d-c+1] := u2{[1..d]}[d-c+1] + (-z^phi) * u2{[1..d]}[d-j+1];
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

    #Add(slp,[[u1pos,1],u1pos]);
    #test := MakeSLP(slp,7);
    #if not(ResultOfStraightLineProgram(test,stdgens)= u1) then
    #    Error("u1");
    #fi;
    #Add(slp,[[u2pos,1],u2pos]);
    #test := MakeSLP(slp,7);
    #if not(ResultOfStraightLineProgram(test,stdgens)= u2) then
    #    Error("u1");
    #fi;
    #Display(ResultOfStraightLineProgram(slp,stdgens)= u1);
    #Display(ResultOfStraightLineProgram(slp,stdgens)= u2);
    #return slp;
    #Display(g);

    Add( slp, [ [u1pos,1], [u2pos,1] ]);

    # Now u1^-1 * g * u2^-1 is the input matrix
    return [slp,[g, u1, u2], hs];

end
);



#####
# UnitriangularDecompositionSUEvenAndEvenChar
#####

InstallGlobalFunction(  UnitriangularDecompositionSUEvenAndEvenChar,
function(arg)
    local u1, u2, d, fld, f, alpha, c, r, j, a, z, i, Galois, phi, stdgens, g, ell, slp, hs, tmppos, AEMrespos, u1pos, u2pos, tvpos, T2pos, T3pos, T4pos, tmppos2, uipos, q, f2, TransvecAtAlpha2, TransvecAtAlpha3, TransvecAtAlpha4, test, ShiftTransvection3ByJ, ShiftTransvection3ByI, ShiftTransvection4, ShiftTransvection2ByJ, ShiftTransvection2ByI;

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

        i := i-1;

        instr := AEM( 4, AEMrespos, tmppos, i-1 );
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

        local cc, ell, instr, w, y, VS, basis;

        y := stdgens[7];
        w := y[1][1];
        basis := [];
        for ell in [1..f2] do
            Add(basis,(w^(q+1))^ell);
        od;

        VS := VectorSpace(GF(Characteristic(fld)),basis);

        cc := CoefficientsPrimitiveElementS( fld, alpha, Basis(VS,basis));  ### TODO Replace Basis! Basis is unbelieveable slow!
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
        # The first 14 entries are the stdgens and the inverses
        # s, t, del, v, x, s^-1, t^-1, del^-1, v^-1, x^-1
        slp := [    [1,1], [2,1], [3,1], [4,1], [5,1], [6,1], [7,1],
                    [1,-1],[2,-1],[3,-1],[4,-1],[5,-1], [6,-1], [7,-1]    ];
    fi;

    d := Length( g );
    fld := FieldOfMatrixList( stdgens );
    Galois := GaloisGroup(fld);
    Galois := Filtered(Galois, x -> Order(x) = 2);
    phi := Galois[1];

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
    q := RootInt(Characteristic(fld)^f);

    hs := HighestSlotOfSLP(slp);

    # We create the help variables for the block top left or bottom right
    T2pos := [ hs + 1 .. hs + f ];

    hs := hs + f;

    for ell in [ 1..f ] do
        Add(slp, [1,0] );
    od;

    for ell in [0..f-1] do

        Add(slp, [ [7, -ell, 4, -1, 7, -ell, 4 ,1 ], tmppos ] );
        Add(slp, [ [tmppos, 1, 5, -1, 6, 1, 5, 1, tmppos, -1 ], T2pos[ell+1] ] );

    od;

    # We create the help variables for the block in the bottom left
    T3pos := [ hs + 1 .. hs + f ];

    hs := hs + f;

    for ell in [ 1..f ] do
        Add(slp, [1,0] );
    od;

    for ell in [0..f-1] do

        Add(slp, [ [7, -(ell+ 0 ) , 4, -1, 7, -(ell+ 0 ), 4 ,1 ], tmppos ] );
        Add(slp, [ [1, -1, 5, -1, tmppos, 1, 5, -1, 6, 1, 5, 1, tmppos, -1 , 5, 1, 1, 1], T3pos[ell+1] ] );

    od;

    # We create the help variables for the diagonal
    f2 := Int((f * 0.5));
    T4pos := [ hs + 1 .. hs + f2 ];

    hs := hs + f2 ;

    for ell in [ 1..f2 ] do
        Add(slp, [1,0] );
    od;

    for ell in [1..f2] do

        Add(slp, [ [7, -ell, 1, -1, 2, 1, 1, 1 , 7, ell], T4pos[ell] ] );

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
    #ShiftTransvection2ByI(3);
    #ShiftTransvection2ByJ(2, 3);

    #y := stdgens[7];
    #w := y[1][1];
    #specialalpha := w^((q+1)/2);
    #basis := [];
    #for ell in [1..f2] do
    #    Add(basis,specialalpha^(-q)*(w^(q+1))^ell);
    #od;

    #VS := VectorSpace(GF(Characteristic(fld)),basis);
    #test := PseudoRandom(VS);

    #Display(test);
    #TransvecAtAlpha4(test);
    #ShiftTransvection4(7);

    #TransvecAtAlpha3(test);
    #ShiftTransvection3ByJ(4);
    #ShiftTransvection3ByI(10);

    #if fld = GF(4) then
    #    TransvecAtAlpha2(Z(2^2)^2);
    #    test:= slp;
    #    Add(test,[[tvpos,1],tvpos]);
    #    test := MakeSLP(test,7);
    #    Display(ResultOfStraightLineProgram(test,stdgens));
    #    Error("here");
    #fi;
    #test := slp;
    #Add(test, [[T2pos[2],1],T2pos[2]]);
    #test := MakeSLP(test,7);
    #Display(ResultOfStraightLineProgram(test,stdgens));

    #return MakeSLP(slp,7);

    ############
    # Start function
    ############

    g := MutableCopyMat(g);

    for c in [ d, d-1.. (d/2)+1 ] do

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
                #Mul := MutableCopyMat( One(g) );

                if (r+r+1 <> d+1) then

                    if r in [1..d/2] and r+1 in [1..d/2] then
                        TransvecAtAlpha2(z);
                        ShiftTransvection2ByI(r+1);
                        ShiftTransvection2ByJ(r, r+1);
                    else
                        TransvecAtAlpha2(-z^phi);
                        ShiftTransvection2ByI(d-r+1);
                        ShiftTransvection2ByJ(d-r,d-r+1);
                    fi;

                    #Mul[r+1][r] := z;
                    g[r+1] :=  g[r+1] + z *  g[r];
                    u1[r+1] := u1[r+1] + z * u1[r];

                    #Mul[d-r+1][d-r] := -z^phi;
                    g[d-r+1] :=  g[d-r+1] + -z^phi *  g[d-r];
                    u1[d-r+1] := u1[d-r+1] + -z^phi * u1[d-r];

                else
                    # Mul[r+1][r] := z;

                    TransvecAtAlpha4(z);
                    ShiftTransvection4(r+1);

                    g[r+1] :=  g[r+1] + z *  g[r];
                    u1[r+1] := u1[r+1] + z * u1[r];
                fi;

                Add(slp,[[tvpos,1,u1pos,1],u1pos]);

                #g := Mul * g;
                #u1 := Mul * u1;
            fi;


            # Second: Clear the rest of column c
            for i in [ r+1..d ] do

                if not IsZero(g[i][c]) then

                    z := -g[i][c] * a;

                    # add z times row r of g  to row i
                    # add z times row r of u1  to row i
                    #g[i] := g[i] + z*g[r];
                    #u1[i] := u1[i] + z*u1[r];
                    #Mul := MutableCopyMat( One(g) );

                    if (i+r <> d+1) then
                        if i in [1..d/2] and r in [1..d/2] then
                            TransvecAtAlpha2(z);
                            ShiftTransvection2ByI(i);
                            ShiftTransvection2ByJ(r, i);
                        elif i in [((d/2)+1)..d] and r in [((d/2)+1)..d] then
                            TransvecAtAlpha2(-z^phi);
                            ShiftTransvection2ByI(d-r+1);
                            ShiftTransvection2ByJ(d-i+1,d-r+1);   # LOOK SO PLUS
                        elif i+r < d+1 then
                            TransvecAtAlpha3(-z^phi);
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

                        #Mul[d-r+1][d-i+1] := -z^phi;
                        g[d-r+1] := g[d-r+1] + -z^phi * g[d-i+1];
                        u1[d-r+1] := u1[d-r+1] + -z^phi * u1[d-i+1];
                    else
                        #Mul[i][r] := z;
                        TransvecAtAlpha4(z);

                        if i > r then
                            ShiftTransvection4(i);
                        else
                            ShiftTransvection4(r);
                        fi;

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
                #Mul := MutableCopyMat( One(g) );

                if (c+c-1 <>  d+1) then

                    if c in [1..d/2] and c-1 in [1..d/2] then
                        TransvecAtAlpha2(z);
                        ShiftTransvection2ByI(c);
                        ShiftTransvection2ByJ(c-1, c);
                    else
                        TransvecAtAlpha2(-z^phi);
                        ShiftTransvection2ByI(d-c+2);
                        ShiftTransvection2ByJ(d-c+1,d-c+2);
                    fi;

                    #Mul[c][c-1] := z;
                    g{[ 1..d ]}[ c-1 ] := g{[ 1..d ]}[ c-1 ] + z * g{[1..d]}[c];
                    u2{[1..d]}[c-1] := u2{[1..d]}[c-1] + z * u2{[1..d]}[c];

                    #Mul[d-c+2][d-c+1] := -z^phi;
                    g{[ 1..d ]}[ d-c+1 ] := g{[ 1..d ]}[ d-c+1 ] + (-z^phi) * g{[1..d]}[d-c+2];
                    u2{[1..d]}[d-c+1] := u2{[1..d]}[d-c+1] + (-z^phi) * u2{[1..d]}[d-c+2];
                else
                    #Mul[c][c-1] := z;

                    TransvecAtAlpha4(z);
                    ShiftTransvection4(c);

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
                    #Mul := MutableCopyMat( One(g) );

                    if (c+j <>  d+1) then

                        if c in [1..d/2] and j in [1..d/2] then
                            TransvecAtAlpha2(z);
                            ShiftTransvection2ByI(c);
                            ShiftTransvection2ByJ(j, c);
                        elif c in [((d/2)+1)..d] and j in [((d/2)+1)..d] then
                            TransvecAtAlpha2(-z^phi);
                            ShiftTransvection2ByI(d-j+1);
                            ShiftTransvection2ByJ(d-c+1,d-j+1);
                        elif c+j < d+1 then
                            TransvecAtAlpha3(-z^phi);
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

                        #Mul[d-j+1][d-c+1] := -z^phi;
                        g{[1..d]}[d-c+1] :=  g{[1..d]}[d-c+1] + (-z^phi) *  g{[1..d]}[d-j+1];
                        u2{[1..d]}[d-c+1] := u2{[1..d]}[d-c+1] + (-z^phi) * u2{[1..d]}[d-j+1];
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

    #Add(slp,[[u1pos,1],u1pos]);
    #test := MakeSLP(slp,7);
    #if not(ResultOfStraightLineProgram(test,stdgens)= u1) then
    #    Error("u1");
    #fi;
    #Add(slp,[[u2pos,1],u2pos]);
    #test := MakeSLP(slp,7);
    #if not(ResultOfStraightLineProgram(test,stdgens)= u2) then
    #    Error("u1");
    #fi;
    #Display(ResultOfStraightLineProgram(slp,stdgens)= u1);
    #Display(ResultOfStraightLineProgram(slp,stdgens)= u2);
    #return slp;
    #Display(g);

    Add( slp, [ [u1pos,1], [u2pos,1] ]);

    # Now u1^-1 * g * u2^-1 is the input matrix
    return [slp,[g, u1, u2], hs];

end
);



#####
# UnitriangularDecompositionSUOdd
#####

InstallGlobalFunction(  UnitriangularDecompositionSUOdd,
function(arg)
    local u1, u2, d, fld, f, alpha, c, r, j, a, z, i, Mul, kon, x, Galois, phi, T2pos, T3pos, T4pos, T5pos, uipos,
    TransvecAtAlpha2, ShiftTransvection2ByI, ShiftTransvection2ByJ, TransvecAtAlpha3, ShiftTransvection3ByI, ShiftTransvection3ByJ,
    TransvecAtAlpha4, ShiftTransvection4, hs, ell, f2, q, stdgens, g, tmppos, tmppos2, u1pos, u2pos, AEMrespos, tvpos, test,
    TransvecAtAlpha5, ShiftTransvection5, slp;

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

        i := i-1;

        instr := AEM( 4, AEMrespos, tmppos, i-1 );
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

        local cc, ell, instr, w, y, specialalpha, VS, basis;

        y := stdgens[7];
        w := y[d][d];
        specialalpha := w^((q+1)/2);
        basis := [];
        for ell in [1..f2] do
            Add(basis,specialalpha^(-q)*(w^(q+1))^ell);
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

    #####
    # TransvectionAtAlpha5()
    #####

    TransvecAtAlpha5 := function( alpha )

        local cc, ell, instr, calcx, y, w, x, ell2, corri, findStart;

        # if omega = 1 then we overwrite the position for tv with Ti(1)
        if IsOne( alpha ) then
            Add(slp, [ [ T5pos[1], 1 ], tvpos ] );
            return One(fld)*(-2^(-1));
        fi;

        y := stdgens[7];
        w := y[d][d];
        calcx := [];
        for ell in [0..f-1] do
            Add(calcx,-2^(-1)*(w^(q+1))^ell);
        od;

        cc := CoefficientsPrimitiveElement( fld, alpha );
        instr := [];
        findStart := 0;

        for ell in [ 1..Length(cc) ] do

            if not IsZero( cc[ell] ) then
                if (findStart = 0) then
                    findStart := ell;
                fi;
                Append( instr, [ T5pos[ell], Int(cc[ell]) ] );
            fi;
        od;

        if Length( instr ) = 0 then
            Error("TransvecAtAlpha3: this should not happen");
        fi;

        Add( slp, [ instr,tvpos ] );

        x := calcx[findStart];
        corri := w^(findStart-1);

        for ell2 in [1..Int(cc[findStart])-1] do
                x := x + calcx[findStart] + corri * -(w^(findStart-1))^phi;
                corri := corri + w^(findStart-1);
        od;


        for ell in [ findStart+1..Length(cc) ] do
            for ell2 in [1..Int(cc[ell])] do
                x := x + calcx[ell] + corri * -(w^(ell-1))^phi;
                corri := corri + w^(ell-1);
            od;
        od;

        return x;

    end;

    #####
    # ShiftTransvection5()
    #####

    ShiftTransvection5 := function(i)
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
        # The first 14 entries are the stdgens and the inverses
        # s, t, del, v, x, s^-1, t^-1, del^-1, v^-1, x^-1
        slp := [    [1,1], [2,1], [3,1], [4,1], [5,1], [6,1], [7,1],
                    [1,-1],[2,-1],[3,-1],[4,-1],[5,-1], [6,-1], [7,-1]    ];
    fi;

    d := Length( g );
    fld := FieldOfMatrixList( [g] );
    Galois := GaloisGroup(fld);
    Galois := Filtered(Galois, x -> Order(x) = 2);
    phi := Galois[1];

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
    q := RootInt(Characteristic(fld)^f);

    hs := HighestSlotOfSLP(slp);

    # We create the help variables for the block top left or bottom right
    T2pos := [ hs + 1 .. hs + f ];

    hs := hs + f;

    for ell in [ 1..f ] do
        Add(slp, [1,0] );
    od;

    Add(slp, [ [4, -1, 6, 1, 4, 1, 6 , -1, 4,-1, 6,-1, 4,1,6,1 ], tmppos2 ] );

    for ell in [0..f-1] do

        Add(slp, [ [7, ell-((q^2+q)/2), 4, -2, 7, -(ell-((q^2+q)/2)), 4 ,2 ], tmppos ] );
        Add(slp, [ [5,-1,1,-1,tmppos, 1, tmppos2, -1, tmppos, -1, 1, 1, 5, 1], T2pos[ell+1] ] );

    od;

    # We create the help variables for the block in the bottom left
    T3pos := [ hs + 1 .. hs + f ];

    hs := hs + f;

    for ell in [ 1..f ] do
        Add(slp, [1,0] );
    od;

    Add(slp, [ [4, -1, 6, 1, 4, 1, 6 , -1, 4,-1, 6,-1, 4,1,6,1 ], tmppos2 ] );

    for ell in [0..f-1] do

        Add(slp, [ [7, ell, 4, -2, 7, -ell, 4 ,2 ], tmppos ] );
        Add(slp, [ [tmppos, 1, tmppos2, -1, tmppos, -1], T3pos[ell+1] ] );

    od;

    # We create the help variables for the diagonal
    f2 := Int((f * 0.5));
    T4pos := [ hs + 1 .. hs + f2 ];

    hs := hs + f2 ;

    for ell in [ 1..f2 ] do
        Add(slp, [1,0] );
    od;

    for ell in [1..f2] do

        Add(slp, [ [7, ell, 1, -1, 2, 1, 1, 1 , 7, -ell], T4pos[ell] ] );

    od;

    # We create the help variables for the centre row and column
    T5pos := [ hs + 1 .. hs + f ];

    hs := hs + f;

    for ell in [ 1..f ] do
        Add(slp, [1,0] );
    od;

    for ell in [0..f-1] do

        Add(slp, [ [7, ell , 4, -2, 7, -ell, 4 ,2 ], tmppos ] );
        Add(slp, [ [tmppos, 1, 6, 1, tmppos, -1], T5pos[ell+1] ] );

        #test := slp;
        #test := MakeSLP(test,7);
        #Display(ResultOfStraightLineProgram(test,stdgens));

    od;

    # We create the help variables for the shift

    uipos := [ hs + 1 .. (hs + ((d-1)/2)-2) ];

    hs := hs + (((d-1)/2)-2) ;

    for ell in [ 1 .. (((d-1)/2)-2)  ] do
        Add(slp, [1,0] );
    od;

    Add( slp, [[5,1],uipos[1]]);

    for ell in [2..(((d-1)/2)-2) ] do
            Add( slp, [ [ 4, -1, uipos[ell-1] , 1, 4, 1 ], uipos[ell] ] );
    od;

    ############
    # Tests
    ############

    #test :=PseudoRandom(fld);

    #Display(test);

    #TransvecAtAlpha2(test);
    #ShiftTransvection2ByI(5);
    #ShiftTransvection2ByJ(4, 5);

    #y := stdgens[7];
    #w := y[d][d];
    #specialalpha := w^((q+1)/2);
    #basis := [];
    #for ell in [1..f2] do
    #    Add(basis,specialalpha^(-q)*(w^(q+1))^ell);
    #od;

    #VS := VectorSpace(GF(Characteristic(fld)),basis);
    #test := PseudoRandom(VS);

    #Display(test);
    #TransvecAtAlpha4(test);
    #ShiftTransvection4(7);

    #TransvecAtAlpha3(test);
    #ShiftTransvection3ByJ(4);
    #ShiftTransvection3ByI(10);

    #Add(slp, [[tvpos,1],tvpos]);

    #TransvecAtAlpha5(test);
    #ShiftTransvection5(10);

    #return MakeSLP(slp,7);

    ############
    # Start function
    ############

    g := MutableCopyMat( g );

    for c in [ d, d-1.. ((d+1)/2)+1 ] do

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

            if (not(IsZero(g[(d+1)/2][c])) and (c <> ((d+1)/2))) then
                i := (d+1)/2;
                z := -g[i][c] * a;

                    # add z times row r of g  to row i
                    # add z times row r of u1  to row i
                    #g[i] := g[i] + z*g[r];
                    #u1[i] := u1[i] + z*u1[r];

                    if (i+r <> d+1) then
                        #Mul := List( One(SU(11,25)), ShallowCopy );
                        #Mul[i][r] := z;

                        x := TransvecAtAlpha5(-z^phi);
                        ShiftTransvection5(d-r+1);

                        #for x in fld do
                        #    if ((-z)^phi)*(-z)+x+x^phi = Zero(fld) then
                        #        #Mul[d-r+1][r] := x;
                        #        break;
                        #    fi;
                        #od;

                        g[d-r+1] := g[d-r+1] + x * g[r];
                        u1[d-r+1] := u1[d-r+1] + x * u1[r];

                        #Mul[d-r+1][d-i+1] := -z^phi;
                        g[d-r+1] := g[d-r+1] + -z^phi * g[d-i+1];
                        u1[d-r+1] := u1[d-r+1] + -z^phi * u1[d-i+1];

                        g[i] := g[i] + z*g[r];
                        u1[i] := u1[i] + z*u1[r];
                    else
                        #Mul[i][r] := z;

                        TransvecAtAlpha4(z);

                        if i > r then
                            ShiftTransvection4(i);
                        else
                            ShiftTransvection4(r);
                        fi;

                        g[i] := g[i] + z*g[r];
                        u1[i] := u1[i] + z*u1[r];
                    fi;

                    Add(slp,[[tvpos,1,u1pos,1],u1pos]);

                    #g := Mul * g;
                    #u1 := Mul * u1;

            fi;

            if not IsZero( g[r+1][c] ) and (r+1 <> (d+1)/2) then

                z := - g[r+1][c] * a;

                if (r+1 <> (d+1)/2) then

                    # add z times row r of g  to row r+1
                    # add z times row r of u1  to row r+1
                    # g[r+1] :=  g[r+1] + z *  g[r];
                    # u1[r+1] := u1[r+1] + z * u1[r];
                    #Mul := List( One(G), ShallowCopy );

                    if (r+r+1 <> d+1) then

                        if r+1 in [1..(d+1)/2] then
                            TransvecAtAlpha2(z);
                            ShiftTransvection2ByI(r+1);
                            ShiftTransvection2ByJ(r, r+1);
                        else
                            TransvecAtAlpha2(-z^phi);
                            ShiftTransvection2ByI(d-r+1);
                            ShiftTransvection2ByJ(d-r,d-r+1);
                        fi;

                        #Mul[r+1][r] := z;
                        g[r+1] :=  g[r+1] + z *  g[r];
                        u1[r+1] := u1[r+1] + z * u1[r];

                        #Mul[d-r+1][d-r] := -(z)^phi;
                        g[d-r+1] :=  g[d-r+1] + -z^phi *  g[d-r];
                        u1[d-r+1] := u1[d-r+1] + -z^phi * u1[d-r];
                    else
                        #Mul[r+1][r] := z;

                        TransvecAtAlpha4(z);
                        ShiftTransvection4(r+1);

                        g[r+1] :=  g[r+1] + z *  g[r];
                        u1[r+1] := u1[r+1] + z * u1[r];
                    fi;

                    Add(slp,[[tvpos,1,u1pos,1],u1pos]);

                    #g := Mul * g;
                    #u1 := Mul * u1;

                else
                    #Mul := List( One(G), ShallowCopy );

                    if (r+r+1 <> d+1) then

                        #Display("Test");
                        #Mul[r+1][r] := z;
                        g[r+1] :=  g[r+1] + z *  g[r];
                        u1[r+1] := u1[r+1] + z * u1[r];

                        #Mul[d-r+1][d-r] := -z^phi;
                        g[d-r+1] :=  g[d-r+1] + -z^phi *  g[d-r];
                        u1[d-r+1] := u1[d-r+1] + -z^phi * u1[d-r];
                    else
                        #Mul[r+1][r] := z;

                        TransvecAtAlpha4(z);
                        ShiftTransvection4(r+1);

                        g[r+1] :=  g[r+1] + z *  g[r];
                        u1[r+1] := u1[r+1] + z * u1[r];
                    fi;

                    Add(slp,[[tvpos,1,u1pos,1],u1pos]);

                    #g := Mul * g;
                    #u1 := Mul * u1;

                fi;
            fi;


            # Second: Clear the rest of column c
            for i in [ r+2..d ] do

                if not IsZero(g[i][c]) and (i <> (d+1)/2) then

                    z := -g[i][c] * a;

                    # add z times row r of g  to row i
                    # add z times row r of u1  to row i
                    #g[i] := g[i] + z*g[r];
                    #u1[i] := u1[i] + z*u1[r];
                    #Mul := List( One(G), ShallowCopy );

                    if (i+r <> d+1) then

                        if i in [1..(d+1)/2] and r in [1..(d+1)/2] then
                            TransvecAtAlpha2(z);
                            ShiftTransvection2ByI(i);
                            ShiftTransvection2ByJ(r, i);
                        elif i in [(((d+1)/2)+1)..d] and r in [(((d+1)/2)+1)..d] then
                            TransvecAtAlpha2(-z^phi);
                            ShiftTransvection2ByI(d-r+1);
                            ShiftTransvection2ByJ(d-i+1,d-r+1);     # Davor d-r in erster Komponente
                        elif i+r < d+1 then
                            TransvecAtAlpha3(-z^phi);
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

                        #Mul[d-r+1][d-i+1] := -z^phi;
                        g[d-r+1] := g[d-r+1] + -z^phi * g[d-i+1];
                        u1[d-r+1] := u1[d-r+1] + -z^phi * u1[d-i+1];
                    else
                        TransvecAtAlpha4(z);

                        if i > r then
                            ShiftTransvection4(i);
                        else
                            ShiftTransvection4(r);
                        fi;

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


            if not IsZero(g[r][(d+1)/2]) and (r <> ((d+1)/2)) then
                j := (d+1)/2;
                z := -g[r][j] * a;

                # add z times row r of g  to row i
                # add z times row r of u1  to row i
                #g[i] := g[i] + z*g[r];
                #u1[i] := u1[i] + z*u1[r];

                if (c+j <> d+1) then
                    #Mul := List( One(SU(11,25)), ShallowCopy );
                    #Mul[c][j] := z;

                    x := TransvecAtAlpha5(z);
                    ShiftTransvection5(c);

                    #for x in fld do
                    #    if ((-z)^phi)*(-z)+x+x^phi = Zero(fld) then
                    #        #Mul[c][d-c+1] := x;
                    #        break;
                    #    fi;
                    #od;
                    #Mul[d-j+1][d-c+1] := -z^phi;
                    #Mul[c][d-c+1] := x;
                    #Display(g*Mul);

                    g{[1..d]}[d-c+1] :=  g{[1..d]}[d-c+1] + x *  g{[1..d]}[c];
                    u2{[1..d]}[d-c+1] := u2{[1..d]}[d-c+1] + x * u2{[1..d]}[c];

                    g{[1..d]}[d-c+1] :=  g{[1..d]}[d-c+1] + (-z^phi) *  g{[1..d]}[d-j+1];
                    u2{[1..d]}[d-c+1] := u2{[1..d]}[d-c+1] + (-z^phi) * u2{[1..d]}[d-j+1];

                    g{[1..d]}[j] :=  g{[1..d]}[j] + z *  g{[1..d]}[c];
                    u2{[1..d]}[j] := u2{[1..d]}[j] + z * u2{[1..d]}[c];

                else
                    #Mul[i][r] := z;

                    TransvecAtAlpha4(z);

                    if c > j then
                        ShiftTransvection4(c);
                    else
                        ShiftTransvection4(j);
                    fi;

                    g{[1..d]}[j] :=  g{[1..d]}[j] + z *  g{[1..d]}[c];
                    u2{[1..d]}[j] := u2{[1..d]}[j] + z * u2{[1..d]}[c];
                fi;

                Add(slp,[[u2pos,1,tvpos,1],u2pos]);

                #g := g * Mul;
                #u2 := u2 * Mul;
            fi;


            if not IsZero( g[r][c-1] ) and (c-1 <> (d+1)/2) then

                z := -g[r][c-1] * a;

                # add z times column c of g to column c-1
                # add z times column c of u2 to column c-1
                #g{[ 1..d ]}[ c-1 ] := g{[ 1..d ]}[ c-1 ] + z * g{[1..d]}[c];
                #u2{[1..d]}[c-1] := u2{[1..d]}[c-1] + z * u2{[1..d]}[c];

                #Mul := List( One(G), ShallowCopy );

                if (c+c-1 <>  d+1) then

                    if c in [1..(d+1)/2] and c-1 in [1..(d+1)/2] then
                        TransvecAtAlpha2(z);
                        ShiftTransvection2ByI(c);
                        ShiftTransvection2ByJ(c-1, c);
                    else
                        TransvecAtAlpha2(-z^phi);
                        ShiftTransvection2ByI(d-c+2);
                        ShiftTransvection2ByJ(d-c+1,d-c+2);
                    fi;

                    #Mul[c][c-1] := z;
                    g{[ 1..d ]}[ c-1 ] := g{[ 1..d ]}[ c-1 ] + z * g{[1..d]}[c];
                    u2{[1..d]}[c-1] := u2{[1..d]}[c-1] + z * u2{[1..d]}[c];

                    #Mul[d-c+2][d-c+1] := -z^phi;
                    g{[ 1..d ]}[ d-c+1 ] := g{[ 1..d ]}[ d-c+1 ] + (-z^phi) * g{[1..d]}[d-c+2];
                    u2{[1..d]}[d-c+1] := u2{[1..d]}[d-c+1] + (-z^phi) * u2{[1..d]}[d-c+2];
                else
                    #Mul[c][c-1] := z;

                    TransvecAtAlpha4(z);
                    ShiftTransvection4(c);

                    g{[ 1..d ]}[ c-1 ] := g{[ 1..d ]}[ c-1 ] + z * g{[1..d]}[c];
                    u2{[1..d]}[c-1] := u2{[1..d]}[c-1] + z * u2{[1..d]}[c];
                fi;

                Add(slp,[[u2pos,1,tvpos,1],u2pos]);

                #g := g * Mul;
                #u2 := u2 * Mul;
            fi;


            # Now clear the rest of row r
            for j in [ c-2, c-3..1 ] do

                if not IsZero( g[r][j] ) and (j <> (d+1)/2) then

                    z := - g[r][j] * a;

                    # add z times column c of g to column j
                    # add z times column c of u2 to column j
                    # g{[1..d]}[j] :=  g{[1..d]}[j] + z *  g{[1..d]}[c];
                    #u2{[1..d]}[j] := u2{[1..d]}[j] + z * u2{[1..d]}[c];

                    #Mul := List( One(G), ShallowCopy );

                    if (c+j <> d+1) then

                        if c in [1..(d+1)/2] and j in [1..(d+1)/2] then
                            TransvecAtAlpha2(z);
                            ShiftTransvection2ByI(c);
                            ShiftTransvection2ByJ(j, c);
                        elif c in [(((d+1)/2)+1)..d] and j in [(((d+1)/2)+1)..d] then
                            TransvecAtAlpha2(-z^phi);
                            ShiftTransvection2ByI(d-j+1);
                            ShiftTransvection2ByJ(d-c+1,d-j+1);
                        elif c+j < d+1 then
                            TransvecAtAlpha3(-z^phi);
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

                        #Mul[d-j+1][d-c+1] := -z^phi;
                        g{[1..d]}[d-c+1] :=  g{[1..d]}[d-c+1] + (-z^phi) *  g{[1..d]}[d-j+1];
                        u2{[1..d]}[d-c+1] := u2{[1..d]}[d-c+1] + (-z^phi) * u2{[1..d]}[d-j+1];
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

    #Add(slp,[[u1pos,1],u1pos]);
    #test := MakeSLP(slp,7);
    #if not(ResultOfStraightLineProgram(test,stdgens)= u1) then
    #    Error("u1");
    #fi;
    #Add(slp,[[u2pos,1],u2pos]);
    #test := MakeSLP(slp,7);
    #if not(ResultOfStraightLineProgram(test,stdgens)= u2) then
    #    Error("u2");
    #fi;

    #Add(slp,[[u1pos,1],u1pos]);
    #slp := MakeSLP(slp,7);
    #Display(ResultOfStraightLineProgram(slp,stdgens));
    #Display(ResultOfStraightLineProgram(slp,stdgens)= u1);
    #Display(ResultOfStraightLineProgram(slp,stdgens)= u2);
    #return slp;
    #Display(g);

    Add( slp, [ [u1pos,1], [u2pos,1] ]);

    # Now u1^-1 * g * u2^-1 is the input matrix
    return [slp,[g, u1, u2], hs];

end
);



#####
# UnitriangularDecompositionSUOddAndEvenChar
#####

InstallGlobalFunction(  UnitriangularDecompositionSUOddAndEvenChar,
function(arg)
    local u1, u2, d, fld, f, alpha, c, r, j, a, z, i, Mul, kon, x, Galois, phi, T2pos, T3pos, T4pos, T5pos, uipos,
    TransvecAtAlpha2, ShiftTransvection2ByI, ShiftTransvection2ByJ, TransvecAtAlpha3, ShiftTransvection3ByI, ShiftTransvection3ByJ,
    TransvecAtAlpha4, ShiftTransvection4, hs, ell, f2, q, stdgens, g, tmppos, tmppos2, u1pos, u2pos, AEMrespos, tvpos, test,
    TransvecAtAlpha5, ShiftTransvection5, slp;

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

        i := i-1;

        instr := AEM( 4, AEMrespos, tmppos, i-1 );
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

        local cc, ell, instr, w, y, specialalpha, VS, basis;

        y := stdgens[7];
        w := y[((d+1)/2)-1][((d+1)/2)-1];
        basis := [];
        for ell in [1..f2] do
            Add(basis,(w^(q+1))^ell);
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

    #####
    # TransvectionAtAlpha5()
    #####

    TransvecAtAlpha5 := function( alpha )

        local cc, ell, instr, calcx, y, w, x, ell2, corri, findStart;

        # if omega = 1 then we overwrite the position for tv with Ti(1)
        if IsOne( alpha ) then
            Add(slp, [ [ T5pos[1], 1 ], tvpos ] );
            return (stdgens[6])[((d+1)/2)-1,((d+1)/2)+1];
        fi;

        y := stdgens[7];
        w := y[((d+1)/2)-1][((d+1)/2)-1];
        calcx := [];
        for ell in [0..f-1] do
            Add(calcx,(stdgens[6])[((d+1)/2)-1,((d+1)/2)+1]*(w^(q+1))^ell);
        od;

        cc := CoefficientsPrimitiveElement( fld, alpha );
        instr := [];
        findStart := 0;

        for ell in [ 1..Length(cc) ] do

            if not IsZero( cc[ell] ) then
                if (findStart = 0) then
                    findStart := ell;
                fi;
                Append( instr, [ T5pos[ell], Int(cc[ell]) ] );
            fi;
        od;

        if Length( instr ) = 0 then
            Error("TransvecAtAlpha3: this should not happen");
        fi;

        Add( slp, [ instr,tvpos ] );

        x := calcx[findStart];
        corri := w^(findStart-1);

        for ell2 in [1..Int(cc[findStart])-1] do
                x := x + calcx[findStart] + corri * -(w^(findStart-1))^phi;
                corri := corri + w^(findStart-1);
        od;


        for ell in [ findStart+1..Length(cc) ] do
            for ell2 in [1..Int(cc[ell])] do
                x := x + calcx[ell] + corri * -(w^(ell-1))^phi;
                corri := corri + w^(ell-1);
            od;
        od;

        return x;

    end;

    #####
    # ShiftTransvection5()
    #####

    ShiftTransvection5 := function(i)
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
        # The first 14 entries are the stdgens and the inverses
        # s, t, del, v, x, s^-1, t^-1, del^-1, v^-1, x^-1
        slp := [    [1,1], [2,1], [3,1], [4,1], [5,1], [6,1], [7,1],
                    [1,-1],[2,-1],[3,-1],[4,-1],[5,-1], [6,-1], [7,-1]    ];
                   
        # Change generators to match the one of odd characteristic
        Add(slp, [[1,-1,4,-1,6,1,4,1,1,1],6]);
        Add(slp, [[6,-1],13]);
        Add(slp, [[1,1,4,1,5,1,4,-1,7,1,4,1,5,-1,4,-1,1,1],7]);
        Add(slp, [[7,-1],14]);
    fi;

    d := Length( g );
    fld := FieldOfMatrixList( [g] );
    Galois := GaloisGroup(fld);
    Galois := Filtered(Galois, x -> Order(x) = 2);
    phi := Galois[1];

    # To create an MSLP, we allocate all the memory needed at the beginning.
    Add( slp, [1,0] );        tmppos       := Length(slp)-4;    #15
    Add( slp, [1,0] );        AEMrespos    := Length(slp)-4;    #16
    Add( slp, [1,0] );        u1pos        := Length(slp)-4;    #17
    Add( slp, [1,0] );        u2pos        := Length(slp)-4;    #18
    Add( slp, [1,0] );        tvpos        := Length(slp)-4;    #19
    Add( slp, [1,0] );        tmppos2      := Length(slp)-4;    #20


    u1 := MutableCopyMat( One(g) );
    u2 := MutableCopyMat( One(g) );

    # If g is already a monomial matrix return u_1 = u_2 = I_d
    if TestIfMonomial( g ) then
        Add( slp, [ [1,0],[1,0] ] );
        return [ slp, [u1,g,u2] ];
    fi;

    f := LogInt(Size(fld), Characteristic(fld)); #ie q=p^f
    q := RootInt(Characteristic(fld)^f);

    hs := HighestSlotOfSLP(slp);

    # We create the help variables for the block top left or bottom right
    T2pos := [ hs + 1 .. hs + f ];

    hs := hs + f;

    for ell in [ 1..f ] do
        Add(slp, [1,0] );
    od;

    Add(slp, [ [4, -1, 6, 1, 4, 1, 6 , -1, 4,-1, 6,-1, 4,1,6,1 ], tmppos2 ] );

    for ell in [0..f-1] do

        Add(slp, [ [7, ell, 4, -2, 7, -(ell), 4 ,2 ], tmppos ] );
        Add(slp, [ [5,-1,1,-1,tmppos, 1, tmppos2, -1, tmppos, -1, 1, 1, 5, 1], T2pos[ell+1] ] );
        
    od;

    # We create the help variables for the block in the bottom left
    T3pos := [ hs + 1 .. hs + f ];

    hs := hs + f;

    for ell in [ 1..f ] do
        Add(slp, [1,0] );
    od;

    Add(slp, [ [4, -1, 6, 1, 4, 1, 6 , -1, 4,-1, 6,-1, 4,1,6,1 ], tmppos2 ] );

    for ell in [0..f-1] do

        Add(slp, [ [7, ell, 4, -2, 7, -ell, 4 ,2 ], tmppos ] );
        Add(slp, [ [tmppos, 1, tmppos2, -1, tmppos, -1], T3pos[ell+1] ] );

    od;

    # We create the help variables for the diagonal
    f2 := Int((f * 0.5));
    T4pos := [ hs + 1 .. hs + f2 ];

    hs := hs + f2 ;

    for ell in [ 1..f2 ] do
        Add(slp, [1,0] );
    od;

    for ell in [1..f2] do

        Add(slp, [ [7, ell, 1, -1, 2, 1, 1, 1 , 7, -ell], T4pos[ell] ] );

    od;

    # We create the help variables for the centre row and column
    T5pos := [ hs + 1 .. hs + f ];

    hs := hs + f;

    for ell in [ 1..f ] do
        Add(slp, [1,0] );
    od;

    for ell in [0..f-1] do

        Add(slp, [ [7, ell , 4, -2, 7, -ell, 4 ,2 ], tmppos ] );
        Add(slp, [ [tmppos, 1, 6, 1, tmppos, -1], T5pos[ell+1] ] );

        #test := slp;
        #test := MakeSLP(test,7);
        #Display(ResultOfStraightLineProgram(test,stdgens));

    od;

    # We create the help variables for the shift

    uipos := [ hs + 1 .. (hs + ((d-1)/2)-2) ];

    hs := hs + (((d-1)/2)-2) ;

    for ell in [ 1 .. (((d-1)/2)-2)  ] do
        Add(slp, [1,0] );
    od;

    Add( slp, [[5,1],uipos[1]]);

    for ell in [2..(((d-1)/2)-2) ] do
            Add( slp, [ [ 4, -1, uipos[ell-1] , 1, 4, 1 ], uipos[ell] ] );
    od;

    ############
    # Tests
    ############

    #test :=PseudoRandom(fld);

    #Display(test);

    #TransvecAtAlpha2(test);
    #ShiftTransvection2ByI(3);
    #ShiftTransvection2ByJ(1, 3);

    #y := stdgens[7];
    #w := y[d][d];
    #specialalpha := w^((q+1)/2);
    #basis := [];
    #for ell in [1..f2] do
    #    Add(basis,specialalpha^(-q)*(w^(q+1))^ell);
    #od;

    #VS := VectorSpace(GF(Characteristic(fld)),basis);
    #test := PseudoRandom(VS);

    #Display(test);
    #TransvecAtAlpha4(test);
    #ShiftTransvection4(7);

    #TransvecAtAlpha3(test);
    #ShiftTransvection3ByJ(3);
    #ShiftTransvection3ByI(6);

    #Add(slp, [[T4pos[2],1],tvpos]);

    #TransvecAtAlpha5(test);
    #ShiftTransvection5(6);

    #return MakeSLP(slp,7);

    ############
    # Start function
    ############

    g := MutableCopyMat( g );

    for c in [ d, d-1.. ((d+1)/2)+1 ] do

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

            if (not(IsZero(g[(d+1)/2][c])) and (c <> ((d+1)/2))) then
                i := (d+1)/2;
                z := -g[i][c] * a;

                    # add z times row r of g  to row i
                    # add z times row r of u1  to row i
                    #g[i] := g[i] + z*g[r];
                    #u1[i] := u1[i] + z*u1[r];

                    if (i+r <> d+1) then
                        #Mul := List( One(SU(d,q)), ShallowCopy );
                        #Mul[i][r] := z;

                        x := TransvecAtAlpha5(-z^phi);
                        ShiftTransvection5(d-r+1);

                        #for x in fld do
                        #    if ((-z)^phi)*(-z)+x+x^phi = Zero(fld) then
                        #        #Mul[d-r+1][r] := x;
                        #        break;
                        #    fi;
                        #od;

                        #Mul[d-r+1,r] := x;
                        g[d-r+1] := g[d-r+1] + x * g[r];
                        u1[d-r+1] := u1[d-r+1] + x * u1[r];

                        #Mul[d-r+1][d-i+1] := -z^phi;
                        g[d-r+1] := g[d-r+1] + -z^phi * g[d-i+1];
                        u1[d-r+1] := u1[d-r+1] + -z^phi * u1[d-i+1];

                        g[i] := g[i] + z*g[r];
                        u1[i] := u1[i] + z*u1[r];
                    else
                        #Mul[i][r] := z;

                        TransvecAtAlpha4(z);

                        if i > r then
                            ShiftTransvection4(i);
                        else
                            ShiftTransvection4(r);
                        fi;

                        g[i] := g[i] + z*g[r];
                        u1[i] := u1[i] + z*u1[r];
                    fi;

                    Add(slp,[[tvpos,1,u1pos,1],u1pos]);
                    
                    #g := Mul * g;
                    #u1 := Mul * u1;

            fi;

            if not IsZero( g[r+1][c] ) and (r+1 <> (d+1)/2) then

                z := - g[r+1][c] * a;

                if (r+1 <> (d+1)/2) then

                    # add z times row r of g  to row r+1
                    # add z times row r of u1  to row r+1
                    # g[r+1] :=  g[r+1] + z *  g[r];
                    # u1[r+1] := u1[r+1] + z * u1[r];
                    #Mul := List( One(G), ShallowCopy );

                    if (r+r+1 <> d+1) then

                        if r+1 in [1..(d+1)/2] then
                            TransvecAtAlpha2(z);
                            ShiftTransvection2ByI(r+1);
                            ShiftTransvection2ByJ(r, r+1);
                        else
                            TransvecAtAlpha2(-z^phi);
                            ShiftTransvection2ByI(d-r+1);
                            ShiftTransvection2ByJ(d-r,d-r+1);
                        fi;

                        #Mul[r+1][r] := z;
                        g[r+1] :=  g[r+1] + z *  g[r];
                        u1[r+1] := u1[r+1] + z * u1[r];

                        #Mul[d-r+1][d-r] := -(z)^phi;
                        g[d-r+1] :=  g[d-r+1] + -z^phi *  g[d-r];
                        u1[d-r+1] := u1[d-r+1] + -z^phi * u1[d-r];
                    else
                        #Mul[r+1][r] := z;

                        TransvecAtAlpha4(z);
                        ShiftTransvection4(r+1);

                        g[r+1] :=  g[r+1] + z *  g[r];
                        u1[r+1] := u1[r+1] + z * u1[r];
                    fi;

                    Add(slp,[[tvpos,1,u1pos,1],u1pos]);

                    #g := Mul * g;
                    #u1 := Mul * u1;

                else
                    #Mul := List( One(G), ShallowCopy );

                    if (r+r+1 <> d+1) then

                        #Display("Test");
                        #Mul[r+1][r] := z;
                        g[r+1] :=  g[r+1] + z *  g[r];
                        u1[r+1] := u1[r+1] + z * u1[r];

                        #Mul[d-r+1][d-r] := -z^phi;
                        g[d-r+1] :=  g[d-r+1] + -z^phi *  g[d-r];
                        u1[d-r+1] := u1[d-r+1] + -z^phi * u1[d-r];
                    else
                        #Mul[r+1][r] := z;

                        TransvecAtAlpha4(z);
                        ShiftTransvection4(r+1);

                        g[r+1] :=  g[r+1] + z *  g[r];
                        u1[r+1] := u1[r+1] + z * u1[r];
                    fi;

                    Add(slp,[[tvpos,1,u1pos,1],u1pos]);

                    #g := Mul * g;
                    #u1 := Mul * u1;
                    
                fi;
            fi;


            # Second: Clear the rest of column c
            for i in [ r+2..d ] do

                if not IsZero(g[i][c]) and (i <> (d+1)/2) then

                    z := -g[i][c] * a;

                    # add z times row r of g  to row i
                    # add z times row r of u1  to row i
                    #g[i] := g[i] + z*g[r];
                    #u1[i] := u1[i] + z*u1[r];
                    #Mul := List( One(G), ShallowCopy );

                    if (i+r <> d+1) then

                        if i in [1..(d+1)/2] and r in [1..(d+1)/2] then
                            TransvecAtAlpha2(z);
                            ShiftTransvection2ByI(i);
                            ShiftTransvection2ByJ(r, i);
                        elif i in [(((d+1)/2)+1)..d] and r in [(((d+1)/2)+1)..d] then
                            TransvecAtAlpha2(-z^phi);
                            ShiftTransvection2ByI(d-r+1);
                            ShiftTransvection2ByJ(d-i+1,d-r+1);     # Vorher d-r
                        elif i+r < d+1 then
                            TransvecAtAlpha3(-z^phi);
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

                        #Mul[d-r+1][d-i+1] := -z^phi;
                        g[d-r+1] := g[d-r+1] + -z^phi * g[d-i+1];
                        u1[d-r+1] := u1[d-r+1] + -z^phi * u1[d-i+1];
                    else
                        TransvecAtAlpha4(z);

                        if i > r then
                            ShiftTransvection4(i);
                        else
                            ShiftTransvection4(r);
                        fi;

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


            if not IsZero(g[r][(d+1)/2]) and (r <> ((d+1)/2)) then
                j := (d+1)/2;
                z := -g[r][j] * a;

                # add z times row r of g  to row i
                # add z times row r of u1  to row i
                #g[i] := g[i] + z*g[r];
                #u1[i] := u1[i] + z*u1[r];

                if (c+j <> d+1) then
                    #Mul := List( One(SU(11,25)), ShallowCopy );
                    #Mul[c][j] := z;

                    x := TransvecAtAlpha5(z);
                    ShiftTransvection5(c);

                    #for x in fld do
                    #    if ((-z)^phi)*(-z)+x+x^phi = Zero(fld) then
                    #        #Mul[c][d-c+1] := x;
                    #        break;
                    #    fi;
                    #od;
                    #Mul[d-j+1][d-c+1] := -z^phi;
                    #Mul[c][d-c+1] := x;
                    #Display(g*Mul);

                    g{[1..d]}[d-c+1] :=  g{[1..d]}[d-c+1] + x *  g{[1..d]}[c];
                    u2{[1..d]}[d-c+1] := u2{[1..d]}[d-c+1] + x * u2{[1..d]}[c];

                    g{[1..d]}[d-c+1] :=  g{[1..d]}[d-c+1] + (-z^phi) *  g{[1..d]}[d-j+1];
                    u2{[1..d]}[d-c+1] := u2{[1..d]}[d-c+1] + (-z^phi) * u2{[1..d]}[d-j+1];

                    g{[1..d]}[j] :=  g{[1..d]}[j] + z *  g{[1..d]}[c];
                    u2{[1..d]}[j] := u2{[1..d]}[j] + z * u2{[1..d]}[c];

                else
                    #Mul[i][r] := z;

                    TransvecAtAlpha4(z);

                    if c > j then
                        ShiftTransvection4(c);
                    else
                        ShiftTransvection4(j);
                    fi;

                    g{[1..d]}[j] :=  g{[1..d]}[j] + z *  g{[1..d]}[c];
                    u2{[1..d]}[j] := u2{[1..d]}[j] + z * u2{[1..d]}[c];
                fi;

                Add(slp,[[u2pos,1,tvpos,1],u2pos]);

                #g := g * Mul;
                #u2 := u2 * Mul;
                
            fi;


            if not IsZero( g[r][c-1] ) and (c-1 <> (d+1)/2) then

                z := -g[r][c-1] * a;

                # add z times column c of g to column c-1
                # add z times column c of u2 to column c-1
                #g{[ 1..d ]}[ c-1 ] := g{[ 1..d ]}[ c-1 ] + z * g{[1..d]}[c];
                #u2{[1..d]}[c-1] := u2{[1..d]}[c-1] + z * u2{[1..d]}[c];

                #Mul := List( One(G), ShallowCopy );

                if (c+c-1 <>  d+1) then

                    if c in [1..(d+1)/2] and c-1 in [1..(d+1)/2] then
                        TransvecAtAlpha2(z);
                        ShiftTransvection2ByI(c);
                        ShiftTransvection2ByJ(c-1, c);
                    else
                        TransvecAtAlpha2(-z^phi);
                        ShiftTransvection2ByI(d-c+2);
                        ShiftTransvection2ByJ(d-c+1,d-c+2);
                    fi;

                    #Mul[c][c-1] := z;
                    g{[ 1..d ]}[ c-1 ] := g{[ 1..d ]}[ c-1 ] + z * g{[1..d]}[c];
                    u2{[1..d]}[c-1] := u2{[1..d]}[c-1] + z * u2{[1..d]}[c];

                    #Mul[d-c+2][d-c+1] := -z^phi;
                    g{[ 1..d ]}[ d-c+1 ] := g{[ 1..d ]}[ d-c+1 ] + (-z^phi) * g{[1..d]}[d-c+2];
                    u2{[1..d]}[d-c+1] := u2{[1..d]}[d-c+1] + (-z^phi) * u2{[1..d]}[d-c+2];
                else
                    #Mul[c][c-1] := z;

                    TransvecAtAlpha4(z);
                    ShiftTransvection4(c);

                    g{[ 1..d ]}[ c-1 ] := g{[ 1..d ]}[ c-1 ] + z * g{[1..d]}[c];
                    u2{[1..d]}[c-1] := u2{[1..d]}[c-1] + z * u2{[1..d]}[c];
                fi;

                Add(slp,[[u2pos,1,tvpos,1],u2pos]);

                #g := g * Mul;
                #u2 := u2 * Mul;
                
            fi;


            # Now clear the rest of row r
            for j in [ c-2, c-3..1 ] do

                if not IsZero( g[r][j] ) and (j <> (d+1)/2) then

                    z := - g[r][j] * a;

                    # add z times column c of g to column j
                    # add z times column c of u2 to column j
                    # g{[1..d]}[j] :=  g{[1..d]}[j] + z *  g{[1..d]}[c];
                    #u2{[1..d]}[j] := u2{[1..d]}[j] + z * u2{[1..d]}[c];

                    #Mul := List( One(G), ShallowCopy );

                    if (c+j <> d+1) then

                        if c in [1..(d+1)/2] and j in [1..(d+1)/2] then
                            TransvecAtAlpha2(z);
                            ShiftTransvection2ByI(c);
                            ShiftTransvection2ByJ(j, c);
                        elif c in [(((d+1)/2)+1)..d] and j in [(((d+1)/2)+1)..d] then
                            TransvecAtAlpha2(-z^phi);
                            ShiftTransvection2ByI(d-j+1);
                            ShiftTransvection2ByJ(d-c+1,d-j+1);
                        elif c+j < d+1 then
                            TransvecAtAlpha3(-z^phi);
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

                        #Mul[d-j+1][d-c+1] := -z^phi;
                        g{[1..d]}[d-c+1] :=  g{[1..d]}[d-c+1] + (-z^phi) *  g{[1..d]}[d-j+1];
                        u2{[1..d]}[d-c+1] := u2{[1..d]}[d-c+1] + (-z^phi) * u2{[1..d]}[d-j+1];
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

    #test := slp;
    #Add(test,[[u1pos,1],u1pos]);
    #test := MakeSLP(test,7);
    #if not(ResultOfStraightLineProgram(test,stdgens)= u1) then
    #    Error("u1");
    #fi;
    #test := slp;
    #Add(test,[[u2pos,1],u2pos]);
    #test := MakeSLP(test,7);
    #if not(ResultOfStraightLineProgram(test,stdgens)= u2) then
    #    Error("u2");
    #fi;

    #Add(slp,[[u1pos,1],u1pos]);
    #slp := MakeSLP(slp,7);
    #Display(ResultOfStraightLineProgram(slp,stdgens));
    #Display(ResultOfStraightLineProgram(slp,stdgens)= u1);
    #Display(ResultOfStraightLineProgram(slp,stdgens)= u2);
    #return slp;
    #Display(g);

    Add( slp, [ [u1pos,1], [u2pos,1] ]);

    # Now u1^-1 * g * u2^-1 is the input matrix
    return [slp,[g, u1, u2], hs];

end
);



#####
# UnitriangularDecompositionSU
#####

InstallGlobalFunction(  UnitriangularDecompositionSU,
function(g)

    if (Length(g) mod 2) = 0 then
        return UnitriangularDecompositionSUEven(g);
    else
        return UnitriangularDecompositionSUOdd(g);
    fi;

end
);



#####
# LGOStandardGensSU
#####

InstallGlobalFunction(  LGOStandardGensSU,
function( d, q )

    local w, alpha, s, t, delta, u, v, x, y, J, fld;
    
    if d < 6 then
        Error("LGOStandardGens: d has to be at least 6\n");
        return;
    fi;
    
    if (q mod 2 = 0) then
        return LGOStandardGensSUEvenChar(d,q);
    fi;

    w := PrimitiveElement(GF(q^2));
    alpha := w^((q+1)/2);
    fld := GF(q^2);

    s := IdentityMat( d, fld );
    s[1][1] := Zero(fld);
    s[d][d] := Zero(fld);
    s[1][d] := alpha;
    s[d][1] := alpha^(-q);

    t := IdentityMat( d, fld );
    t[1][d] := alpha;

    delta := IdentityMat( d, fld );
    delta[1][1] := w^(q+1);
    delta[d][d] := w^((-(q+1)));

    v := 0 * IdentityMat( d, fld );
    if (IsEvenInt(d)) then
        v[d/2][1] := One(fld);
        v{[1..(d/2)-1]}{[2..d/2]} := IdentityMat((d/2)-1,fld);
        v[d/2+1][d] := One(fld);
        v{[(d/2)+2..d]}{[(d/2)+1..d-1]} := IdentityMat((d/2)-1,fld);
    else
        v[(d-1)/2][1] := One(fld);
        v{[1..((d-1)/2)-1]}{[2..(d-1)/2]} := IdentityMat(((d-1)/2)-1,fld);
        v[((d+1)/2)+1][d] := One(fld);
        v[(d+1)/2][(d+1)/2] := One(fld);
        v{[((d+1)/2)+2..d]}{[((d+1)/2)+1..d-1]} := IdentityMat(((d-1)/2)-1,fld);
    fi;

    u := IdentityMat( d, fld );;
    J := [[Zero(fld),One(fld)],[One(fld),Zero(fld)]];
    u{[1,2]}{[1,2]} := J;
    u{[d-1,d]}{[d-1,d]} := J;

    x := IdentityMat( d, fld );;
    if (IsEvenInt(d)) then
        x[1][2] := One(fld);
        x[d-1][d] := -One(fld);
    else
        x[(d+1)/2][1] := One(fld) * -1;
        x[d][1] := One(fld)* -2^(-1);
        x[d][(d+1)/2] := One(fld);
    fi;

    y := IdentityMat( d, fld );;
    if (IsEvenInt(d)) then
        y[1][1] := w;
        y[2][2] := w^(-1);
        y[d-1][d-1] := w^q;
        y[d][d] := w^(-q);
    else
        y[1][1] := w^(-q);
        y[d][d] := w;
        y[(d+1)/2][(d+1)/2] := w^(q-1);
    fi;

    return [s,t,delta,v,u,x,y];

end
);



#####
# LGOStandardGensSUEvenChar
#####

InstallGlobalFunction(  LGOStandardGensSUEvenChar,
function( d, q )

    local w, alpha, s, t, delta, u, v, x, y, J, fld, nu, Galois, phi, i;

    fld := GF(q^2);
    w := PrimitiveElement(fld);
    nu := Trace(GF(q^2),GF(q),w)^(-1) * w;

    s := IdentityMat( d, fld );
    s[1][1] := Zero(fld);
    s[d][d] := Zero(fld);
    s[1][d] := One(fld);
    s[d][1] := One(fld);

    t := IdentityMat( d, fld );
    t[1][d] := One(fld);

    delta := IdentityMat( d, fld );
    delta[1][1] := w^(q+1);
    delta[d][d] := w^((-(q+1)));

    v := 0 * IdentityMat( d, fld );
    if (IsEvenInt(d)) then
        v[d/2][1] := One(fld);
        v{[1..(d/2)-1]}{[2..d/2]} := IdentityMat((d/2)-1,fld);
        v[d/2+1][d] := One(fld);
        v{[(d/2)+2..d]}{[(d/2)+1..d-1]} := IdentityMat((d/2)-1,fld);
    else
        v[(d-1)/2][1] := One(fld);
        v{[1..((d-1)/2)-1]}{[2..(d-1)/2]} := IdentityMat(((d-1)/2)-1,fld);
        v[((d+1)/2)+1][d] := One(fld);
        v[(d+1)/2][(d+1)/2] := One(fld);
        v{[((d+1)/2)+2..d]}{[((d+1)/2)+1..d-1]} := IdentityMat(((d-1)/2)-1,fld);
    fi;

    u := IdentityMat( d, fld );;
    J := [[Zero(fld),One(fld)],[One(fld),Zero(fld)]];
    u{[1,2]}{[1,2]} := J;
    u{[d-1,d]}{[d-1,d]} := J;

    x := IdentityMat( d, fld );;
    if (IsEvenInt(d)) then
        x[1][2] := One(fld);
        x[d-1][d] := One(fld);
    else
        x[((d+1)/2)-1][(d+1)/2] := One(fld) ;
        x[((d+1)/2)-1][((d+1)/2)+1] := nu;
        x[(d+1)/2][((d+1)/2)+1] := One(fld);
    fi;

    y := IdentityMat( d, fld );;
    if (IsEvenInt(d)) then
        y[1][1] := w;
        y[2][2] := w^(-1);
        y[d-1][d-1] := w^q;
        y[d][d] := w^(-q);
    else
        y[((d+1)/2)+1][((d+1)/2)+1] := w^(-q);
        y[((d+1)/2)-1][((d+1)/2)-1] := w;
        y[(d+1)/2][(d+1)/2] := w^(q-1);
    fi;

    return [s,t,delta,v,u,x,y];

end
);



#####
#   BruhatDecompositionSU
#####

InstallGlobalFunction(  BruhatDecompositionSU,
function(stdgens, g)

    local slp, u1, pm, u2, p_sign, diag, res1, res2, res3, lastline, line, pgr, fld;
    
    fld := FieldOfMatrixList( [g] );

    if Size(fld) mod 2 = 0 then
        if (Length(g) mod 2) = 0 then

            # We write an SLP into the variable slp
            # The first 12 entries are the stdgens and their inverses
            # s, t, del, v, u, x, s^-1, t^-1, del^-1, v^-1, u^-1, x^-1

            Info( InfoBruhat, 1,
                    "returns an SLP to generate u1, u2, p_sign, diag\n"    );
                    
            fld := FieldOfMatrixList( [g] );

            # Compute the matrices u1,u2 of Bruhat-Decomposition and the instructions
            # for an SLP that compute u1 and u2
            res1 := UnitriangularDecompositionSUEvenAndEvenChar( stdgens, g);

            slp := res1[1];
            u1 := res1[2][2];
            pm := res1[2][1];    # the monomial matrix w
            u2 := res1[2][3];

            lastline := ShallowCopy( slp[ Length(slp) ] ); # remember famous last words
            # Since entries of the form [list1,list2] should only occur at the end
            Remove(slp);

            # Decompose w in to a signed Permutation-Matrix generated by <s,v,x>
            # and a Diagonal-Matrix diag.

            res2 := MonomialSLPSUEvenAndEvenChar(stdgens, pm, slp );

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
            res3 := DiagSLPSUEvenAndEvenChar(stdgens, diag, slp, res1[3]+10);
            slp := res3[1];

            # Here the last entry is of admissible form. Just add it to the end.
            Append( lastline, [ slp[ Length(slp)] ] ); # remember famous last words
            Remove( slp );
            Append( slp, [lastline] );

            Info( InfoBruhat, 2, "The Total Memory Usage is: "
                                , res1[3]+9+14, " memory slots\n" );

            pgr := MakeSLP(slp,7);

            # The result R of pgr satisfies:
            #    R[1]^-1*R[3]*R[4]*R[2]^-1    and
            #    R[1] = u1, R[2] = u2, R[3] = p_sign, R[4] = diag
            return [pgr, [ u1, u2, p_sign^(-1), diag ]];

        else

            # We write an SLP into the variable slp
            # The first 12 entries are the stdgens and their inverses
            # s, t, del, v, u, x, s^-1, t^-1, del^-1, v^-1, u^-1, x^-1

            Info( InfoBruhat, 1,
                    "returns an SLP to generate u1, u2, p_sign, diag\n"    );

            # Compute the matrices u1,u2 of Bruhat-Decomposition and the instructions
            # for an SLP that compute u1 and u2
            res1 := UnitriangularDecompositionSUOddAndEvenChar( stdgens, g);

            slp := res1[1];
            u1 := res1[2][2];
            pm := res1[2][1];    # the monomial matrix w
            u2 := res1[2][3];

            lastline := ShallowCopy( slp[ Length(slp) ] ); # remember famous last words
            # Since entries of the form [list1,list2] should only occur at the end
            Remove(slp);

            # Decompose w in to a signed Permutation-Matrix generated by <s,v,x>
            # and a Diagonal-Matrix diag.

            res2 := MonomialSLPSUOddAndEvenChar(stdgens, pm, slp );

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
            res3 := DiagSLPSUOddAndEvenChar(stdgens, diag, slp, res1[3]+10);
            slp := res3[1];

            # Here the last entry is of admissible form. Just add it to the end.
            Append( lastline, [ slp[ Length(slp)] ] ); # remember famous last words
            Remove( slp );
            Append( slp, [lastline] );

            Info( InfoBruhat, 2, "The Total Memory Usage is: "
                                , res1[3]+9+14, " memory slots\n" );

            pgr := MakeSLP(slp,7);

            # The result R of pgr satisfies:
            #    R[1]^-1*R[3]*R[4]*R[2]^-1    and
            #    R[1] = u1, R[2] = u2, R[3] = p_sign, R[4] = diag
            return [pgr, [ u1, u2, p_sign^(-1), diag ]];

        fi;
    fi;
    
    if (Length(g) mod 2) = 0 then

        # We write an SLP into the variable slp
        # The first 12 entries are the stdgens and their inverses
        # s, t, del, v, u, x, s^-1, t^-1, del^-1, v^-1, u^-1, x^-1

        Info( InfoBruhat, 1,
                "returns an SLP to generate u1, u2, p_sign, diag\n"    );

        # Compute the matrices u1,u2 of Bruhat-Decomposition and the instructions
        # for an SLP that compute u1 and u2
        res1 := UnitriangularDecompositionSUEven( stdgens, g);

        slp := res1[1];
        u1 := res1[2][2];
        pm := res1[2][1];    # the monomial matrix w
        u2 := res1[2][3];

        lastline := ShallowCopy( slp[ Length(slp) ] ); # remember famous last words
        # Since entries of the form [list1,list2] should only occur at the end
        Remove(slp);

        # Decompose w in to a signed Permutation-Matrix generated by <s,v,x>
        # and a Diagonal-Matrix diag.

        res2 := MonomialSLPSUEven(stdgens, pm, slp );

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
        res3 := DiagSLPSUEven(stdgens, diag, slp, res1[3]+10);
        slp := res3[1];

        # Here the last entry is of admissible form. Just add it to the end.
        Append( lastline, [ slp[ Length(slp)] ] ); # remember famous last words
        Remove( slp );
        Append( slp, [lastline] );

        Info( InfoBruhat, 2, "The Total Memory Usage is: "
                            , res1[3]+9+14, " memory slots\n" );

        pgr := MakeSLP(slp,7);

        # The result R of pgr satisfies:
        #    R[1]^-1*R[3]*R[4]*R[2]^-1    and
        #    R[1] = u1, R[2] = u2, R[3] = p_sign, R[4] = diag
        return [pgr, [ u1, u2, p_sign^(-1), diag ]];

    else

        # We write an SLP into the variable slp
        # The first 12 entries are the stdgens and their inverses
        # s, t, del, v, u, x, s^-1, t^-1, del^-1, v^-1, u^-1, x^-1

        Info( InfoBruhat, 1,
                "returns an SLP to generate u1, u2, p_sign, diag\n"    );

        # Compute the matrices u1,u2 of Bruhat-Decomposition and the instructions
        # for an SLP that compute u1 and u2
        res1 := UnitriangularDecompositionSUOdd( stdgens, g);

        slp := res1[1];
        u1 := res1[2][2];
        pm := res1[2][1];    # the monomial matrix w
        u2 := res1[2][3];

        lastline := ShallowCopy( slp[ Length(slp) ] ); # remember famous last words
        # Since entries of the form [list1,list2] should only occur at the end
        Remove(slp);

        # Decompose w in to a signed Permutation-Matrix generated by <s,v,x>
        # and a Diagonal-Matrix diag.

        res2 := MonomialSLPSUOdd(stdgens, pm, slp );

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
        res3 := DiagSLPSUOdd(stdgens, diag, slp, res1[3]+10);
        slp := res3[1];

        # Here the last entry is of admissible form. Just add it to the end.
        Append( lastline, [ slp[ Length(slp)] ] ); # remember famous last words
        Remove( slp );
        Append( slp, [lastline] );

        Info( InfoBruhat, 2, "The Total Memory Usage is: "
                            , res1[3]+9+14, " memory slots\n" );

        pgr := MakeSLP(slp,7);

        # The result R of pgr satisfies:
        #    R[1]^-1*R[3]*R[4]*R[2]^-1    and
        #    R[1] = u1, R[2] = u2, R[3] = p_sign, R[4] = diag
        return [pgr, [ u1, u2, p_sign^(-1), diag ]];

    fi;

end
);



#####
# MonomialSLPSUOdd
#####

InstallGlobalFunction(  MonomialSLPSUOdd,
function(arg)

    local slp, c, n, m, result, i, k, u1, u2, result2, test, g, stdgens, mat, perm, fld, p_signpos, vpos, vipos, spos, upos, unpos, tpos, left, right, cnt, v, vf, s, pot, p_signwr, instr, swr, vwr, viwr, p_sign, leftma, rightma, L, R, diag, w, alpha, tmpvalue, rowlist, L2, R2, tmpSave, perm2, perm3, q;

    # Check for correct Input
    if Length(arg) >= 2 and IsList(arg[1]) and IsMatrix(arg[2]) then

        stdgens := arg[1];  # the LGO standard generators
        mat := arg[2];        # the monomial matrix
        n := Length(stdgens[1]);
        m := (n+1)/2;

        # Compute the permutation in Sym(n) of mat
        perm := PermutationMonomialMatrix( mat );
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
        # The first 14 entries are the stdgens and the inverses
        # s, t, del, v, x, s^-1, t^-1, del^-1, v^-1, x^-1
        # The entries 11 (resAEM) and 12 (tmpAEM) are used to save AEM-values
        slp := [    [1, 1], [2, 1], [3, 1], [4, 1], [5, 1], [6, 1], [7, 1],
                    [1,-1], [2,-1], [3,-1], [4,-1], [5,-1], [6,-1], [7,-1],
                    [1, 0], [1, 0]    ];

        cnt := 16;

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
    L2 := IdentityMat(n,fld);
    R2 := IdentityMat(n,fld);
    w := PrimitiveElement(fld);
    q := RootInt(Size(fld));
    alpha := w^((q+1)/2);
    while (CheckContinue(perm,m)) do
        c := CycleFromPermutation(perm);
        for i in c do
            k := LargestMovedPoint(i);
            if k < m then
                Add(result, i);
            elif SmallestMovedPoint(i) > m then

            elif (n-k+1)^i = n-k+1 then
                tmpvalue := L2[k];
                L2[k] := alpha^(-1)*L2[n-k+1];
                L2[n-k+1] := alpha^(q)* tmpvalue;  #Was ist das Inverse?
                tmpvalue := R2{[1..n]}[k];
                R2{[1..n]}[k] := alpha*R2{[1..n]}[n-k+1];
                R2{[1..n]}[n-k+1] := alpha^(-q)*tmpvalue;
                perm := perm^(k,n-k+1);
                u1 := (k,n-k+1) * u1;
                Add( slp, [ [vpos,-(k-1),spos,1,vpos,k-1] , tpos ] );
                Add( slp, [ [tpos,-1,left,1] , left ] );
                Add( slp, [ [right,1,tpos,1] , right] );
                u2 := u2 * (k,n-k+1);
                break;
            else
                tmpvalue := L2[k];
                L2[k] := alpha^(-q)* L2[n-k+1];
                L2[n-k+1] := alpha*tmpvalue;
                perm := (k,n-k+1)*perm;
                u1 := (k,n-k+1) * u1;
                Add( slp, [ [vpos,-(k-1),spos,1,vpos,k-1] , tpos ] );
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

    Add( slp, [ [left,-1] , left ] );
    Add( slp, [ [right,-1] , right ] );

    result := Set(result);
    result2 := Set(result2);

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

    for i in [ 1 .. m-1 ] do

        pot := i^perm - i;

        # Need to update perm since pi_{i-1} may change pos of i
        perm   :=   perm   *  v ^pot;

        # memory slots 11 and 12 are used for resAEM and tmpAEM
        instr := AEM( vipos, 15, 16, pot );
        Append( slp, instr );
        Add( slp, [ [p_signpos,1, 15,1 ], p_signpos ] ); # permpos

        #Compute v_i+1, save command in slp
        v  :=    s    *  v;

        Add(slp,[ [spos,1, vipos,1 ], vipos ] ); # vipos
        # Don't be confused with notation in Paper
        # There we used v1 (which coincides with v^-1)

        s  :=   s ^(  vf ^-1 );
        Add(slp, [ [11, 1, spos,1, 4,1 ], spos ] ); # spos


    od;

    Add(slp,[ [ p_signpos,-1 ], p_signpos ] );

    tmpvalue := PermutationMat(perm2^(-1),n, fld);
    tmpvalue{[1..((n+1)/2)-1]}{[1..((n+1)/2)-1]} := PermutationMat(perm3^(-1),((n+1)/2)-1, fld);

    Add( slp, [ [left,1,p_signpos,1,right,1] , p_signpos ] );

    Add( slp, [ p_signpos ,1 ] );

    tmpvalue := R2*tmpvalue*L2;
    mat := tmpvalue*mat;

    return [slp, [tmpvalue , mat ] ];

end
);



#####
# MonomialSLPSUOddAndEvenChar
#####

InstallGlobalFunction(  MonomialSLPSUOddAndEvenChar,
function(arg)

    local slp, c, n, m, result, i, k, u1, u2, result2, test, g, stdgens, mat, perm, fld, p_signpos, vpos, vipos, spos, upos, unpos, tpos, left, right, cnt, v, vf, s, pot, p_signwr, instr, swr, vwr, viwr, p_sign, leftma, rightma, L, R, diag, w, alpha, tmpvalue, rowlist, L2, R2, tmpSave, perm2, perm3, q;

    # Check for correct Input
    if Length(arg) >= 2 and IsList(arg[1]) and IsMatrix(arg[2]) then

        stdgens := arg[1];  # the LGO standard generators
        mat := arg[2];        # the monomial matrix
        n := Length(stdgens[1]);
        m := (n+1)/2;

        # Compute the permutation in Sym(n) of mat
        perm := PermutationMonomialMatrix( mat );
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
        # The first 14 entries are the stdgens and the inverses
        # s, t, del, v, x, s^-1, t^-1, del^-1, v^-1, x^-1
        # The entries 11 (resAEM) and 12 (tmpAEM) are used to save AEM-values
        slp := [    [1, 1], [2, 1], [3, 1], [4, 1], [5, 1], [6, 1], [7, 1],
                    [1,-1], [2,-1], [3,-1], [4,-1], [5,-1], [6,-1], [7,-1],
                    [1, 0], [1, 0]    ];

        cnt := 16;

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
    L2 := IdentityMat(n,fld);
    R2 := IdentityMat(n,fld);
    w := PrimitiveElement(fld);
    q := RootInt(Size(fld));
    # alpha := w^((q+1)/2); # Not needed here
    while (CheckContinue(perm,m)) do
        c := CycleFromPermutation(perm);
        for i in c do
            k := LargestMovedPoint(i);
            if k < m then
                Add(result, i);
            elif SmallestMovedPoint(i) > m then

            elif (n-k+1)^i = n-k+1 then
                tmpvalue := L2[k];
                L2[k] := L2[n-k+1];
                L2[n-k+1] := tmpvalue;  #Was ist das Inverse?
                tmpvalue := R2{[1..n]}[k];
                R2{[1..n]}[k] := R2{[1..n]}[n-k+1];
                R2{[1..n]}[n-k+1] := tmpvalue;
                perm := perm^(k,n-k+1);
                u1 := (k,n-k+1) * u1;
                Add( slp, [ [vpos,-(k-1),spos,1,vpos,k-1] , tpos ] );
                Add( slp, [ [tpos,-1,left,1] , left ] );
                Add( slp, [ [right,1,tpos,1] , right] );
                u2 := u2 * (k,n-k+1);
                break;
            else
                tmpvalue := L2[k];
                L2[k] := L2[n-k+1];
                L2[n-k+1] := tmpvalue;
                perm := (k,n-k+1)*perm;
                u1 := (k,n-k+1) * u1;
                Add( slp, [ [vpos,-(k-1),spos,1,vpos,k-1] , tpos ] );
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

    Add( slp, [ [left,-1] , left ] );
    Add( slp, [ [right,-1] , right ] );

    result := Set(result);
    result2 := Set(result2);

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

    for i in [ 1 .. m-1 ] do

        pot := i^perm - i;

        # Need to update perm since pi_{i-1} may change pos of i
        perm   :=   perm   *  v ^pot;

        # memory slots 11 and 12 are used for resAEM and tmpAEM
        instr := AEM( vipos, 15, 16, pot );
        Append( slp, instr );
        Add( slp, [ [p_signpos,1, 15,1 ], p_signpos ] ); # permpos

        #Compute v_i+1, save command in slp
        v  :=    s    *  v;

        Add(slp,[ [spos,1, vipos,1 ], vipos ] ); # vipos
        # Don't be confused with notation in Paper
        # There we used v1 (which coincides with v^-1)

        s  :=   s ^(  vf ^-1 );
        Add(slp, [ [11, 1, spos,1, 4,1 ], spos ] ); # spos


    od;

    Add(slp,[ [ p_signpos,-1 ], p_signpos ] );

    tmpvalue := PermutationMat(perm2^(-1),n, fld);
    tmpvalue{[1..((n+1)/2)-1]}{[1..((n+1)/2)-1]} := PermutationMat(perm3^(-1),((n+1)/2)-1, fld);

    Add( slp, [ [left,1,p_signpos,1,right,1] , p_signpos ] );

    Add( slp, [ p_signpos ,1 ] );

    tmpvalue := R2*tmpvalue*L2;
    mat := tmpvalue*mat;

    return [slp, [tmpvalue , mat ] ];

end
);



#####
# MonomialSLPSUEven
#####

InstallGlobalFunction(  MonomialSLPSUEven,
function(arg)

    local slp, c, n, m, result, i, k, u1, u2, result2, test, g, stdgens, mat, perm, fld, p_signpos, vpos, vipos, spos, upos, unpos, tpos, left, right, cnt, v, vf, s, pot, p_signwr, instr, swr, vwr, viwr, p_sign, leftma, rightma, L, R, diag, w, alpha, tmpvalue, rowlist, L2, R2, tmpSave, perm2, perm3, q;

    # Check for correct Input
    if Length(arg) >= 2 and IsList(arg[1]) and IsMatrix(arg[2]) then

        stdgens := arg[1];  # the LGO standard generators
        mat := arg[2];        # the monomial matrix
        n := Length(stdgens[1]);
        m := n/2;

        # Compute the permutation in Sym(n) of mat
        perm := PermutationMonomialMatrix( mat );
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
        # The first 14 entries are the stdgens and the inverses
        # s, t, del, v, x, s^-1, t^-1, del^-1, v^-1, x^-1
        # The entries 11 (resAEM) and 12 (tmpAEM) are used to save AEM-values
        slp := [    [1, 1], [2, 1], [3, 1], [4, 1], [5, 1], [6, 1], [7, 1],
                    [1,-1], [2,-1], [3,-1], [4,-1], [5,-1], [6,-1], [7,-1],
                    [1, 0], [1, 0]    ];

        cnt := 16;

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
    q := RootInt(Size(fld));
    alpha := w^((q+1)/2);
    while (CheckContinue(perm,m)) do
        c := CycleFromPermutation(perm);
        for i in c do
            k := LargestMovedPoint(i);
            if k <= m then
                Add(result, i);
            elif SmallestMovedPoint(i) > m then

            elif (n-k+1)^i = n-k+1 then
                tmpvalue := L2[k];
                L2[k] := alpha^(-1)*L2[n-k+1];
                L2[n-k+1] := alpha^(q)* tmpvalue;  #Was ist das Inverse?
                tmpvalue := R2{[1..n]}[k];
                R2{[1..n]}[k] := alpha*R2{[1..n]}[n-k+1];
                R2{[1..n]}[n-k+1] := alpha^(-q)*tmpvalue;
                perm := perm^(k,n-k+1);
                u1 := (k,n-k+1) * u1;
                Add( slp, [ [vpos,-k,spos,1,vpos,k] , tpos ] );
                Add( slp, [ [tpos,-1,left,1] , left ] );
                Add( slp, [ [right,1,tpos,1] , right] );
                u2 := u2 * (k,n-k+1);
                break;
            else
                tmpvalue := L2[k];
                L2[k] := alpha^(-q)* L2[n-k+1];
                L2[n-k+1] := alpha*tmpvalue;
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

    Add( slp, [ [left,-1] , left ] );
    Add( slp, [ [right,-1] , right ] );

    #Display(mat);
    #Add(slp, [ [left,1,p_signpos,1,right,1] , p_signpos ] );
    #Add(slp, [[p_signpos,1],p_signpos]);
    #Add(slp, [[left,1],left]);
    #return slp;

    result := Set(result);
    result2 := Set(result2);

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

        # memory slots 11 and 12 are used for resAEM and tmpAEM
        instr := AEM( vipos, 15, 16, pot );
        Append( slp, instr );
        Add( slp, [ [p_signpos,1, 15,1 ], p_signpos ] ); # permpos

        #Compute v_i+1, save command in slp
        v  :=    s    *  v;

        Add(slp,[ [spos,1, vipos,1 ], vipos ] ); # vipos
        # Don't be confused with notation in Paper
        # There we used v1 (which coincides with v^-1)

        s  :=   s ^(  vf ^-1 );
        Add(slp, [ [11, 1, spos,1, 4,1 ], spos ] ); # spos


    od;

    Add(slp,[ [ p_signpos,-1 ], p_signpos ] );

    tmpvalue := PermutationMat(perm2^(-1),n, fld);
    tmpvalue{[1..n/2]}{[1..n/2]} := PermutationMat(perm3^(-1),n/2, fld);

    Add( slp, [ [left,1,p_signpos,1,right,1] , p_signpos ] );

    Add( slp, [ p_signpos ,1 ] );

    tmpvalue := R2*tmpvalue*L2;
    mat := tmpvalue*mat;

    return [slp, [tmpvalue , mat ] ];

end
);



#####
# MonomialSLPSUEvenAndEvenChar
#####

InstallGlobalFunction(  MonomialSLPSUEvenAndEvenChar,
function(arg)

    local slp, c, n, m, result, i, k, u1, u2, result2, test, g, stdgens, mat, perm, fld, p_signpos, vpos, vipos, spos, upos, unpos, tpos, left, right, cnt, v, vf, s, pot, p_signwr, instr, swr, vwr, viwr, p_sign, leftma, rightma, L, R, diag, w, alpha, tmpvalue, rowlist, L2, R2, tmpSave, perm2, perm3, q;

    # Check for correct Input
    if Length(arg) >= 2 and IsList(arg[1]) and IsMatrix(arg[2]) then

        stdgens := arg[1];  # the LGO standard generators
        mat := arg[2];        # the monomial matrix
        n := Length(stdgens[1]);
        m := n/2;

        # Compute the permutation in Sym(n) of mat
        perm := PermutationMonomialMatrix( mat );
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
        # The first 14 entries are the stdgens and the inverses
        # s, t, del, v, x, s^-1, t^-1, del^-1, v^-1, x^-1
        # The entries 11 (resAEM) and 12 (tmpAEM) are used to save AEM-values
        slp := [    [1, 1], [2, 1], [3, 1], [4, 1], [5, 1], [6, 1], [7, 1],
                    [1,-1], [2,-1], [3,-1], [4,-1], [5,-1], [6,-1], [7,-1],
                    [1, 0], [1, 0]    ];

        cnt := 16;

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
    q := RootInt(Size(fld));
    alpha := One(fld);
    while (CheckContinue(perm,m)) do
        c := CycleFromPermutation(perm);
        for i in c do
            k := LargestMovedPoint(i);
            if k <= m then
                Add(result, i);
            elif SmallestMovedPoint(i) > m then

            elif (n-k+1)^i = n-k+1 then
                tmpvalue := L2[k];
                L2[k] := alpha^(-1)*L2[n-k+1];
                L2[n-k+1] := alpha^(q)* tmpvalue;  #Was ist das Inverse?
                tmpvalue := R2{[1..n]}[k];
                R2{[1..n]}[k] := alpha*R2{[1..n]}[n-k+1];
                R2{[1..n]}[n-k+1] := alpha^(-q)*tmpvalue;
                perm := perm^(k,n-k+1);
                u1 := (k,n-k+1) * u1;
                Add( slp, [ [vpos,-k,spos,1,vpos,k] , tpos ] );
                Add( slp, [ [tpos,-1,left,1] , left ] );
                Add( slp, [ [right,1,tpos,1] , right] );
                u2 := u2 * (k,n-k+1);
                break;
            else
                tmpvalue := L2[k];
                L2[k] := alpha^(-q)* L2[n-k+1];
                L2[n-k+1] := alpha*tmpvalue;
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

    Add( slp, [ [left,-1] , left ] );
    Add( slp, [ [right,-1] , right ] );

    #Display(mat);
    #Add(slp, [ [left,1,p_signpos,1,right,1] , p_signpos ] );
    #Add(slp, [[p_signpos,1],p_signpos]);
    #Add(slp, [[left,1],left]);
    #return slp;

    result := Set(result);
    result2 := Set(result2);

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

        # memory slots 11 and 12 are used for resAEM and tmpAEM
        instr := AEM( vipos, 15, 16, pot );
        Append( slp, instr );
        Add( slp, [ [p_signpos,1, 15,1 ], p_signpos ] ); # permpos

        #Compute v_i+1, save command in slp
        v  :=    s    *  v;

        Add(slp,[ [spos,1, vipos,1 ], vipos ] ); # vipos
        # Don't be confused with notation in Paper
        # There we used v1 (which coincides with v^-1)

        s  :=   s ^(  vf ^-1 );
        Add(slp, [ [11, 1, spos,1, 4,1 ], spos ] ); # spos


    od;

    Add(slp,[ [ p_signpos,-1 ], p_signpos ] );

    tmpvalue := PermutationMat(perm2^(-1),n, fld);
    tmpvalue{[1..n/2]}{[1..n/2]} := PermutationMat(perm3^(-1),n/2, fld);

    Add( slp, [ [left,1,p_signpos,1,right,1] , p_signpos ] );

    Add( slp, [ p_signpos ,1 ] );

    tmpvalue := R2*tmpvalue*L2;
    mat := tmpvalue*mat;

    return [slp, [tmpvalue , mat ] ];

end
);



#####
# CheckContinue
#####

InstallGlobalFunction(  CheckContinue,
function(perm,m)

    local c, i;

    c := CycleFromPermutation(perm);
    for i in c do
        if not(LargestMovedPoint(i) <= m or SmallestMovedPoint(i) > m) then
            return true;
        fi;
    od;

    return false;

end
);



#####
# CycleFromPermutation
#####

InstallGlobalFunction(  CycleFromPermutation,
function(g)

    local result, n, pl, nc, point, i, h;

    h := LargestMovedPoint(g);
    n := [1..h];
    pl := ListPerm(g);
    result := [One(SymmetricGroup(h))];

    for i in n do
        if not(Size(Orbit(GroupByGenerators(result),i))>= 2) then
            nc := Orbit(GroupByGenerators([g]),[1..h],i);
            Add(result,CycleFromListMine(nc,h));
            n := Intersection(n,nc);
        fi;
    od;

    result := Filtered(result, x-> not(x = One(SymmetricGroup(h))));

    return result;

end
);



#####
# CycleFromListMine
#####

InstallGlobalFunction(  CycleFromListMine,
function(nc,h)

    local result, i;

    result := [1..h];
    for i in result do
        if i in nc then
            if not(i = nc[Size(nc)]) then
                result[i] := nc[Position(nc,i)+1];
            else
                result[i] := nc[1];
            fi;
        fi;
    od;

    return PermListList([1..h],result);

end
);



#####
# DiagSLPSUOdd
#####

InstallGlobalFunction(  DiagSLPSUOdd,
function(arg)

    local stdgens, diag, fld, slp, a_i, d, omega, y, v, cnt, hiposm, hipos, respos, hres, instr, i, q;

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
    q := Characteristic(fld);

    if Length(arg) >= 3 and Length(arg) <= 4 then

        # The first 14 entries are the stdgens and their inverses
        slp := arg[3];

        if not IsList(slp) then
            Error("Input: third argument must be a list");
            return fail;
        fi;

        # cnt := HighestSlotOfSLP( slp );     <--- Laesst sich das umgehen? Jeweils den hoechsten Slot mitzaehlen?
        cnt := arg[4];
        Info( InfoBruhat, 2, " and additional:  ",3," memory slots ",
                            "in DiagonalDecomposition()\n");

    else
        # We write an SLP into the variable slp
        # The first 14 entries are the stdgens and their inverses
        # s^-1 t^-1  del^-1    v^-1    x^-1
        # The entries #15 (resAEM),#16 (tmpAEM) are used to save AEM-values
        slp := [     [1, 1], [2, 1], [3, 1], [4, 1], [5, 1], [6, 1], [7,1],
                    [1,-1], [2,-1], [3,-1], [4,-1], [5,-1], [6,-1], [7,-1],
                    [1, 0], [1, 0] ];

        cnt := 16;
        Info( InfoBruhat, 2, "Memory Usage is: ",3," memory slots ",
                            "in DiagonalDecomposition()\n");
    fi;

    # Define the LGO standard-generators given in the input
    y        := stdgens[7];
    v        := stdgens[4];

    # Initialize the additional memory quota
    #hi-2
    Add(slp, [ [1,0], cnt + 1 ] );    hipos := cnt + 1;     #17 or 28+3f
    # result
    Add(slp, [ [1,0], cnt + 2 ] );    respos := cnt + 2;     #18 or 29+3f

    d := Length( diag );
    omega := y[1][1];

    if diag = One(diag) then
        Add( slp, [ [1,0], respos ] );
        Add( slp, [ respos, 1]);
        return [slp];
    fi;

    hres := diag^0;
    Add( slp, [ [7,1], hipos ] );

    for i in [ 1..((d-1)/2) ] do

        a_i := LogFFE( diag[i][i], omega );

        # The memory slots 15 and 16 are res and tmp-slot for AEM
        instr := AEM( hipos, 15, 16, a_i );
        Append( slp, instr );
        Add( slp, [ [respos, 1, 15, 1 ], respos ] );
        Add( slp, [ [4, -1 , hipos, 1, 4,1 ], hipos ] );

    od;

    Add( slp, [ respos ,1 ] );

    return [slp];

end
);



#####
# DiagSLPSUOddAndEvenChar
#####

InstallGlobalFunction(  DiagSLPSUOddAndEvenChar,
function(arg)

    local stdgens, diag, fld, slp, a_i, d, omega, y, v, cnt, hiposm, hipos, respos, hres, instr, i, q;

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
    q := Characteristic(fld);

    if Length(arg) >= 3 and Length(arg) <= 4 then

        # The first 14 entries are the stdgens and their inverses
        slp := arg[3];

        if not IsList(slp) then
            Error("Input: third argument must be a list");
            return fail;
        fi;

        # cnt := HighestSlotOfSLP( slp );     <--- Laesst sich das umgehen? Jeweils den hoechsten Slot mitzaehlen?
        cnt := arg[4];
        Info( InfoBruhat, 2, " and additional:  ",3," memory slots ",
                            "in DiagonalDecomposition()\n");

    else
        # We write an SLP into the variable slp
        # The first 14 entries are the stdgens and their inverses
        # s^-1 t^-1  del^-1    v^-1    x^-1
        # The entries #15 (resAEM),#16 (tmpAEM) are used to save AEM-values
        slp := [     [1, 1], [2, 1], [3, 1], [4, 1], [5, 1], [6, 1], [7,1],
                    [1,-1], [2,-1], [3,-1], [4,-1], [5,-1], [6,-1], [7,-1],
                    [1, 0], [1, 0] ];

        cnt := 16;
        Info( InfoBruhat, 2, "Memory Usage is: ",3," memory slots ",
                            "in DiagonalDecomposition()\n");
    fi;

    # Define the LGO standard-generators given in the input
    y        := stdgens[7];
    v        := stdgens[4];

    # Initialize the additional memory quota
    #hi-2
    Add(slp, [ [1,0], cnt + 1 ] );    hipos := cnt + 1;     #17 or 28+3f
    # result
    Add(slp, [ [1,0], cnt + 2 ] );    respos := cnt + 2;     #18 or 29+3f

    d := Length( diag );
    omega := y[((d+1)/2)-1][((d+1)/2)-1];  #Angepasst, hier muss omega entsprechend y gewaehlt werden.

    if diag = One(diag) then
        Add( slp, [ [1,0], respos ] );
        Add( slp, [ respos, 1]);
        return [slp];
    fi;

    hres := diag^0;
    Add( slp, [ [7,1], hipos ] );

    for i in [ 1..((d-1)/2) ] do

        a_i := LogFFE( diag[d-i+1][d-i+1], omega );

        # The memory slots 15 and 16 are res and tmp-slot for AEM
        instr := AEM( hipos, 15, 16, a_i );
        Append( slp, instr );
        Add( slp, [ [respos, 1, 15, 1 ], respos ] );
        Add( slp, [ [4, -1 , hipos, 1, 4,1 ], hipos ] );

    od;

    Add( slp, [ respos ,1 ] );

    return [slp];

end
);



#####
# DiagSLPSU
#####

InstallGlobalFunction(  DiagSLPSU,
function(arg)

    local diag, n;

     diag := arg[2];
     n := Length(diag);

    if (n mod 2) = 0 then
        return DiagSLPSUEven(arg);
    else
        return DiagSLPSUOdd(arg);
    fi;

end
);



#####
# DiagSLPSUEven
#####

InstallGlobalFunction(  DiagSLPSUEven,
function(arg)

    local stdgens, diag, fld, slp, a_i, d, omega, y, v, cnt, hiposm, hipos, respos, hres, instr, i, q, alpha, lambdai;

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
    q := RootInt(Size(fld));

    if Length(arg) >= 3 and Length(arg) <= 4 then

        # The first 14 entries are the stdgens and their inverses
        slp := arg[3];

        if not IsList(slp) then
            Error("Input: third argument must be a list");
            return fail;
        fi;

        # cnt := HighestSlotOfSLP( slp );     <--- Laesst sich das umgehen? Jeweils den hoechsten Slot mitzaehlen?
        cnt := arg[4];
        Info( InfoBruhat, 2, " and additional:  ",3," memory slots ",
                            "in DiagonalDecomposition()\n");

    else
        # We write an SLP into the variable slp
        # The first 10 entries are the stdgens and their inverses
        # s^-1 t^-1  del^-1    v^-1    x^-1
        # The entries #15 (resAEM),#16 (tmpAEM) are used to save AEM-values
        slp := [     [1, 1], [2, 1], [3, 1], [4, 1], [5, 1], [6, 1], [7,1],
                    [1,-1], [2,-1], [3,-1], [4,-1], [5,-1], [6,-1], [7,-1],
                    [1, 0], [1, 0] ];

        cnt := 16;
        Info( InfoBruhat, 2, "Memory Usage is: ",3," memory slots ",
                            "in DiagonalDecomposition()\n");
    fi;

    # Define the LGO standard-generators given in the input
    y        := stdgens[7];
    v        := stdgens[4];

    # Initialize the additional memory quota
    #hi-2
    Add(slp, [ [1,0], cnt + 1 ] );    hipos := cnt + 1;     #17 or 28+3f
    # result
    Add(slp, [ [1,0], cnt + 2 ] );    respos := cnt + 2;     #18 or 29+3f

    d := Length( diag );
    omega := y[1][1];

    if diag = One(diag) then
        Add( slp, [ [1,0], respos ] );
        Add( slp, [ respos, 1]);
        return [slp];
    fi;

    hres := diag^0;
    lambdai := 0;
    Add( slp, [ [7,1], hipos ] );

    for i in [ 1..(d/2)-1 ] do

        lambdai := lambdai + LogFFE( diag[i][i], omega );

        # The memory slots 15 and 16 are res and tmp-slot for AEM
        instr := AEM( hipos, 15, 16, lambdai );
        Append( slp, instr );
        Add( slp, [ [respos, 1, 15, 1 ], respos ] );
        Add( slp, [ [4, -1 , hipos, 1, 4,1 ], hipos ] );

    od;

    alpha := omega^(q+1);
    lambdai := LogFFE( diag[d/2][d/2] * omega^(lambdai), alpha );

    Add( slp, [ [4, -((d/2)-1) , 3, 1, 4, (d/2)-1], hipos ] );
    instr := AEM( hipos, 15, 16, lambdai );
    Append( slp, instr );
    Add( slp, [ [respos, 1, 15, 1 ], respos ] );

    Add( slp, [ respos ,1 ] );

    return [slp];

end
);



#####
# DiagSLPSUEvenAndEvenChar
#####

InstallGlobalFunction(  DiagSLPSUEvenAndEvenChar,
function(arg)

    local stdgens, diag, fld, slp, a_i, d, omega, y, v, cnt, hiposm, hipos, respos, hres, instr, i, q, alpha, lambdai;

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
    q := RootInt(Size(fld));

    if Length(arg) >= 3 and Length(arg) <= 4 then

        # The first 14 entries are the stdgens and their inverses
        slp := arg[3];

        if not IsList(slp) then
            Error("Input: third argument must be a list");
            return fail;
        fi;

        # cnt := HighestSlotOfSLP( slp );     <--- Laesst sich das umgehen? Jeweils den hoechsten Slot mitzaehlen?
        cnt := arg[4];
        Info( InfoBruhat, 2, " and additional:  ",3," memory slots ",
                            "in DiagonalDecomposition()\n");

    else
        # We write an SLP into the variable slp
        # The first 10 entries are the stdgens and their inverses
        # s^-1 t^-1  del^-1    v^-1    x^-1
        # The entries #15 (resAEM),#16 (tmpAEM) are used to save AEM-values
        slp := [     [1, 1], [2, 1], [3, 1], [4, 1], [5, 1], [6, 1], [7,1],
                    [1,-1], [2,-1], [3,-1], [4,-1], [5,-1], [6,-1], [7,-1],
                    [1, 0], [1, 0] ];

        cnt := 16;
        Info( InfoBruhat, 2, "Memory Usage is: ",3," memory slots ",
                            "in DiagonalDecomposition()\n");
    fi;

    # Define the LGO standard-generators given in the input
    y        := stdgens[7];
    v        := stdgens[4];

    # Initialize the additional memory quota
    #hi-2
    Add(slp, [ [1,0], cnt + 1 ] );    hipos := cnt + 1;     #17 or 28+3f
    # result
    Add(slp, [ [1,0], cnt + 2 ] );    respos := cnt + 2;     #18 or 29+3f

    d := Length( diag );
    omega := y[1][1];

    if diag = One(diag) then
        Add( slp, [ [1,0], respos ] );
        Add( slp, [ respos, 1]);
        return [slp];
    fi;

    hres := diag^0;
    lambdai := 0;
    Add( slp, [ [7,1], hipos ] );

    for i in [ 1..(d/2)-1 ] do

        lambdai := lambdai + LogFFE( diag[i][i], omega );

        # The memory slots 15 and 16 are res and tmp-slot for AEM
        instr := AEM( hipos, 15, 16, lambdai );
        Append( slp, instr );
        Add( slp, [ [respos, 1, 15, 1 ], respos ] );
        Add( slp, [ [4, -1 , hipos, 1, 4,1 ], hipos ] );

    od;

    alpha := omega^(q+1);
    lambdai := LogFFE( diag[d/2][d/2] * omega^(lambdai), alpha );

    Add( slp, [ [4, -((d/2)-1) , 3, 1, 4, (d/2)-1], hipos ] );
    instr := AEM( hipos, 15, 16, lambdai );
    Append( slp, instr );
    Add( slp, [ [respos, 1, 15, 1 ], respos ] );

    Add( slp, [ respos ,1 ] );

    return [slp];

end
);
