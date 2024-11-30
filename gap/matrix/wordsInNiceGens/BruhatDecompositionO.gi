######################################
# BruhatDecompositionO.gi
######################################

####################
# PART I - a)
#    Originally implemented subfunctions
####################

InfoBruhat := NewInfoClass("InfoBruhat");;
SetInfoLevel( InfoBruhat, 2 );

#####
# FindPrimePowerDecomposition()
#####

InstallGlobalFunction(  FindPrimePowerDecomposition,
function(n)
    local res, a, b;

    res := n-1;
    a := 0;
    while res mod 2 = 0 do
        a := a + 1;
        res := Int(res*0.5);
    od;
    b := (n-1)/(2^a);
    
    return [a,b];

end
);



#####
# LGOStandardGensSO()
#####

InstallGlobalFunction(  LGOStandardGensSO,
function(e, d, q)

    if e = 1 then
        if d < 6 then
            Error("LGOStandardGens: d has to be at least 6\n");
            return;
        fi;
        return __LGOStandardGensSOPlus(d,q);
    fi;
    
    if e = -1 then
        if d < 6 then
            Error("LGOStandardGens: d has to be at least 8\n");
            return;
        fi;
        return __LGOStandardGensSOMinus(d,q);
    fi;
    
    if e = 0 then
        if d < 6 then
            Error("LGOStandardGens: d has to be at least 7\n");
            return;
        fi;
        return __LGOStandardGensSOCircle(d,q);
    fi;
    
    Error("e has to be 1, -1 or 0.");

end
);



#####
# __LGOStandardGensSOPlus()
#####

InstallGlobalFunction(  __LGOStandardGensSOPlus,
function(d,q)
    local s, sBar, t, tBar, delta, deltaBar, u, v, sigma, fld, w, n, S1, S2, a, b, res;
    
    fld := GF(q);
    w := PrimitiveElement(fld);

    s := IdentityMat( d, fld );
    s[1][1] := Zero(fld);
    s[2][2] := Zero(fld);
    s[d-1][d-1] := Zero(fld);
    s[d][d] := Zero(fld);
    s[1][d-1] := -1 * One(fld);
    s[d][2] := -1 * One(fld);
    s[2][d] := One(fld);
    s[d-1][1] := One(fld);
    
    sBar := IdentityMat( d, fld );
    sBar[1][1] := Zero(fld);
    sBar[2][2] := Zero(fld);
    sBar[d-1][d-1] := Zero(fld);
    sBar[d][d] := Zero(fld);
    sBar[1][2] := One(fld);
    sBar[d][d-1] := One(fld);
    sBar[2][1] := -1 * One(fld);
    sBar[d-1][d] := -1 * One(fld);

    t := IdentityMat( d, fld );
    t[1][d-1] := -1 * One(fld);
    t[2][d] := One(fld);
    
    tBar := IdentityMat( d, fld );
    tBar[1][2] := One(fld);
    tBar[d-1][d] := -1 * One(fld);

    delta := IdentityMat( d, fld );
    delta[1][1] := w;
    delta[d][d] := w^(-1);
    delta[2][2] := w;
    delta[d-1][d-1] := w^(-1);

    deltaBar := IdentityMat( d, fld );
    deltaBar[1][1] := w;
    deltaBar[d][d] := w^(-1);
    deltaBar[2][2] := w^(-1);
    deltaBar[d-1][d-1] := w;
    
    u := IdentityMat( d, fld );
    
    n := Int(d* 0.5);
    
    v := 0 * IdentityMat( d, fld );
    v[d/2][1] := One(fld);
    v{[1..(d/2)-1]}{[2..d/2]} := IdentityMat((d/2)-1, fld);
    v[d/2+1][d] := One(fld);
    v{[(d/2)+2..d]}{[(d/2)+1..d-1]} := IdentityMat((d/2)-1, fld);
    if n mod 2 = 0 then
        v[d/2][1] := -1 * One(fld);
        v[d/2+1][d] := -1 * One(fld);
    fi;
    
    res := q-1;
    a := 0;
    while res mod 2 = 0 do
        a := a + 1;
        res := Int(res*0.5);
    od;
    b := (q-1)/(2^a);
    sigma := IdentityMat( d, fld );
    sigma[1][1] := w^b;
    sigma[d][d] := w^(-b);

    return [s, sBar, t, tBar, delta, deltaBar, u, v, sigma];

end
);



#####
# __LGOStandardGensSOCircle()
#####

InstallGlobalFunction(  __LGOStandardGensSOCircle,
function(d,q)
    local s, t, delta, u, v, sigma, fld, w, n, S1, a, b, res;
    
    fld := GF(q);
    w := PrimitiveElement(fld);
    n := Int((d-1)*1/2);

    s := IdentityMat( d, fld );
    s[1][1] := Zero(fld);
    s[d][d] := Zero(fld);
    s[(d+1)/2][(d+1)/2] := -1 * One(fld);
    s[1][d] := One(fld);
    s[d][1] := One(fld);

    t := IdentityMat( d, fld );
    t[1][d] := One(fld);
    t[1][(d+1)/2] := 2 * One(fld);
    t[(d+1)/2][d] := One(fld);
    
    delta := IdentityMat( d, fld );
    delta[1][1] := w^2;
    delta[d][d] := w^(-2);
    delta[3][3] := One(fld);
    
    u := IdentityMat( d, fld );
    u{[1..2]}{[1..2]} := [[0,1],[-1,0]];
    u{[d-1,d]}{[d-1,d]} := [[0,-1],[1,0]];
    u := u * One(fld);
    
    v := 0 * IdentityMat( d, fld );
    v[(d+1)/2][(d+1)/2] := One(fld);
    v[(d+1)/2 - 1][1] := One(fld);
    v{[1..((d+1)/2)-2]}{[2..((d+1)/2)-1]} := IdentityMat(((d+1)/2)-2, fld);
    v[(d+1)/2 + 1][d] := One(fld);
    v{[((d+1)/2)+2..d]}{[((d+1)/2)+1..d-1]} := IdentityMat(((d+1)/2)-2, fld);
    if n mod 2 = 0 then
        v[(d+1)/2 - 1][1] := -1 * One(fld);
        v[(d+1)/2 + 1][d] := -1 * One(fld);
    fi;
    
    res := q-1;
    a := 0;
    while res mod 2 = 0 do
        a := a + 1;
        res := Int(res*0.5);
    od;
    b := (q-1)/(2^a);
    sigma := IdentityMat( d, fld );
    sigma[1][1] := w^b;
    sigma[d][d] := w^(-b);
    sigma[3][3] := One(fld);

    return [s, t, delta, u, v, sigma];

end
);



#####
# __LGOStandardGensSOMinus()
#####

InstallGlobalFunction(  __LGOStandardGensSOMinus,
function(d,q)
    local s, t, delta, u, v, sigma, fld, w, n, S1, lambda, A, B, C, gamma, alpha,perm, inv, gamma2;
    
    fld := GF(q);
    gamma := PrimitiveElement(GF(q^2));
    gamma2 := PrimitiveElement(GF(q));
    alpha := gamma^((q+1)/2);
    w := alpha^2;

    s := IdentityMat( d, fld );
    s[1][1] := Zero(fld);
    s[d][d] := Zero(fld);
    s[1][d] := One(fld);
    s[d][1] := One(fld);
    s[d/2][d/2] := -1 * One(fld);

    t := IdentityMat( d, fld );
    t[1][d] := One(fld);
    t[1][(d/2) + 1] := One(fld);
    t[(d/2) + 1][d] := 2 * One(fld);
    
    A := 1/2 * ((gamma^(q-1))+(gamma^(-q+1)));
    if A <> Zero(fld) then
        A := gamma2^LogFFE(A,gamma2);
    else
        A := Zero(fld);
    fi;
    B := 1/2 * alpha * ((gamma^(q-1)) - (gamma^(-q+1)));
    if B <> Zero(fld) then
        B := gamma2^LogFFE(B,gamma2);
    else
        B := Zero(fld);
    fi;
    C := 1/2 * alpha^(-1) * ((gamma^(q-1)) - (gamma^(-q+1)));
    if C <> Zero(fld) then
        C := gamma2^LogFFE(C,gamma2);
    else
        C := Zero(fld);
    fi;
    w := gamma2^LogFFE(w,gamma2);
    delta := IdentityMat( d, fld );
    delta[1][1] := w;
    delta[d][d] := w^(-1);
    delta[(d/2)][(d/2)] := A;
    delta[(d/2)+1][(d/2)+1] := A;
    delta[(d/2)][(d/2)+1] := B;
    delta[(d/2)+1][(d/2)] := C;
    
    u := IdentityMat( d, fld );
    u{[1..2]}{[1..2]} := [[0,1],[-1,0]];
    u{[d-1,d]}{[d-1,d]} := [[0,-1],[1,0]];
    u := u * One(fld);
    
    n := Int(d * 0.5)-1;
    v := 0 * IdentityMat( d, fld );
    v[(d/2)][(d/2)] := One(fld);
    v[(d/2)+1][(d/2)+1] := One(fld);
    v[(d/2) - 1][1] := One(fld);
    v{[1..(d/2)-2]}{[2..((d/2)-1)]} := IdentityMat((d/2)-2, fld);
    v[(d/2) + 2][d] := One(fld);
    v{[(d/2)+3..d]}{[(d/2)+2..d-1]} := IdentityMat((d/2)-2, fld);
    if n mod 2 = 0 then
        v[(d/2) - 1][1] := -1 * One(fld);
        v[(d/2) + 2][d] := -1 * One(fld);
    fi;
    
    sigma := IdentityMat( d, fld );
    n := Int(d * 0.5);
    lambda := (-1)^((q-1)/2);
    sigma[1][1] := lambda * One(fld);
    sigma[d][d] := lambda * One(fld);
    sigma[d/2][d/2] := -lambda * One(fld);
    sigma[(d/2)+1][(d/2)+1] := -lambda * One(fld);

    return [s, t, delta, u, v, sigma];

end
);



#####
# LGOStandardGensOmega()
#####

InstallGlobalFunction(  LGOStandardGensOmega,
function(e, d, q)

    if (q mod 2 = 0) then
        if e = 1 then
            return __LGOStandardGensOmegaPlusEvenChar(d,q);
        fi;
        
        if e = -1 then
            return __LGOStandardGensOmegaMinusEvenChar(d,q);
        fi;
        
        if e = 0 then
            return __LGOStandardGensOmegaCircleEvenChar(d,q);
        fi;
    else
        if e = 1 then
            return __LGOStandardGensOmegaPlus(d,q);
        fi;
        
        if e = -1 then
            return __LGOStandardGensOmegaMinus(d,q);
        fi;
        
        if e = 0 then
            return __LGOStandardGensOmegaCircle(d,q);
        fi;
    fi;
    
    Error("e has to be 1, -1 or 0.");

end
);



#####
# __LGOStandardGensOmegaPlus()
#####

InstallGlobalFunction(  __LGOStandardGensOmegaPlus,
function(d,q)
    local s, sBar, t, tBar, delta, deltaBar, u, v, sigma, fld, w, n, S1, S2, a, b, res;
    
    fld := GF(q);
    w := PrimitiveElement(fld);

    s := IdentityMat( d, fld );
    s[1][1] := Zero(fld);
    s[2][2] := Zero(fld);
    s[d-1][d-1] := Zero(fld);
    s[d][d] := Zero(fld);
    s[1][d-1] := -1 * One(fld);
    s[d][2] := -1 * One(fld);
    s[2][d] := One(fld);
    s[d-1][1] := One(fld);
    
    sBar := IdentityMat( d, fld );
    sBar[1][1] := Zero(fld);
    sBar[2][2] := Zero(fld);
    sBar[d-1][d-1] := Zero(fld);
    sBar[d][d] := Zero(fld);
    sBar[1][2] := One(fld);
    sBar[d][d-1] := One(fld);
    sBar[2][1] := -1 * One(fld);
    sBar[d-1][d] := -1 * One(fld);

    t := IdentityMat( d, fld );
    t[1][d-1] := -1 * One(fld);
    t[2][d] := One(fld);
    
    tBar := IdentityMat( d, fld );
    tBar[1][2] := One(fld);
    tBar[d-1][d] := -1 * One(fld);

    delta := IdentityMat( d, fld );
    delta[1][1] := w;
    delta[d][d] := w^(-1);
    delta[2][2] := w;
    delta[d-1][d-1] := w^(-1);

    deltaBar := IdentityMat( d, fld );
    deltaBar[1][1] := w;
    deltaBar[d][d] := w^(-1);
    deltaBar[2][2] := w^(-1);
    deltaBar[d-1][d-1] := w;
    
    u := IdentityMat( d, fld );
    
    n := Int(d* 0.5);
    
    v := 0 * IdentityMat( d, fld );
    v[d/2][1] := One(fld);
    v{[1..(d/2)-1]}{[2..d/2]} := IdentityMat((d/2)-1, fld);
    v[d/2+1][d] := One(fld);
    v{[(d/2)+2..d]}{[(d/2)+1..d-1]} := IdentityMat((d/2)-1, fld);
    if n mod 2 = 0 then
        v[d/2][1] := -1 * One(fld);
        v[d/2+1][d] := -1 * One(fld);
    fi;

    return [s, sBar, t, tBar, delta, deltaBar, u, v];

end
);



#####
# __LGOStandardGensOmegaCircle()
#####

InstallGlobalFunction(  __LGOStandardGensOmegaCircle,
function(d,q)
    local s, t, delta, u, v, sigma, fld, w, n, S1, a, b, res;
    
    fld := GF(q);
    w := PrimitiveElement(fld);
    n := Int((d-1)*1/2);

    s := IdentityMat( d, fld );
    s[1][1] := Zero(fld);
    s[d][d] := Zero(fld);
    s[(d+1)/2][(d+1)/2] := -1 * One(fld);
    s[1][d] := One(fld);
    s[d][1] := One(fld);

    t := IdentityMat( d, fld );
    t[1][d] := One(fld);
    t[1][(d+1)/2] := 2 * One(fld);
    t[(d+1)/2][d] := One(fld);
    
    delta := IdentityMat( d, fld );
    delta[1][1] := w^2;
    delta[d][d] := w^(-2);
    delta[3][3] := One(fld);
    
    u := IdentityMat( d, fld );
    u{[1..2]}{[1..2]} := [[0,1],[-1,0]];
    u{[d-1,d]}{[d-1,d]} := [[0,-1],[1,0]];
    u := u * One(fld);
    
    v := 0 * IdentityMat( d, fld );
    v[(d+1)/2][(d+1)/2] := One(fld);
    v[(d+1)/2 - 1][1] := One(fld);
    v{[1..((d+1)/2)-2]}{[2..((d+1)/2)-1]} := IdentityMat(((d+1)/2)-2, fld);
    v[(d+1)/2 + 1][d] := One(fld);
    v{[((d+1)/2)+2..d]}{[((d+1)/2)+1..d-1]} := IdentityMat(((d+1)/2)-2, fld);
    if n mod 2 = 0 then
        v[(d+1)/2 - 1][1] := -1 * One(fld);
        v[(d+1)/2 + 1][d] := -1 * One(fld);
    fi;

    return [s, t, delta, u, v];

end
);



#####
# __LGOStandardGensOmegaMinus()
#####

InstallGlobalFunction(  __LGOStandardGensOmegaMinus,
function(d,q)
    local s, t, delta, u, v, sigma, fld, w, n, S1, lambda, A, B, C, gamma, alpha,perm, inv, gamma2;
    
    fld := GF(q);
    gamma := PrimitiveElement(GF(q^2));
    gamma2 := PrimitiveElement(GF(q));
    alpha := gamma^((q+1)/2);
    w := alpha^2;

    s := IdentityMat( d, fld );
    s[1][1] := Zero(fld);
    s[d][d] := Zero(fld);
    s[1][d] := One(fld);
    s[d][1] := One(fld);
    s[d/2][d/2] := -1 * One(fld);

    t := IdentityMat( d, fld );
    t[1][d] := One(fld);
    t[1][(d/2) + 1] := One(fld);
    t[(d/2) + 1][d] := 2 * One(fld);
    
    A := 1/2 * ((gamma^(q-1))+(gamma^(-q+1)));
    if A <> Zero(fld) then
        A := gamma2^LogFFE(A,gamma2);
    else
        A := Zero(fld);
    fi;
    B := 1/2 * alpha * ((gamma^(q-1)) - (gamma^(-q+1)));
    if B <> Zero(fld) then
        B := gamma2^LogFFE(B,gamma2);
    else
        B := Zero(fld);
    fi;
    C := 1/2 * alpha^(-1) * ((gamma^(q-1)) - (gamma^(-q+1)));
    if C <> Zero(fld) then
        C := gamma2^LogFFE(C,gamma2);
    else
        C := Zero(fld);
    fi;
    w := gamma2^LogFFE(w,gamma2);
    delta := IdentityMat( d, fld );
    delta[1][1] := w;
    delta[d][d] := w^(-1);
    delta[(d/2)][(d/2)] := A;
    delta[(d/2)+1][(d/2)+1] := A;
    delta[(d/2)][(d/2)+1] := B;
    delta[(d/2)+1][(d/2)] := C;
    
    u := IdentityMat( d, fld );
    u{[1..2]}{[1..2]} := [[0,1],[-1,0]];
    u{[d-1,d]}{[d-1,d]} := [[0,-1],[1,0]];
    u := u * One(fld);
    
    n := Int(d * 0.5)-1;
    v := 0 * IdentityMat( d, fld );
    v[(d/2)][(d/2)] := One(fld);
    v[(d/2)+1][(d/2)+1] := One(fld);
    v[(d/2) - 1][1] := One(fld);
    v{[1..(d/2)-2]}{[2..((d/2)-1)]} := IdentityMat((d/2)-2, fld);
    v[(d/2) + 2][d] := One(fld);
    v{[(d/2)+3..d]}{[(d/2)+2..d-1]} := IdentityMat((d/2)-2, fld);
    if n mod 2 = 0 then
        v[(d/2) - 1][1] := -1 * One(fld);
        v[(d/2) + 2][d] := -1 * One(fld);
    fi;

    return [s, t, delta, u, v];

end
);



#####
# __LGOStandardGensOmegaPlusEvenChar()
#####

InstallGlobalFunction(  __LGOStandardGensOmegaPlusEvenChar,
function(d,q)
    local s, t, tBar, delta, deltaBar, u, v, sigma, fld, w, n, S1, S2, a, b, res, J;
    
    fld := GF(q);
    w := PrimitiveElement(fld);

    s := IdentityMat( d, fld );
    s[1][1] := Zero(fld);
    s[2][2] := Zero(fld);
    s[d-1][d-1] := Zero(fld);
    s[d][d] := Zero(fld);
    s[1][d-1] := One(fld);
    s[d][2] := One(fld);
    s[2][d] := One(fld);
    s[d-1][1] := One(fld);

    t := IdentityMat( d, fld );
    t[1][d-1] := One(fld);
    t[2][d] := One(fld);
    
    tBar := IdentityMat( d, fld );
    tBar[1][2] := One(fld);
    tBar[d-1][d] := One(fld);

    delta := IdentityMat( d, fld );
    delta[1][1] := w;
    delta[d][d] := w^(-1);
    delta[2][2] := w;
    delta[d-1][d-1] := w^(-1);
    
    deltaBar := IdentityMat( d, fld );
    deltaBar[1][1] := w;
    deltaBar[d][d] := w^(-1);
    deltaBar[2][2] := w^(-1);
    deltaBar[d-1][d-1] := w;
    
    u := IdentityMat( d, fld );
    J := [[Zero(fld),One(fld)],[One(fld),Zero(fld)]];
    u{[1,2]}{[1,2]} := J;
    u{[d-1,d]}{[d-1,d]} := J;
    
    n := Int(d* 0.5);
    
    v := 0 * IdentityMat( d, fld );
    v[d/2][1] := One(fld);
    v{[1..(d/2)-1]}{[2..d/2]} := IdentityMat((d/2)-1, fld);
    v[d/2+1][d] := One(fld);
    v{[(d/2)+2..d]}{[(d/2)+1..d-1]} := IdentityMat((d/2)-1, fld);

    return [s, t, tBar, delta, deltaBar, u, v];

end
);



#####
# __LGOStandardGensOmegaCircleEvenChar()
#####

InstallGlobalFunction(  __LGOStandardGensOmegaCircleEvenChar,
function(d,q)
    
    return LGOStandardGensSpEvenChar(d-1,q);

end
);



#####
# __LGOStandardGensOmegaMinusEvenChar()
#####

InstallGlobalFunction(  __LGOStandardGensOmegaMinusEvenChar,
function(d,q)
    local s, t, delta, u, v, sigma, fld, w, n, S1, lambda, A, B, C, gamma,perm, inv, gamma2, nu;
    
    fld := GF(q);
    gamma := PrimitiveElement(GF(q^2));
    gamma2 := PrimitiveElement(GF(q));
    w := gamma^(q+1);

    nu := gamma + gamma^q;
    if nu <> Zero(fld) then
        nu := gamma2^LogFFE(nu,gamma2);
    else
        nu := Zero(fld);
    fi;
    s := IdentityMat( d, fld );
    s[1][1] := Zero(fld);
    s[d][d] := Zero(fld);
    s[1][d] := One(fld);
    s[d][1] := One(fld);
    s[(d/2)+1][d/2] := nu * One(fld);

    t := IdentityMat( d, fld );
    t[1][d] := One(fld);
    t[1][(d/2) ] := One(fld);
    t[(d/2) + 1][d] := nu;
    
    A :=((gamma^(-1))+(gamma^(-q)));
    if A <> Zero(fld) then
        A := gamma2^LogFFE(A,gamma2);
    else
        A := Zero(fld);
    fi;
    B := ((gamma^(1)) + (gamma^(q)));
    if B <> Zero(fld) then
        B := gamma2^LogFFE(B,gamma2);
    else
        B := Zero(fld);
    fi;
    C := ((gamma^(-q+1)) + (gamma^(q-1))+1);
    if C <> Zero(fld) then
        C := gamma2^LogFFE(C,gamma2);
    else
        C := Zero(fld);
    fi;
    w := gamma2^LogFFE(w,gamma2);
    delta := IdentityMat( d, fld );
    delta[1][1] := w;
    delta[d][d] := w^(-1);
    delta[(d/2)][(d/2)] := One(fld);
    delta[(d/2)+1][(d/2)+1] := C;
    delta[(d/2)][(d/2)+1] := A;
    delta[(d/2)+1][(d/2)] := B;
    
    u := IdentityMat( d, fld );
    u{[1..2]}{[1..2]} := [[0,1],[1,0]];
    u{[d-1,d]}{[d-1,d]} := [[0,1],[1,0]];
    u := u * One(fld);
    
    n := Int(d * 0.5)-1;
    v := 0 * IdentityMat( d, fld );
    v[(d/2)][(d/2)] := One(fld);
    v[(d/2)+1][(d/2)+1] := One(fld);
    v[(d/2) - 1][1] := One(fld);
    v{[1..(d/2)-2]}{[2..((d/2)-1)]} := IdentityMat((d/2)-2, fld);
    v[(d/2) + 2][d] := One(fld);
    v{[(d/2)+3..d]}{[(d/2)+2..d-1]} := IdentityMat((d/2)-2, fld);

    return [s, t, delta, u, v];

end
);



#####
# MSO()
#####

InstallGlobalFunction(  MSO,
function(e,d,q)
    local gens, G, inv, i, s, q2, q2i, perm, k, m;
    
    #Test Input TODO

    if e = 1 then
        gens := __LGOStandardGensSOPlus(d,q);
        
        m:= d / 2;
        
        s  := 1;
        q2 := q^2;
        q2i:= 1;
        for i in [ 1 .. m-1 ] do
          q2i:= q2 * q2i;
          s  := s * (q2i-1);
        od;
        
        perm := ();
        k := 1;
        while k < d do
            perm := perm * (k,d-k+1);
            k := k+2;
        od;
        inv := PermutationMat(perm,d) * One(GF(q));
        
        G  := GroupByGenerators(gens);
        SetDimensionOfMatrixGroup( G, d );
        SetFieldOfMatrixGroup( G, GF(q) );
        SetSize( G, q^(m*(m-1)) * (q^m-1) * s );
        SetInvariantBilinearForm( G, rec( matrix:=inv) );
        
        inv := Zero(GF(q)) * IdentityMat(d);
        for k in [1..(d/2)] do
            inv[k][d-k+1] := 1;
        od;
        
        SetInvariantQuadraticForm( G, rec( matrix:=inv) );
        SetIsFullSubgroupGLorSLRespectingBilinearForm( G, true );
        
    elif e = -1 then
        #gens := __LGOStandardGensChangeSOMinus(d,q);
        gens := __LGOStandardGensSOMinus(d,q);
        
        m:= d/2;
        
        s  := 1;
        q2 := q^2;
        q2i:= 1;
        for i in [ 1 .. m-1 ] do
          q2i:= q2 * q2i;
          s  := s * (q2i-1);
        od;
        
        perm := ();
        k := 1;
        while k < d do
            perm := perm * (k,d-k+1);
            k := k+2;
        od;
        inv := PermutationMat(perm,d) * One(GF(q));
        inv[m][m+1] := 0;
        inv[m+1][m] := 0;
        inv[m][m] := 2*PrimitiveElement(GF(q));
        inv[m+1][m+1] := -2;
        inv := inv * One(GF(q));
        
        G := GroupWithGenerators(gens);
        SetDimensionOfMatrixGroup( G, d );
        SetFieldOfMatrixGroup( G, GF(q) );
        SetSize( G, q^(m*(m-1)) * (q^m+1) * s );
        SetInvariantBilinearForm( G, rec( matrix:=inv) );
        
        inv := Zero(GF(q)) * IdentityMat(d);
        for k in [1..(d/2)-1] do
            inv[k][d-k+1] := 1 * One(GF(q));
        od;
        inv[d/2][d/2] := PrimitiveElement(GF(q));
        inv[(d/2)+1][(d/2)+1] := -1 * One(GF(q));
        
        SetInvariantQuadraticForm( G, rec( matrix:=inv) );
        SetIsFullSubgroupGLorSLRespectingBilinearForm( G, true );
        
    elif e = 0 then
        gens := __LGOStandardGensSOCircle(d,q);
        
        m:= ( d-1 ) / 2;
        
        s  := 1;
        q2 := q^2;
        q2i:= 1;
        for i in [ 1 .. m ] do
          q2i:= q2 * q2i;
          s  := s * (q2i-1);
        od;
        
        perm := ();
        k := 1;
        while k < (d+1)/2 do
            perm := perm * (k,d-k+1);
            k := k+1;
        od;
        inv := PermutationMat(perm,d) * One(GF(q));
        inv[(d+1)/2][(d+1)/2] := One(GF(q)) * (- 1/2);
        
        G := GroupByGenerators(gens);
        SetDimensionOfMatrixGroup( G, d );
        SetFieldOfMatrixGroup( G, GF(q) );
        SetSize( G, q^(m^2) * s  );
        SetInvariantBilinearForm( G, rec( matrix:=inv) );
        
        #inv := Zero(GF(q)) * IdentityMat(d);
        #for k in [1..(d/2)-1] do
        #    inv[k][d-k+1] := 1;
        #od;
        #inv[d/2][d/2] := PrimitiveElement(GF(q));
        #inv[(d/2)+1][(d/2)+1] := -1 * One(GF(q));
        
        #SetInvariantQuadraticForm( G, rec( matrix:=inv) );
        # Quadratic Form of Circle Typ??? TODO
        SetIsFullSubgroupGLorSLRespectingBilinearForm( G, true );
        
    else
        Error("e has to be 1, -1 or 0.");
    fi;
    
    return G;

end
);



#####
# UnitriangularDecompositionSOPlus
#####

InstallGlobalFunction(  UnitriangularDecompositionSOPlus,
function(arg)
    local g, u1, u2, j, r ,c, z, fld, f, i, a, d, stdgens, TransvecAtAlpha2, TransvecAtAlpha3, TransvecAtAlpha4, ShiftTransvection3ByJ, ShiftTransvection3ByI, ShiftTransvection4, ShiftTransvection2ByJ, ShiftTransvection2ByI, test, CalcXY, XX, YY, DeltaStarNumber, ell, slp, hs, tmppos, tmppos2, AEMrespos, u1pos, u2pos, tvpos, T2pos, T3pos, uipos, deltaStar;
    
    
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

        instr := AEM( 8, AEMrespos, tmppos, i-2 );
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
            Add(slp, [[uipos[ui-(d/2-abnr)],1,tvpos,1,uipos[ui-(d/2-abnr)],-1],tvpos]);
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
            Add(slp, [[uipos[ui],-1,tvpos,1,uipos[ui],1],tvpos]);
            ui := ui+1;
        od;

    end;

    #####
    # ShiftTransvection3ByJ()
    #####

    ShiftTransvection3ByJ := function(i)

        local instr;

        i := i-1;

        Add(slp,[[2,1,8,-1],tmppos2]);
        instr := AEM( tmppos2, AEMrespos, tmppos, i-1 );
        Append( slp, instr );
        Add( slp, [ [ AEMrespos, 1, tvpos , 1, AEMrespos, -1 ], tvpos ] );

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
        # The first 18 entries are the stdgens and the inverses
        # s, t, del, v, x, s^-1, t^-1, del^-1, v^-1, x^-1
        slp := [    [1,1], [2,1], [3,1], [4,1], [5,1], [6,1], [7,1], [8,1], [9,1],
                    [1,-1],[2,-1],[3,-1],[4,-1],[5,-1], [6,-1], [7,-1], [8,-1], [9,-1]   ];
    fi;

    d := Length( g );
    fld := FieldOfMatrixList( stdgens );

    # To create an MSLP, we allocate all the memory needed at the beginning.
    Add( slp, [1,0] );        tmppos       := Length(slp);    #19
    Add( slp, [1,0] );        AEMrespos    := Length(slp);    #20
    Add( slp, [1,0] );        u1pos        := Length(slp);    #21
    Add( slp, [1,0] );        u2pos        := Length(slp);    #22
    Add( slp, [1,0] );        tvpos        := Length(slp);    #23
    Add( slp, [1,0] );        tmppos2      := Length(slp);    #24
    Add( slp, [1,0] );        deltaStar    := Length(slp);    #25


    u1 := MutableCopyMat( One(g) );
    u2 := MutableCopyMat( One(g) );

    # If g is already a monomial matrix return u_1 = u_2 = I_d
    if TestIfMonomial( g ) then
        Add( slp, [ [1,0],[1,0] ] );
        return [ slp, [u1,g,u2] ];
    fi;

    f := LogInt(Size(fld), Characteristic(fld)); #ie q=p^f

    hs := HighestSlotOfSLP(slp);
    
    # deltaStar
    CalcXY := Size(fld)-1;
    YY := 0;
    while CalcXY mod 2 = 0 do
        YY := YY + 1;
        CalcXY := Int(CalcXY*0.5);
    od;
    XX := (Size(fld)-1)/(2^YY);
    if XX = 1 then
        Add( slp, [ [9,1], deltaStar ] );
     else
        DeltaStarNumber := (1-XX)/2 mod (Size(fld)-1);
        Add( slp, [ [6,DeltaStarNumber,5,DeltaStarNumber,9,1], deltaStar ] );
    fi;

    # We create the help variables for the block top left or bottom right
    T2pos := [ hs + 1 .. hs + f ];

    hs := hs + f;

    for ell in [ 1..f ] do
        Add(slp, [1,0] );
    od;

    for ell in [0..f-1] do

        Add(slp, [ [deltaStar, -ell, 8, -2, deltaStar, ell, 8 ,2 ], tmppos ] );
        Add(slp, [ [tmppos, 1, 2, 1, 4, -1, 2, -1, tmppos, -1], T2pos[ell+1] ] );

    od;

    # We create the help variables for the block in the bottom left
    T3pos := [ hs + 1 .. hs + f ];

    hs := hs + f;

    for ell in [ 1..f ] do
        Add(slp, [1,0] );
    od;

    for ell in [0..f-1] do

        Add(slp, [ [deltaStar, -ell, 8, -2, deltaStar, ell, 8 ,2 ], tmppos ] );
        Add(slp, [ [tmppos, 1, 1, 1, 3, -1, 1, -1, tmppos, -1], T3pos[ell+1] ] );

    od;

    # We create the help variables for the shift

    uipos := [ hs + 1 .. (hs + (d/2)-2) ];

    hs := hs + ((d/2)-2) ;

    for ell in [ 1 .. ((d/2)-2)  ] do
        Add(slp, [1,0] );
    od;

    Add( slp, [[2,1],uipos[1]]);

    for ell in [2..((d/2)-2) ] do
            Add( slp, [ [ 8, -1, uipos[ell-1] , 1, 8, 1 ], uipos[ell] ] );
    od;

    ############
    # Tests
    ############

    #test :=PseudoRandom(fld);

    #Display(test);
    
    #Add(slp, [[T3pos[2],1], T3pos[2]]);

    #TransvecAtAlpha2(test);
    #ShiftTransvection2ByI(4);
    #ShiftTransvection2ByJ(1, 4);

    #TransvecAtAlpha4(test);
    #ShiftTransvection4(7);

    #TransvecAtAlpha3(test);
    #ShiftTransvection3ByJ(4);
    #ShiftTransvection3ByI(6);

    #Add(slp, [[tvpos,1],tvpos]);

    #return MakeSLP(slp,9);

    ############
    # Main
    ############

    g := MutableCopyMat( g );

    for c in [ d, d-1..d/2+1 ] do

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

            # Clear the rest of column c
            for i in [ r+1..d ] do

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
                                    TransvecAtAlpha3(-z);
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
                                    TransvecAtAlpha3(-z);
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
                                g[d-r+1] := g[d-r+1] + (-z)*g[d-i+1];
                                u1[d-r+1] := u1[d-r+1] + (-z)*u1[d-i+1];
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
                                TransvecAtAlpha3(-z);
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

                        #Mul[i][r] := z;
                        #g[i] := g[i] + z*g[r];
                        #u1[i] := u1[i] + z*u1[r];

                        #Mul[d-r+1][d-i+1] := -z;
                        #g[d-r+1] := g[d-r+1] + (-z)*g[d-i+1];
                        #u1[d-r+1] := u1[d-r+1] + (-z)*u1[d-i+1];
                        
                        Add(slp,[[tvpos,1,u1pos,1],u1pos]);
                    
                    fi;
                fi;
            od;
        fi;


        # Step Two: Clear all entries in row r apart from g[r][c]
        # This coincides with multiplying t_{c,j} from right.
        if c >= 2 then

            # Now clear the rest of row r
            for j in [ c-1, c-2..1 ] do

                if not IsZero( g[r][j] ) then

                    z := - g[r][j] * a;

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
                            g{[1..d]}[d-c+1] :=  g{[1..d]}[d-c+1] + (-z) *  g{[1..d]}[d-j+1];
                            u2{[1..d]}[d-c+1] := u2{[1..d]}[d-c+1] + (-z) * u2{[1..d]}[d-j+1];
                        fi;

                        #Mul[c][j] := z;
                        #g{[1..d]}[j] :=  g{[1..d]}[j] + z *  g{[1..d]}[c];
                        #u2{[1..d]}[j] := u2{[1..d]}[j] + z * u2{[1..d]}[c];

                        #Mul[d-j+1][d-c+1] := -z;
                        #g{[1..d]}[d-c+1] :=  g{[1..d]}[d-c+1] + (-z) *  g{[1..d]}[d-j+1];
                        #u2{[1..d]}[d-c+1] := u2{[1..d]}[d-c+1] + (-z) * u2{[1..d]}[d-j+1];
                        
                        Add(slp,[[u2pos,1,tvpos,1],u2pos]);
                      
                    fi;
                fi;
            od;
        fi;
    od;

    # Now u1^-1 * g * u2^-1 is the input matrix
    #return [g,u1,u2];
    
    Add( slp, [ [u1pos,1], [u2pos,1] ]);

    # Now u1^-1 * g * u2^-1 is the input matrix
    return [slp,[g, u1, u2], hs];


end
);



#####
# UnitriangularDecompositionSOCircle
#####

InstallGlobalFunction(  UnitriangularDecompositionSOCircle,
function(arg)
    local g, u1, u2, j, r ,c, z, fld, f, i, a, d, stdgens, TransvecAtAlpha2, TransvecAtAlpha3, TransvecAtAlpha5, ShiftTransvection3ByJ, ShiftTransvection3ByI, ShiftTransvection5, ShiftTransvection2ByJ, ShiftTransvection2ByI, test, CalcXY, XX, YY, DeltaStarNumber, ell, slp, hs, tmppos, tmppos2, AEMrespos, u1pos, u2pos, tvpos, T2pos, T3pos, uipos, deltaStar, T5pos, jjj;
    
    
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

        instr := AEM( 5, AEMrespos, tmppos, i-1 );
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
            Add(slp, [[uipos[ui-(d/2-abnr)],1,tvpos,1,uipos[ui-(d/2-abnr)],-1],tvpos]);
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
            Add(slp, [[uipos[ui],-1,tvpos,1,uipos[ui],1],tvpos]);
            ui := ui+1;
        od;

    end;

    #####
    # ShiftTransvection3ByJ()
    #####

    ShiftTransvection3ByJ := function(i)

        local instr;

        i := i-1;

        Add(slp,[[5,1,4,-1],tmppos2]);
        instr := AEM( tmppos2, AEMrespos, tmppos, i-1 );
        Append( slp, instr );
        Add( slp, [ [ AEMrespos, -1, tvpos , 1, AEMrespos, 1 ], tvpos ] );

    end;
    
    #####
    # TransvectionAtAlpha5()
    #####

    TransvecAtAlpha5 := function( alpha )

        local cc, ell, instr;

        # if omega = 1 then we overwrite the position for tv with Ti(1)
        if IsOne( alpha ) then
            Add(slp, [ [ T5pos[1], 1 ], tvpos ] );
            return;
        fi;

        cc := CoefficientsPrimitiveElement( fld, alpha );
        instr := [];

        for ell in [ 1..Length(cc) ] do

            if not IsZero( cc[ell] ) then
                Append( instr, [ T5pos[ell], Int(cc[ell]) ] );
            fi;
        od;

        if Length( instr ) = 0 then
            Error("TransvecAtAlpha5: this should not happen");
        fi;

        Add( slp, [ instr,tvpos ] );

    end;

    #####
    # ShiftTransvection5()
    #####

    ShiftTransvection5 := function(i)
        local instr;

        i := d-i+1;

        if (i<d+1 ) then
            instr := AEM( 5, AEMrespos, tmppos, i-1 );
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
                    [1,-1],[2,-1],[3,-1],[4,-1],[5,-1], [6,-1]  ];
    fi;

    d := Length( g );
    fld := FieldOfMatrixList( stdgens );

    # To create an MSLP, we allocate all the memory needed at the beginning.
    Add( slp, [1,0] );        tmppos       := Length(slp);    #13
    Add( slp, [1,0] );        AEMrespos    := Length(slp);    #14
    Add( slp, [1,0] );        u1pos        := Length(slp);    #15
    Add( slp, [1,0] );        u2pos        := Length(slp);    #16
    Add( slp, [1,0] );        tvpos        := Length(slp);    #17
    Add( slp, [1,0] );        tmppos2      := Length(slp);    #18
    Add( slp, [1,0] );        deltaStar    := Length(slp);    #19


    u1 := MutableCopyMat( One(g) );
    u2 := MutableCopyMat( One(g) );

    # If g is already a monomial matrix return u_1 = u_2 = I_d
    if TestIfMonomial( g ) then
        Add( slp, [ [1,0],[1,0] ] );
        return [ slp, [u1,g,u2] ];
    fi;

    f := LogInt(Size(fld), Characteristic(fld)); #ie q=p^f

    hs := HighestSlotOfSLP(slp);
    
    # deltaStar
    CalcXY := Size(fld)-1;
    YY := 0;
    while CalcXY mod 2 = 0 do
        YY := YY + 1;
        CalcXY := Int(CalcXY*0.5);
    od;
    XX := (Size(fld)-1)/(2^YY);
    if XX = 1 then
        Add( slp, [ [6,1], deltaStar ] );
     else
        DeltaStarNumber := (1-XX)/2 mod (Size(fld)-1);
        Add( slp, [ [3,DeltaStarNumber,6,1], deltaStar ] );
    fi;
            
    jjj := Int(2^(-1) * One(fld));
    Add(slp, [ [5, -1, 2, -1, 5, 1, 2 , jjj, 5, -1, 2, 1, 5, 1, 2, -jjj ], tmppos2 ] );

    # We create the help variables for the block top left or bottom right
    T2pos := [ hs + 1 .. hs + f ];

    hs := hs + f;

    for ell in [ 1..f ] do
        Add(slp, [1,0] );
    od;

    for ell in [0..f-1] do

        Add(slp, [ [deltaStar, -ell, 5, -2, deltaStar, ell, 5 ,2 ], tmppos ] );
        Add(slp, [ [tmppos, 1, 1, -1, 4, -1, tmppos2, -1, 4, 1, 1, 1, tmppos, -1], T2pos[ell+1] ] );

    od;

    # We create the help variables for the block in the bottom left
    T3pos := [ hs + 1 .. hs + f ];

    hs := hs + f;

    for ell in [ 1..f ] do
        Add(slp, [1,0] );
    od;

    for ell in [0..f-1] do

        Add(slp, [ [deltaStar, -ell, 5, -2, deltaStar, ell, 5 ,2 ], tmppos ] );
        Add(slp, [ [tmppos, 1, 1, -1, 4, -1, 1, -1, 4, -1, tmppos2, 1, 4, 1, 1, 1, 4, 1, 1, 1, tmppos, -1], T3pos[ell+1] ] );

    od;
    
    # We create the help variables for the centre row and column
    T5pos := [ hs + 1 .. hs + f ];

    hs := hs + f;

    for ell in [ 1..f ] do
        Add(slp, [1,0] );
    od;

    for ell in [0..f-1] do

        Add(slp, [ [deltaStar, -ell, 5, -2, deltaStar, ell, 5 ,2 ], tmppos ] );
        Add(slp, [ [tmppos, 1, 1, -1, 2, -jjj, 1, 1, tmppos, -1], T5pos[ell+1] ] );

    od;

    # We create the help variables for the shift
    uipos := [ hs + 1 .. (hs + ((d-1)/2)-2) ];

    hs := hs + (((d-1)/2)-2) ;

    for ell in [ 1 .. (((d-1)/2)-2)  ] do
        Add(slp, [1,0] );
    od;

    if (uipos <> [] ) then
        Add( slp, [[4,1],uipos[1]]);
    fi;

    for ell in [2..(((d-1)/2)-2) ] do
            Add( slp, [ [ 5, -1, uipos[ell-1] , 1, 5, 1 ], uipos[ell] ] );
    od;

    ############
    # Tests
    ############

    #test :=PseudoRandom(fld);
    #test := 2 * One(GF(3));
    #Display(test);
    
    #Add(slp, [[T5pos[2],1],tvpos]);

    #TransvecAtAlpha2(test);
    #ShiftTransvection2ByI(3);
    #ShiftTransvection2ByJ(1, 3);

    #TransvecAtAlpha3(test);
    #ShiftTransvection3ByJ(5);
    #ShiftTransvection3ByI(8);
    
    #TransvecAtAlpha5(test);
    #ShiftTransvection5(9);

    #Add(slp, [[tvpos,1],tvpos]);

    #return MakeSLP(slp,6);

    ############
    # Main
    ############;

    g := MutableCopyMat( g );

    for c in [ d, d-1..(d-1)/2 ] do

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

                if (i+r <> d+1) then
                
                    TransvecAtAlpha5(2*z);
                    ShiftTransvection5(d-r+1);
                    Add(slp,[[tvpos,1,u1pos,1],u1pos]);

                    g[d-r+1] := g[d-r+1] + z^2 * g[r];
                    u1[d-r+1] := u1[d-r+1] + z^2 * u1[r];

                    #Mul[d-r+1][d-i+1] := -z^phi;
                    g[d-r+1] := g[d-r+1] + 2*z * g[d-i+1];
                    u1[d-r+1] := u1[d-r+1] + 2*z * u1[d-i+1];

                    g[i] := g[i] + z*g[r];
                    u1[i] := u1[i] + z*u1[r];
                fi;
            fi;


            # Second: Clear the rest of column c
            for i in [ r+1..d ] do

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
                            TransvecAtAlpha2(-z);
                            ShiftTransvection2ByI(d-r+1);
                            ShiftTransvection2ByJ(d-i+1,d-r+1);
                        elif i+r < d+1 then
                            TransvecAtAlpha3(-z);
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
                        g[d-r+1] := g[d-r+1] + (-z) * g[d-i+1];
                        u1[d-r+1] := u1[d-r+1] + (-z) * u1[d-i+1];
                        
                        Add(slp,[[tvpos,1,u1pos,1],u1pos]);

                    fi;
                fi;
            od;
        fi;



        # Step Two: Clear all entries in row r apart from g[r][c]
        # This coincides with multiplying t_{c,j} from right.
        if c >= 2 then


            if not IsZero(g[r][(d+1)/2]) and (r <> ((d+1)/2)) then
                j := (d+1)/2;
                z := -g[r][j] * a;

                if (c+j <> d+1) then
                
                    TransvecAtAlpha5(z);
                    ShiftTransvection5(c);
                    Add(slp,[[u2pos,1,tvpos,1],u2pos]);

                    g{[1..d]}[d-c+1] :=  g{[1..d]}[d-c+1] + ((1/2)*z)^2 *  g{[1..d]}[c];
                    u2{[1..d]}[d-c+1] := u2{[1..d]}[d-c+1] + ((1/2)*z)^2 * u2{[1..d]}[c];

                    g{[1..d]}[d-c+1] :=  g{[1..d]}[d-c+1] + (1/2)*z *  g{[1..d]}[d-j+1];
                    u2{[1..d]}[d-c+1] := u2{[1..d]}[d-c+1] + (1/2)*z * u2{[1..d]}[d-j+1];

                    g{[1..d]}[j] :=  g{[1..d]}[j] + z *  g{[1..d]}[c];
                    u2{[1..d]}[j] := u2{[1..d]}[j] + z * u2{[1..d]}[c];
                    
                fi;
            fi;

            # Now clear the rest of row r
            for j in [ c-1, c-2..1 ] do

                if not IsZero( g[r][j] ) and (j <> (d+1)/2) then

                    z := - g[r][j] * a;

                    if (c+j <> d+1) then
                    
                        if c in [1..(d+1)/2] and j in [1..(d+1)/2] then
                            TransvecAtAlpha2(z);
                            ShiftTransvection2ByI(c);
                            ShiftTransvection2ByJ(j, c);
                        elif c in [(((d+1)/2)+1)..d] and j in [(((d+1)/2)+1)..d] then
                            TransvecAtAlpha2(-z);
                            ShiftTransvection2ByI(d-j+1);
                            ShiftTransvection2ByJ(d-c+1,d-j+1);
                        elif c+j < d+1 then
                            TransvecAtAlpha3(-z);
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
                        g{[1..d]}[d-c+1] :=  g{[1..d]}[d-c+1] + (-z) *  g{[1..d]}[d-j+1];
                        u2{[1..d]}[d-c+1] := u2{[1..d]}[d-c+1] + (-z) * u2{[1..d]}[d-j+1];
                        
                        Add(slp,[[u2pos,1,tvpos,1],u2pos]);
                        
                    fi;
                fi;
            od;
        fi;
    od;
    
    Add( slp, [ [u1pos,1], [u2pos,1] ]);
        
    # Now u1^-1 * g * u2^-1 is the input matrix
    return [slp,[g, u1, u2], hs];

end
);



#####
# UnitriangularDecompositionSOMinus
#####

InstallGlobalFunction(  UnitriangularDecompositionSOMinus,
function(arg)

    local g, u1, u2, j, r ,c, z, fld, f, i, a, d, w, A, B, C, k, mat, A2, B2, C2, A3, B3, C3, StartValue, slp, TransvecAtAlpha2, TransvecAtAlpha3, TransvecAtAlpha5, TransvecAtAlpha6, ShiftTransvection2ByI, ShiftTransvection3ByI, ShiftTransvection2ByJ, ShiftTransvection3ByJ, ShiftTransvection5, ShiftTransvection6, tvpos, T2pos, T3pos, T5pos, T6pos, uipos, tmppos, tmppos2, hs, ell, StartValueForFirstCentreRow, stdgens, AEMrespos, u1pos, u2pos, jjj, MakeEntry1, test;
    
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

        instr := AEM( 5, AEMrespos, tmppos, i-1 );
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
            Add(slp, [[uipos[ui-(d/2-abnr)],1,tvpos,1,uipos[ui-(d/2-abnr)],-1],tvpos]);
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
            Add(slp, [[uipos[ui],-1,tvpos,1,uipos[ui],1],tvpos]);
            ui := ui+1;
        od;

    end;

    #####
    # ShiftTransvection3ByJ()
    #####

    ShiftTransvection3ByJ := function(i)

        local instr;

        i := i-1;

        Add(slp,[[5,1,4,-1],tmppos2]);
        instr := AEM( tmppos2, AEMrespos, tmppos, i-1 );
        Append( slp, instr );
        Add( slp, [ [ AEMrespos, -1, tvpos , 1, AEMrespos, 1 ], tvpos ] );

    end;
    
    #####
    # TransvectionAtAlpha5()
    #####

    TransvecAtAlpha5 := function( alpha )

        local cc, ell, instr;

        # if omega = 1 then we overwrite the position for tv with Ti(1)
        if IsOne( alpha ) then
            Add(slp, [ [ T5pos[1], 1 ], tvpos ] );
            return;
        fi;

        cc := CoefficientsPrimitiveElement( fld, alpha );
        instr := [];

        for ell in [ 1..Length(cc) ] do

            if not IsZero( cc[ell] ) then
                Append( instr, [ T5pos[ell], Int(cc[ell]) ] );
            fi;
        od;

        if Length( instr ) = 0 then
            Error("TransvecAtAlpha5: this should not happen");
        fi;

        Add( slp, [ instr,tvpos ] );

    end;

    #####
    # ShiftTransvection5()
    #####

    ShiftTransvection5 := function(i)
        local instr;

        i := d-i+1;

        if (i<d+1 ) then
            instr := AEM( 5, AEMrespos, tmppos, i-1 );
            Append( slp, instr );
            Add( slp, [ [ AEMrespos, -1, tvpos , 1, AEMrespos, 1 ], tvpos ] );
        fi;

    end;
    
    #####
    # TransvectionAtAlpha6()
    #####

    TransvecAtAlpha6 := function( alpha )

        local cc, ell, instr;

        # if omega = 1 then we overwrite the position for tv with Ti(1)
        if IsOne( alpha ) then
            Add(slp, [ [ T6pos[1], 1 ], tvpos ] );
            return;
        fi;

        cc := CoefficientsPrimitiveElement( fld, alpha );
        instr := [];

        for ell in [ 1..Length(cc) ] do

            if not IsZero( cc[ell] ) then
                Append( instr, [ T6pos[ell], Int(cc[ell]) ] );
            fi;
        od;

        if Length( instr ) = 0 then
            Error("TransvecAtAlpha5: this should not happen");
        fi;

        Add( slp, [ instr,tvpos ] );

    end;

    #####
    # ShiftTransvection6()
    #####

    ShiftTransvection6 := function(i)
        local instr;

        i := d-i+1;

        if (i<d+1 ) then
            instr := AEM( 5, AEMrespos, tmppos, i-1 );
            Append( slp, instr );
            Add( slp, [ [ AEMrespos, -1, tvpos , 1, AEMrespos, 1 ], tvpos ] );
        fi;

    end;
    
    #####
    # StartValueForFirstCentreRow()
    #####
    
    StartValueForFirstCentreRow := function(q)
        local i, j, gamma, omega, alpha, delta, t, gens;
    
        w := PrimitiveElement(GF(q));
        gamma := PrimitiveElement(GF(q^2));
        alpha := gamma^((q+1)/2);
        
        for j in [1..q] do
            if ( (2^(-1)*alpha^(-1)*(gamma^(-2*j)-gamma^(-2*j*q))) in GF(Characteristic(GF(q)))) and ((2^(-1)*alpha^(-1)*(gamma^(-2*j)-gamma^(-2*j*q))) <> Zero(GF(q))) then
                return [j,Int((2^(-1)*alpha^(-1)*(gamma^(-2*j)-gamma^(-2*j*q)))), (gamma^(2*-j)+gamma^(2*-j*q)-2^(-1)*(gamma^(-2*j)+gamma^(-2*j*q)) + 2)];
            fi;
        od;
        
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
                    [1,-1],[2,-1],[3,-1],[4,-1],[5,-1], [6,-1]  ];
    fi;

    d := Length( g );
    fld := FieldOfMatrixList( stdgens );
    
    mat := GeneratorsOfGroup(MSO(-1,d,Size(fld)))[3];
    w := mat[1][1];   #TODO Choose primitiveElement from LGO Standard generator, such that the generator are the same
    A := mat[d/2][d/2];
    B := mat[d/2][(d/2)+1];
    C := mat[(d/2)+1][d/2];

    # To create an MSLP, we allocate all the memory needed at the beginning.
    Add( slp, [1,0] );        tmppos       := Length(slp);    #13
    Add( slp, [1,0] );        AEMrespos    := Length(slp);    #14
    Add( slp, [1,0] );        u1pos        := Length(slp);    #15
    Add( slp, [1,0] );        u2pos        := Length(slp);    #16
    Add( slp, [1,0] );        tvpos        := Length(slp);    #17
    Add( slp, [1,0] );        tmppos2      := Length(slp);    #18

    u1 := MutableCopyMat( One(g) );
    u2 := MutableCopyMat( One(g) );

    # If g is already a monomial matrix return u_1 = u_2 = I_d
    if TestIfMonomial( g ) then
        Add( slp, [ [1,0],[1,0] ] );
        return [ slp, [u1,g,u2] ];
    fi;

    f := LogInt(Size(fld), Characteristic(fld)); #ie q=p^f

    hs := HighestSlotOfSLP(slp);
            
    jjj := Int(2^(-1) * One(fld));
    Add(slp, [ [5, -1, 2, -1, 5, 1, 2 , jjj, 5, -1, 2, 1, 5, 1, 2, -jjj ], tmppos2 ] );

    # We create the help variables for the block top left or bottom right
    T2pos := [ hs + 1 .. hs + f ];

    hs := hs + f;

    for ell in [ 1..f ] do
        Add(slp, [1,0] );
    od;

    for ell in [0..f-1] do

        Add(slp, [ [3, -ell, 5, -2, 3, ell, 5 ,2 ], tmppos ] );
        Add(slp, [ [tmppos, 1, 1, -1, 4, -1, tmppos2, -1, 4, 1, 1, 1, tmppos, -1], T2pos[ell+1] ] );

    od;

    # We create the help variables for the block in the bottom left
    T3pos := [ hs + 1 .. hs + f ];

    hs := hs + f;

    for ell in [ 1..f ] do
        Add(slp, [1,0] );
    od;

    for ell in [0..f-1] do

        Add(slp, [ [3, -ell, 5, -2, 3, ell, 5 ,2 ], tmppos ] );
        Add(slp, [ [tmppos, 1, 1, -1, 4, -1, 1, -1, 4, -1, tmppos2, 1, 4, 1, 1, 1, 4, 1, 1, 1, tmppos, -1], T3pos[ell+1] ] );

    od;
    
    # We create the help variables for the sencond centre row and column
    T5pos := [ hs + 1 .. hs + f ];

    hs := hs + f;

    for ell in [ 1..f ] do
        Add(slp, [1,0] );
    od;

    for ell in [0..f-1] do

        Add(slp, [ [3, -ell, 5, -2, 3, ell, 5 ,2 ], tmppos ] );
        Add(slp, [ [tmppos, 1, 1, -1, 2, 1, 1, 1, tmppos, -1], T5pos[ell+1] ] );

    od;
    
    # We create the help variables for the first centre row and column
    T6pos := [ hs + 1 .. hs + f ];

    hs := hs + f;

    for ell in [ 1..f ] do
        Add(slp, [1,0] );
    od;
    
    StartValue := StartValueForFirstCentreRow(Size(fld));
    MakeEntry1 := StartValue[2];
    z := -StartValue[3];
    StartValue := StartValue[1];
    Add(slp, [ [3,-StartValue, 2, 2, 3, StartValue, 3, -StartValue, 2, -1, 3, StartValue, 2, 2 ], tmppos2 ] );
    if z <> Zero(fld) then
        TransvecAtAlpha5(z);
        Add(slp,[[tmppos2,1,1,-1,tvpos,1,1,1],tmppos2]);
    fi;
    MakeEntry1 := Int((-1)*MakeEntry1^(-1) * One(fld));
    Add(slp, [ [tmppos2,MakeEntry1 ], tmppos2 ] );

    for ell in [0..f-1] do

        Add(slp, [ [3, -ell, 5, -2, 3, ell, 5 ,2 ], tmppos ] );
        Add(slp, [ [tmppos, 1, 1, -1, tmppos2, 1, 1, 1, tmppos, -1], T6pos[ell+1] ] );

    od;

    # We create the help variables for the shift
    uipos := [ hs + 1 .. (hs + (d/2)-2) ];

    hs := hs + ((d/2)-2) ;

    for ell in [ 1 .. ((d/2)-2)  ] do
        Add(slp, [1,0] );
    od;

    Add( slp, [[4,1],uipos[1]]);

    for ell in [2..((d/2)-2) ] do
            Add( slp, [ [ 5, -1, uipos[ell-1] , 1, 5, 1 ], uipos[ell] ] );
    od;

    ############
    # Tests
    ############

    #test :=PseudoRandom(fld);
    #Display(test);
    
    #Add(slp, [[T5pos[2],1],tvpos]);

    #TransvecAtAlpha2(test);
    #ShiftTransvection2ByI(4);
    #ShiftTransvection2ByJ(1, 4);

    #TransvecAtAlpha3(test);
    #ShiftTransvection3ByJ(5);
    #ShiftTransvection3ByI(8);
    
    #TransvecAtAlpha5(test);
    #ShiftTransvection5(9);

    #Add(slp, [[T5pos[2],1],tvpos]);

    #return MakeSLP(slp,6);

    ############
    # Main
    ############;

    g := MutableCopyMat( g );

    for c in [ d, d-1..(d/2)+2 ] do

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

            if (not(IsZero(g[d/2][c]))) then
                i := (d/2);
                z := -g[i][c] * a;

                if (i+r <> d+1) then
                
                    TransvecAtAlpha6(-z/(2*w));
                    ShiftTransvection6(d-r+1);
                    Add(slp,[[tvpos,1,u1pos,1],u1pos]);

                    g[d-r+1] := g[d-r+1] + -(z^2)/(4*w) * g[r];
                    u1[d-r+1] := u1[d-r+1] + -(z^2)/(4*w) * u1[r];

                    #Mul[d-r+1][d-i+1] := -z^phi;
                    g[d-r+1] := g[d-r+1] + -z/(2*w) * g[d-i];
                    u1[d-r+1] := u1[d-r+1] + -z/(2*w) * u1[d-i];

                    g[i] := g[i] + z*g[r];
                    u1[i] := u1[i] + z*u1[r];
                fi;
            fi;
            
            
            if (not(IsZero(g[(d/2)+1][c]))) then
                i := (d/2)+1;
                z := -g[i][c] * a;

                if (i+r <> d+1) then
                
                    TransvecAtAlpha5(2^(-1)*z);
                    ShiftTransvection5(d-r+1);
                    Add(slp,[[tvpos,1,u1pos,1],u1pos]);

                    g[d-r+1] := g[d-r+1] + z^2/4 * g[r];
                    u1[d-r+1] := u1[d-r+1] + z^2/4 * u1[r];

                    #Mul[d-r+1][d-i+1] := -z^phi;
                    g[d-r+1] := g[d-r+1] + z/2 * g[d-i+2];
                    u1[d-r+1] := u1[d-r+1] + z/2 * u1[d-i+2];

                    g[i] := g[i] + z*g[r];
                    u1[i] := u1[i] + z*u1[r];
                fi;
            fi;


            # Clear the rest of column c
            for i in [ r+1..d ] do

                if not IsZero(g[i][c]) then

                    z := -g[i][c] * a;

                    # add z times row r of g  to row i
                    # add z times row r of u1  to row i
                    #g[i] := g[i] + z*g[r];
                    #u1[i] := u1[i] + z*u1[r];
                    #Mul := List( One(SU(d,Size(fld))), ShallowCopy );

                    if (i+r <> d+1) then
                        
                        if i in [1..d/2] and r in [1..d/2] then
                            TransvecAtAlpha2(z);
                            ShiftTransvection2ByI(i);
                            ShiftTransvection2ByJ(r, i);
                        elif i in [((d/2)+1)..d] and r in [((d/2)+1)..d] then
                            TransvecAtAlpha2(-z);
                            ShiftTransvection2ByI(d-r+1);
                            ShiftTransvection2ByJ(d-i+1,d-r+1);
                        elif i+r < d+1 then
                            TransvecAtAlpha3(-z);
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
                        
                        Add(slp,[[tvpos,1,u1pos,1],u1pos]);
                    
                    fi;
                fi;
            od;
        fi;


        # Step Two: Clear all entries in row r apart from g[r][c]
        # This coincides with multiplying t_{c,j} from right.
        if c >= 2 then
            
            if not IsZero(g[r][(d/2)+1]) then
                j := (d/2)+1;
                z := -g[r][j] * a;

                if (c+j <> d+1) then
                
                    TransvecAtAlpha5(z);
                    ShiftTransvection5(c);
                    Add(slp,[[u2pos,1,tvpos,1],u2pos]);

                    g{[1..d]}[d-c+1] :=  g{[1..d]}[d-c+1] + z^2 *  g{[1..d]}[c];
                    u2{[1..d]}[d-c+1] := u2{[1..d]}[d-c+1] + z^2 * u2{[1..d]}[c];

                    g{[1..d]}[d-c+1] :=  g{[1..d]}[d-c+1] + 2*z *  g{[1..d]}[d-j+2];
                    u2{[1..d]}[d-c+1] := u2{[1..d]}[d-c+1] + 2*z * u2{[1..d]}[d-j+2];

                    g{[1..d]}[j] :=  g{[1..d]}[j] + z *  g{[1..d]}[c];
                    u2{[1..d]}[j] := u2{[1..d]}[j] + z * u2{[1..d]}[c];
                fi;
            fi;
            
                    
            if not IsZero(g[r][d/2]) then
                j := (d/2);
                z := -g[r][j] * a;

                if (c+j <> d+1) then
            
                    TransvecAtAlpha6(z);
                    ShiftTransvection6(c);
                    Add(slp,[[u2pos,1,tvpos,1],u2pos]);

                    g{[1..d]}[d-c+1] :=  g{[1..d]}[d-c+1] + -w*z^2 *  g{[1..d]}[c];
                    u2{[1..d]}[d-c+1] := u2{[1..d]}[d-c+1] + -w*z^2 * u2{[1..d]}[c];

                    g{[1..d]}[d-c+1] :=  g{[1..d]}[d-c+1] + -2*w*z *  g{[1..d]}[d-j];
                    u2{[1..d]}[d-c+1] := u2{[1..d]}[d-c+1] + -2*w*z * u2{[1..d]}[d-j];

                    g{[1..d]}[j] :=  g{[1..d]}[j] + z *  g{[1..d]}[c];
                    u2{[1..d]}[j] := u2{[1..d]}[j] + z * u2{[1..d]}[c];
                fi;
            fi;
            

            # Now clear the rest of row r
            for j in [ c-1, c-2..1 ] do

                if not IsZero( g[r][j] ) then

                    z := - g[r][j] * a;

                    if (c+j <>  d+1) then
                    
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
                        
                        Add(slp,[[u2pos,1,tvpos,1],u2pos]);
                      
                    fi;
                fi;
            od;
        fi;
    od;
    
    # Is there a way to improve this here?
    if (g[d/2][(d/2)+1] <> Zero(fld)) and (g[(d/2)+1][(d/2)+1] <> Zero(fld)) then
        k := 1;
        A2 := A;
        B2 := B;
        C2 := C;
        while true do
            if (A*g[d/2][(d/2)+1]+B*g[(d/2)+1][(d/2)+1] = Zero(fld)) or (A*g[d/2][(d/2)]+B*g[(d/2)+1][(d/2)] = Zero(fld)) then
                mat := MutableCopyMat(mat);
                mat[1][1] := w^k;
                mat[d][d] := w^(-k);
                mat[d/2][d/2] := A;
                mat[d/2][(d/2)+1] := B;
                mat[(d/2)+1][d/2] := C;
                mat[(d/2)+1][(d/2)+1] := A;
                g := mat*g;
                u1 := mat*u1;
                Add(slp,[[3,k,u1pos,1],u1pos]);
                break;
            fi;
            k := k+1;
            A3 := A*A2+B*C2;
            B3 := A*B2+A2*B;
            C3 := A*C2+A2*C;
            A := A3;
            B := B3;
            C := C3;
        od;
    fi;
    
    #test := MakeSLP(slp,6);
    #if (ResultOfStraightLineProgram(test,stdgens) <> u1) then
    #    Error("u1");
    #fi;
    #test := slp;
    #Add(test,[[u2pos,1],u2pos]);
    #test := MakeSLP(test,6);
    #if (ResultOfStraightLineProgram(test,stdgens) <> u2) then
    #    Error("u2");
    #fi;
    
    Add( slp, [ [u1pos,1], [u2pos,1] ]);

    # Now u1^-1 * g * u2^-1 is the input matrix
    return [slp,[g, u1, u2], hs];

end
);



#####
# MonomialSLPSOPlus
#####

InstallGlobalFunction(  MonomialSLPSOPlus,
function( arg )

    local slp, c, n, m, result, i, k, u1, u2, result2, test, g, stdgens, mat, perm, fld, mb, v, list, j, tp, tc, nu, random, diag, p_signwr, p_signpos, vpos, vipos, spos, upos, unpos, tpos, left, right, tmpvalue, perm2, L2, R2, cnt, pot, perm3, w, vf, instr, s, slpnu, Ev, Evf, EvfMinus, Es;
    
    
    # Check for correct Input
    if Length(arg) >= 2 and IsList(arg[1]) and IsMatrix(arg[2]) then

        stdgens := arg[1];  # the LGO standard generators
        mat := arg[2];        # the monomial matrix
        n := Length(stdgens[1]);
        m := (n/2)-1;

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

        # Info( InfoBruhat, 2, " and additional:  ",7," memory slots ", "in PermSLP()\n");
        
    else

        # we write an SLP into the variable slp
        # The first 12 entries are the stdgens and the inverses
        # s, t, del, v, x, s^-1, t^-1, del^-1, v^-1, x^-1
        # The entries 13 (resAEM) and 14 (tmpAEM) are used to save AEM-values
        slp := [    [1, 1], [2, 1], [3, 1], [4, 1], [5, 1], [6, 1], [7, 1], [8, 1], [9, 1],
                    [1,-1], [2,-1], [3,-1], [4,-1], [5,-1], [6,-1], [7,-1], [8,-1], [9,-1],
                    [1, 0], [1, 0]    ];

        cnt := 20;

        # Info( InfoBruhat, 2, "Memory Usage is: ",19,"  memory slots ", "in PermSLP()\n");
        
    fi;

    # Initialize the additional memory quota
    Add(slp, [ [1,0], cnt + 1 ] );    p_signpos := cnt + 1;    #13 or 20+3f
    Add(slp, [ [8,-1], cnt + 2 ] );    vpos      := cnt + 2;    #14 or 21+3f
    Add(slp, [ [8,-1], cnt + 3 ] );    vipos     := cnt + 3;    #15 or 22+3f
    Add(slp, [ [1,1], cnt + 4 ] );    spos      := cnt + 4;    #16 or 23+3f
    Add(slp, [ [2,1], cnt + 5 ] );    upos      := cnt + 5;    #17 or 24+3f
    Add(slp, [ [2,0], cnt + 6 ] );    unpos     := cnt + 6;    #18 or 25+3f
    Add(slp, [ [1,0], cnt + 7 ] );    tpos      := cnt + 7;    #19 or 26+3f
    Add(slp, [ [1,0], cnt + 8 ] );    left      := cnt + 8;    #20 or 27+3f
    Add(slp, [ [1,0], cnt + 9 ] );    right     := cnt + 9;    #21 or 28+3f

    if IsDiagonalMat( mat ) then
        # In order to make it coincide with the other possible output.
        # This is ok since it is Id
        Add( slp, [ [p_signpos,-1] , p_signpos ] );
        return [ slp, [ stdgens[1]^0, mat ] ];
    fi;
    
    Add(slp, [[2,1,1,1], upos]);
    Add(slp, [[2,1,1,1], spos]);

    c := CycleFromPermutation(perm);
    u1 := One(SymmetricGroup(n));
    u2 := One(SymmetricGroup(n));
    result := [];
    result2 := [];
    m := n/2;
    L2 := IdentityMat(n,fld);
    R2 := IdentityMat(n,fld);
    w := PrimitiveElement(fld);
    v := PermutationMonomialMatrix(stdgens[8])[2];
    # set alpha in SU
    while (CheckContinue(perm,m)) do
        c := CycleFromPermutation(perm);
        list := [1..n];
        for i in [1..n] do
            list[i] := false;
        od;
        mb := false;
        for j in Reversed([m+1..n]) do
            i := FindCorrectCycel(c,j);
            if i <> () then
                k := LargestMovedPoint(i);
                if j = m+1 then
                    perm := v*perm;
                    u1 := v*u1;
                    L2 := stdgens[8]*L2;
                    Add( slp, [ [8,1,left,1] , left ] );
                    mb := true;
                else
                    if k <= m then
                        
                    elif SmallestMovedPoint(i) > m then
                        for nu in Orbit(GroupByGenerators([i]),j) do
                            list[nu] := true;
                        od;
                    elif (n-k+1)^i = n-k+1 then
                        for nu in [1..(n/2)-(n-j+1)] do
                            if TestPermutationProd2(c, CycleFromPermutation(perm^(k,n-k+1)(k-nu,n-k+1+nu)), n-k+1, list, n) then
                                # Dieser Case wird manchmal ausgeführt.
                                tmpvalue := L2[k];
                                L2[k] := L2[n-k+1];
                                L2[n-k+1] := tmpvalue;
                                tmpvalue := R2{[1..n]}[k];
                                R2{[1..n]}[k] := R2{[1..n]}[n-k+1];
                                R2{[1..n]}[n-k+1] := tmpvalue;
                                
                                tmpvalue := L2[k-nu];
                                L2[k-nu] := L2[n-k+1+nu];
                                L2[n-k+1+nu] := tmpvalue;
                                tmpvalue := R2{[1..n]}[k-nu];
                                R2{[1..n]}[k-nu] := R2{[1..n]}[n-k+1+nu];
                                R2{[1..n]}[n-k+1+nu] := tmpvalue;
                                
                                perm := perm^(k,n-k+1)(k-nu,n-k+1+nu);
                                u1 := (k,n-k+1)(k-nu,n-k+1+nu) * u1;
                                u2 := u2 * (k,n-k+1)(k-nu,n-k+1+nu);
                                
                                Add( slp, [ [vpos,(n-k),spos,1,vpos,-(n-k)] , tpos ] );
                                for slpnu in [1..nu-1] do
                                    Add( slp, [ [vpos,(n-k+slpnu),2,1,vpos,-(n-k+slpnu)], upos] );
                                    # Maybe we can change the previous line into Add( slp, [ [vpos,1,upos,1,vpos,-1], upos] ); such that we don't get high numbers by the conjugation. Test that!
                                    Add( slp, [ [upos,-1,tpos,1,upos,1] , tpos ] );
                                od;
                                Add( slp, [ [tpos,1,left,1] , left ] );
                                Add( slp, [ [right,1,tpos,1] , right] );
                                
                                mb := true;
                                break;
                                
                            elif perm^(k,n-k+1)(k-nu,n-k+1+nu) = perm then
                                # Dieser Case wird manchmal ausgeführt.
                                tmpvalue := L2[k];
                                L2[k] := L2[n-k+1];
                                L2[n-k+1] := tmpvalue;
                                tmpvalue := L2[k-nu];
                                L2[k-nu] := L2[n-k+1+nu];
                                L2[n-k+1+nu] := tmpvalue;
                            
                                perm := (k,n-k+1)(k-nu,n-k+1+nu) * perm;
                                u1 := (k,n-k+1)(k-nu,n-k+1+nu) * u1;
                                
                                Add( slp, [ [vpos,(n-k),spos,1,vpos,-(n-k)] , tpos ] );
                                for slpnu in [1..nu-1] do
                                    Add( slp, [ [vpos,(n-k+slpnu),2,1,vpos,-(n-k+slpnu)], upos] );
                                    # Maybe we can change the previous line into Add( slp, [ [vpos,1,upos,1,vpos,-1], upos] ); such that we don't get high numbers by the conjugation. Test that!
                                    Add( slp, [ [upos,-1,tpos,1,upos,1] , tpos ] );
                                od;
                                Add( slp, [ [tpos,-1,left,1] , left ] );
                                
                                mb := true;
                                break;
                            fi;
                        od;
                        for nu in [1..(n/2)-(n-j+1)] do
                            if TestPermutationProd2(c, CycleFromPermutation((k,n-k+1)(k-nu,n-k+1+nu)*perm), n-k+1, list, n) then
                                tmpvalue := L2[k];
                                L2[k] := L2[n-k+1];
                                L2[n-k+1] := tmpvalue;
                                tmpvalue := L2[k-nu];
                                L2[k-nu] := L2[n-k+1+nu];
                                L2[n-k+1+nu] := tmpvalue;
                            
                                perm := (k,n-k+1)(k-nu,n-k+1+nu) * perm;
                                u1 := (k,n-k+1)(k-nu,n-k+1+nu) * u1;
                                
                                Add( slp, [ [vpos,(n-k),spos,1,vpos,-(n-k)] , tpos ] );
                                for slpnu in [1..nu-1] do
                                    Add( slp, [ [vpos,(n-k+slpnu),2,1,vpos,-(n-k+slpnu)], upos] );
                                    # Maybe we can change the previous line into Add( slp, [ [vpos,1,upos,1,vpos,-1], upos] ); such that we don't get high numbers by the conjugation. Test that!
                                    Add( slp, [ [upos,-1,tpos,1,upos,1] , tpos ] );
                                od;
                                Add( slp, [ [tpos,-1,left,1] , left ] );
                                
                                mb := true;
                                break;
                            fi;
                        od;
                        if mb = false then
                            for nu in Orbit(GroupByGenerators([i]),j) do
                                list[nu] := true;
                            od;
                        fi;
                    else
                        for nu in [1..(n/2)-(n-j+1)] do
                            if ((n-k+1)^(FindCorrectCycel(CycleFromPermutation((k,n-k+1)(k-nu,n-k+1+nu)*perm),j)) = (n-k+1)) and TestPermutationProd(c, CycleFromPermutation((k,n-k+1)(k-nu,n-k+1+nu)*perm), list, n) then
                                # Dieser Case wird manchmal ausgeführt
                            
                                tmpvalue := L2[k];
                                L2[k] := L2[n-k+1];
                                L2[n-k+1] := tmpvalue;
                                tmpvalue := L2[k-nu];
                                L2[k-nu] := L2[n-k+1+nu];
                                L2[n-k+1+nu] := tmpvalue;
                                
                                perm := (k,n-k+1)(k-nu,n-k+1+nu)*perm;
                                u1 := (k,n-k+1)(k-nu,n-k+1+nu) * u1;
                                
                                Add( slp, [ [vpos,(n-k),spos,1,vpos,-(n-k)] , tpos ] );
                                for slpnu in [1..nu-1] do
                                    Add( slp, [ [vpos,(n-k+slpnu),2,1,vpos,-(n-k+slpnu)], upos] );
                                    # Maybe we can change the previous line into Add( slp, [ [vpos,1,upos,1,vpos,-1], upos] ); such that we don't get high numbers by the conjugation. Test that!!!!!
                                    Add( slp, [ [upos,-1,tpos,1,upos,1] , tpos ] );
                                od;
                                Add( slp, [ [tpos,-1,left,1] , left ] );
                                
                                mb := true;
                                break;
                            fi;
                        od;
                    fi;
                fi;
                if mb then
                    break;
                fi;
            else
                list[j] := true;
            fi;
        od;
    od;
    
    Add(slp, [[2,1], upos]);
        
    ################
    # Some Tests

    #if PermutationMonomialMatrix(L2)[2] <> u1 then
    #    Error("L2");
    #fi;
    #if PermutationMonomialMatrix(R2)[2] <> u2 then
    #    Error("R2");
    #fi;
    
    #Add( slp, [ [left,1,p_signpos,1,right,1] , p_signpos ] );
    #Add( slp, [ right ,1 ] );
    #slp := MakeSLP(slp,9);
    #if PermutationMonomialMatrix(ResultOfStraightLineProgram(slp,stdgens))[2] <> u2 then
    #    Error("Here");
    #fi;
    
    #Error("Here");
    
    #return slp;
    #return MakeSLP(slp,9);
    
    # return [perm,u1,u2];
    
    #Print(nu);
    #Print(n-k+nu-1);
    #if k = 8 then
    #Display((k,n-k+1)(k-nu,n-k+1+nu));
    #Add( slp, [ tpos ,1 ] );
    #return MakeSLP(slp,9);
    #fi;
    
    ################
    
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

    v := (CycleFromPermutation(PermutationMonomialMatrix(stdgens[8])[2])[1])^(-1);
    Ev := MonomialMatrixToEasyForm(stdgens[8]^(-1));
    vf := (CycleFromPermutation(PermutationMonomialMatrix(stdgens[8])[2])[1])^(-1);
    Evf := MonomialMatrixToEasyForm(stdgens[8]^(-1));
    EvfMinus := MonomialMatrixToEasyForm(stdgens[8]);
    s := CycleFromPermutation(PermutationMonomialMatrix(stdgens[2])[2])[1];
    Es := MonomialMatrixToEasyForm(stdgens[2]);

    Add( slp, [ [8,1], vpos ] );
    Add( slp, [ [8,-1], vipos ] );
    Add( slp, [ [2,1], spos ] );

    perm3 := perm;
    tmpvalue := MonomialMatrixToEasyForm(IdentityMat(n,fld));

    for i in [ 1 .. m-1 ] do

        pot := i^perm - i;

        # Need to update perm since pi_{i-1} may change pos of i
        perm   :=   perm   *  v ^pot;
        for j in [1..pot] do
            tmpvalue := MultiplicationOfEasyForm(tmpvalue,Ev);
        od;

        # memory slots 19 and 20 are used for resAEM and tmpAEM
        instr := AEM( vipos, 19, 20, pot );
        Append( slp, instr );
        Add( slp, [ [p_signpos, 1, 19, 1], p_signpos ] ); # permpos

        #Compute v_i+1, save command in slp
        v  :=    s    *  v;
        Ev := MultiplicationOfEasyForm(Es,Ev);

        Add(slp,[ [spos,1, vipos,1 ], vipos ] ); # vipos
        # Don't be confused with notation in Paper
        # There we used v1 (which coincides with v^-1)

        s  :=   s ^(  vf ^-1 );
        Es := MultiplicationOfEasyForm(MultiplicationOfEasyForm(Evf,Es),EvfMinus);
        Add(slp, [ [17, 1, spos, 1, 8, 1], spos ] ); # spos


    od;

    Add(slp,[ [ p_signpos,-1 ], p_signpos ] );
    Add( slp, [ [left,1,p_signpos,1,right,1] , p_signpos ] );
    Add( slp, [ p_signpos ,1 ] );
    
    tmpvalue := EasyFormToMonomialMatrix(tmpvalue,n,fld);
    tmpvalue := R2*tmpvalue*L2;
    mat := tmpvalue*mat;

    return [slp, [tmpvalue , mat ] ];
    
end
);



#####
# MonomialSLPSOCircle
#####

InstallGlobalFunction(  MonomialSLPSOCircle,
function( arg )
    local slp, c, n, m, result, i, k, u1, u2, result2, test, g, stdgens, mat, perm, fld, p_signpos, vpos, vipos, spos, upos, unpos, tpos, left, right, cnt, v, vf, s, pot, p_signwr, instr, swr, vwr, viwr, p_sign, leftma, rightma, L, R, diag, w, alpha, tmpvalue, rowlist, L2, R2, tmpSave, perm2, perm3, q, Ev, Evf, EvfMinus, Es, j, vTest, vfTest, sTest, resTest;

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

        # Info( InfoBruhat, 2, " and additional:  ",7," memory slots ", "in PermSLP()\n");
        
    else

        # we write an SLP into the variable slp
        # The first 14 entries are the stdgens and the inverses
        # s, t, del, v, x, s^-1, t^-1, del^-1, v^-1, x^-1
        # The entries 11 (resAEM) and 12 (tmpAEM) are used to save AEM-values
        slp := [    [1, 1], [2, 1], [3, 1], [4, 1], [5, 1], [6, 1],
                    [1,-1], [2,-1], [3,-1], [4,-1], [5,-1], [6,-1],
                    [1, 0], [1, 0]    ];

        cnt := 14;

        # Info( InfoBruhat, 2, "Memory Usage is: ",14,"  memory slots ", "in PermSLP()\n");
        
    fi;

    # Initialize the additional memory quota
    Add(slp, [ [1,0], cnt + 1 ] );    p_signpos := cnt + 1;    #13 or 20+3f
    Add(slp, [ [5,-1], cnt + 2 ] );    vpos      := cnt + 2;    #14 or 21+3f
    Add(slp, [ [5,-1], cnt + 3 ] );    vipos     := cnt + 3;    #15 or 22+3f
    Add(slp, [ [1,1], cnt + 4 ] );    spos      := cnt + 4;    #16 or 23+3f
    Add(slp, [ [4,1], cnt + 5 ] );    upos      := cnt + 5;    #17 or 24+3f
    Add(slp, [ [4,0], cnt + 6 ] );    unpos     := cnt + 6;    #18 or 25+3f
    Add(slp, [ [1,0], cnt + 7 ] );    tpos      := cnt + 7;    #19 or 26+3f
    Add(slp, [ [1,0], cnt + 8 ] );    left      := cnt + 8;    #20 or 27+3f
    Add(slp, [ [1,0], cnt + 9 ] );    right     := cnt + 9;    #21 or 28+3f

    if IsDiagonalMat( mat ) then
        # In order to make it coincide with the other possible output.
        # This is ok since it is Id
        # Add( slp, [ [p_signpos,-1] , p_signpos ] );
        Add( slp, [ p_signpos ,1 ] );
        return [ slp, [ stdgens[1]^0, mat ] ];
    fi;

    c := CycleFromPermutation(perm);
    u1 := One(SymmetricGroup(n));
    u2 := One(SymmetricGroup(n));
    result := [];
    result2 := [];
    L2 := IdentityMat(n,fld);
    R2 := IdentityMat(n,fld);
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
                L2[n-k+1] := tmpvalue;
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

    v := (CycleFromPermutation(PermutationMonomialMatrix(stdgens[5])[2])[1])^(-1);
    Ev := MonomialMatrixToEasyForm(stdgens[5]^(-1));
    vf := (CycleFromPermutation(PermutationMonomialMatrix(stdgens[5])[2])[1])^(-1);
    Evf := MonomialMatrixToEasyForm(stdgens[5]^(-1));
    EvfMinus := MonomialMatrixToEasyForm(stdgens[5]);
    s := CycleFromPermutation(PermutationMonomialMatrix(stdgens[4])[2])[1];
    Es := MonomialMatrixToEasyForm(stdgens[4]);

    Add( slp, [ [5,1], vpos ] );
    Add( slp, [ [5,-1], vipos ] );
    Add( slp, [ [4,1], spos ] );

    perm3 := perm;
    tmpvalue := MonomialMatrixToEasyForm(IdentityMat(n,fld));

    for i in [ 1 .. m-2 ] do

        pot := i^perm - i;

        # Need to update perm since pi_{i-1} may change pos of i
        perm   :=   perm   *  v^pot;
        for j in [1..pot] do
            tmpvalue := MultiplicationOfEasyForm(tmpvalue,Ev);
        od;

        # memory slots 13 and 14 are used for resAEM and tmpAEM
        instr := AEM( vipos, 13, 14, pot );
        Append( slp, instr );
        Add( slp, [ [p_signpos, 1, 13, 1], p_signpos ] ); # permpos

        #Compute v_i+1, save command in slp
        v  :=    s    *  v;
        Ev := MultiplicationOfEasyForm(Es,Ev);

        Add(slp,[ [spos,1, vipos,1 ], vipos ] ); # vipos
        # Don't be confused with notation in Paper
        # There we used v1 (which coincides with v^-1)

        s  :=   s ^(  vf ^-1 );
        Es := MultiplicationOfEasyForm(MultiplicationOfEasyForm(Evf,Es),EvfMinus);
        Add(slp, [ [11, 1, spos, 1, 5, 1], spos ] ); # spos
    od;

    Add(slp,[ [ p_signpos,-1 ], p_signpos ] );
    Add( slp, [ [left,1,p_signpos,1,right,1] , p_signpos ] );
    Add( slp, [ p_signpos ,1 ] );

    tmpvalue := EasyFormToMonomialMatrix(tmpvalue,n,fld);
    tmpvalue := R2*tmpvalue*L2;
    mat := tmpvalue*mat;
    mat[m][m] := One(fld);

    return [slp, [tmpvalue , mat ] ];

end
);



#####
# MonomialSLPSOMinus
#####

InstallGlobalFunction(  MonomialSLPSOMinus,
function( arg )

    local slp, c, n, m, result, i, k, u1, u2, result2, test, g, stdgens, mat, perm, fld, p_signpos, vpos, vipos, spos, upos, unpos, tpos, left, right, cnt, v, vf, s, pot, p_signwr, instr, p_sign, leftma, rightma, L, R, diag, w, alpha, tmpvalue, rowlist, L2, R2, tmpSave, perm2, perm3, delta, A, B, C, A2, B2, C2, A3, B3, C3, Es, Ev, Evf, EvfMinus, j;

    # Check for correct Input
    if Length(arg) >= 2 and IsList(arg[1]) and IsMatrix(arg[2]) then

        stdgens := arg[1];  # the LGO standard generators
        mat := arg[2];        # the monomial matrix
        n := Length(stdgens[1]);
        m := (n/2)-1;

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

        # Info( InfoBruhat, 2, " and additional:  ",7," memory slots ", "in PermSLP()\n");
        
    else

        # we write an SLP into the variable slp
        # The first 12 entries are the stdgens and the inverses
        # s, t, del, v, x, s^-1, t^-1, del^-1, v^-1, x^-1
        # The entries 13 (resAEM) and 14 (tmpAEM) are used to save AEM-values
        slp := [    [1, 1], [2, 1], [3, 1], [4, 1], [5, 1], [6, 1],
                    [1,-1], [2,-1], [3,-1], [4,-1], [5,-1], [6,-1],
                    [1, 0], [1, 0]    ];

        cnt := 14;

        # Info( InfoBruhat, 2, "Memory Usage is: ",19,"  memory slots ", "in PermSLP()\n");
        
    fi;

    # Initialize the additional memory quota
    Add(slp, [ [1,0], cnt + 1 ] );    p_signpos := cnt + 1;    #13 or 20+3f
    Add(slp, [ [5,-1], cnt + 2 ] );    vpos      := cnt + 2;    #14 or 21+3f
    Add(slp, [ [5,-1], cnt + 3 ] );    vipos     := cnt + 3;    #15 or 22+3f
    Add(slp, [ [1,1], cnt + 4 ] );    spos      := cnt + 4;    #16 or 23+3f
    Add(slp, [ [4,1], cnt + 5 ] );    upos      := cnt + 5;    #17 or 24+3f
    Add(slp, [ [4,0], cnt + 6 ] );    unpos     := cnt + 6;    #18 or 25+3f
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
    m := (n/2)-1;
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
            elif SmallestMovedPoint(i) > m+2 then
            
            elif SmallestMovedPoint(i) in [m+1,m+2] then

            elif (n-k+1)^i = n-k+1 then
                tmpvalue := L2[k];
                L2[k] := L2[n-k+1];
                L2[n/2] := -1*L2[n/2];
                L2[n-k+1] := tmpvalue;
                tmpvalue := R2{[1..n]}[k];
                R2{[1..n]}[k] := R2{[1..n]}[n-k+1];
                R2{[1..n]}[n/2] := -1*R2{[1..n]}[n/2];
                R2{[1..n]}[n-k+1] := tmpvalue;
                perm := perm^(k,n-k+1);
                u1 := (k,n-k+1) * u1;
                Add( slp, [ [vpos,(n-k),spos,1,vpos,-(n-k)] , tpos ] );
                Add( slp, [ [tpos,1,left,1] , left ] );
                Add( slp, [ [right,1,tpos,1] , right] );
                u2 := u2 * (k,n-k+1);
                break;
            else
                tmpvalue := L2[k];
                L2[k] := L2[n-k+1];
                L2[n/2] := -1*L2[n/2];
                L2[n-k+1] := tmpvalue;
                perm := (k,n-k+1)*perm;
                u1 := (k,n-k+1) * u1;
                Add( slp, [ [vpos,(n-k),spos,1,vpos,-(n-k)] , tpos ] );
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
        elif SmallestMovedPoint(i) > m+2 then
            Add(result2, i);
        fi;
    od;

    result := Set(result);
    result2 := Set(result2);

    Add( slp, [ [left,-1] , left ] );
    Add( slp, [ [right,-1] , right ] );
    
        #Add( slp, [ [left,1,p_signpos,1,right,1] , p_signpos ] );
        #Display(u1);
        #Display(u2);
        #Display(perm);
        #Add( slp, [ right ,1 ] );
        
        #test := slp;
        #Add(test, [[left,1],p_signpos]);
        #test := MakeSLP(test,6);
        #if (ResultOfStraightLineProgram(test,stdgens) <> L2) then
        #    Error("u1");
        #fi;
        
        #test := slp;
        #Add(test, [[right,1],p_signpos]);
        #test := MakeSLP(test,6);
        #if (ResultOfStraightLineProgram(test,stdgens) <> R2) then
        #    Error("u2");
        #fi;
        
        #Error("Here");
        #return MakeSLP(slp,6);
        

    perm := One(SymmetricGroup(n));
    for i in [1..Size(result)] do
        perm := perm * result[i];
    od;

    perm2 := One(SymmetricGroup(n));
    for i in [1..Size(result2)] do
        perm2 := perm2 * result2[i];
    od;

    v := (CycleFromPermutation(PermutationMonomialMatrix(stdgens[5])[2])[1])^(-1);
    Ev := MonomialMatrixToEasyForm(stdgens[5]^(-1));
    vf := (CycleFromPermutation(PermutationMonomialMatrix(stdgens[5])[2])[1])^(-1);
    Evf := MonomialMatrixToEasyForm(stdgens[5]^(-1));
    EvfMinus := MonomialMatrixToEasyForm(stdgens[5]);
    s := CycleFromPermutation(PermutationMonomialMatrix(stdgens[4])[2])[1];
    Es := MonomialMatrixToEasyForm(stdgens[4]);

    Add( slp, [ [5,1], vpos ] );
    Add( slp, [ [5,-1], vipos ] );
    Add( slp, [ [4,1], spos ] );

    perm3 := perm;
    tmpvalue := MonomialMatrixToEasyForm(IdentityMat(n,fld));

    for i in [ 1 .. m-1 ] do

        pot := i^perm - i;

        # Need to update perm since pi_{i-1} may change pos of i
        perm   :=   perm   *  v ^pot;
        for j in [1..pot] do
            tmpvalue := MultiplicationOfEasyForm(tmpvalue,Ev);
        od;

        # memory slots 13 and 14 are used for resAEM and tmpAEM
        instr := AEM( vipos, 13, 14, pot );
        Append( slp, instr );
        Add( slp, [ [p_signpos,1,13,1 ], p_signpos ] ); # permpos

        #Compute v_i+1, save command in slp
        v  :=    s    *  v;
        Ev := MultiplicationOfEasyForm(Es,Ev);

        Add(slp,[ [spos,1, vipos,1 ], vipos ] ); # vipos
        # Don't be confused with notation in Paper
        # There we used v1 (which coincides with v^-1)

        s  :=   s ^(  vf ^-1 );
        Es := MultiplicationOfEasyForm(MultiplicationOfEasyForm(Evf,Es),EvfMinus);
        Add(slp, [ [11, 1, spos,1, 5,1 ], spos ] ); # spos


    od;

    Add(slp,[ [ p_signpos,-1 ], p_signpos ] );
    Add( slp, [ [left,1,p_signpos,1,right,1] , p_signpos ] );

    #tmpvalue := PermutationMat(perm2^(-1),n, fld);
    #tmpvalue{[1..n/2]}{[1..n/2]} := PermutationMat(perm3^(-1),n/2, fld);
    
    #tmpvalue :=R2*tmpvalue*L2;
    #mat := tmpvalue*mat;
    #Display(mat);
    
    tmpvalue := EasyFormToMonomialMatrix(tmpvalue,n,fld);
    tmpvalue := R2*tmpvalue*L2;
    mat := tmpvalue*mat;
    
    #test := slp;
    #Add(test, [[p_signpos,1],p_signpos]);
    #test := MakeSLP(test,6);
    #if (ResultOfStraightLineProgram(test,stdgens)^(-1) <> tmpvalue) then
    #    Error("before middle");
    #fi;
    #Display("Before Middle correct");
    #Display(ResultOfStraightLineProgram(test,stdgens)^(-1));
    #Print("---\n");
    #Display(tmpvalue);
    
    # The permutation is now (m+1,m+2)
    # Need a better way to find this. This is still unbelievable slow!
    #if not(IsDiagonalMat(mat)) then
    #    delta := stdgens[3];
    #    for i in [1..Size(fld)] do
    #        if IsMonomialMatrix(delta) and PermutationMonomialMatrix(delta)[2] = (m+1,m+2) then
    #            mat := delta*mat;
    #            Add( slp, [[ 3 ,i, p_signpos,1], p_signpos ] );
    #            tmpvalue := delta*tmpvalue;
    #            break;
    #        fi;
    #        delta := delta*stdgens[3];
    #    od;
    #fi;
    
    # This is still not fast enough. Is there a better way to find the monomial matrix (m+1,m+2) in SOMinus ??
    # This is independent from the matrix size but needs more time for a larger field.
    if (mat[n/2][(n/2)+1] <> Zero(fld)) then
        k := 1;
        delta := stdgens[3];
        A := delta[m+1][m+1];
        B := delta[m+1][m+2];
        C := delta[m+2][m+1];
        A2 := A;
        B2 := B;
        C2 := C;
        while true do
            if (A*mat[m+1][m+2]+B*mat[m+2][m+2] = Zero(fld)) then
                #g := delta^k*g;
                delta := MutableCopyMat(delta);
                delta[1,1] := delta[1,1]^k;
                delta[n,n] := delta[n,n]^k;
                delta[m+1][m+1] := A;
                delta[m+1][m+2] := B;
                delta[m+2][m+1] := C;
                delta[m+2][m+2] := A;
                mat := delta*mat;
                tmpvalue := delta*tmpvalue;
                Add( slp, [[p_signpos,1,3,-k], p_signpos ] );
                
                #test := slp;
                #Add(test, [[p_signpos,1],p_signpos]);
                #test := MakeSLP(test,6);
                #if (ResultOfStraightLineProgram(test,stdgens)^(-1) <> tmpvalue) then
                #    Error("middle");
                #fi;
                
                break;
            fi;
            k := k+1;
            A3 := A*A2+B*C2;
            B3 := A*B2+A2*B;
            C3 := A*C2+A2*C;
            A := A3;
            B := B3;
            C := C3;
        od;
    fi;
    
    Add( slp, [ p_signpos ,1 ] );

    return [slp, [ tmpvalue, mat ] ];

end
);



#####
# FindCorrectCycel
#####

InstallGlobalFunction(  FindCorrectCycel,
function(perm, j)
    local i;
    
    for i in perm do
        if j^i <> j then
            return i;
        fi;
    od;
    
    return ();
    
end
);



#####
# TestPermutationProd
#####

InstallGlobalFunction(  TestPermutationProd,
function(op, np, l, n)
    local i;

    for i in [(n/2)+1..n] do
        if l[i] then
            if FindCorrectCycel(op,i) <> FindCorrectCycel(np,i) then
                return false;
            fi;
        fi;
    od;
    
    return true;
    
end
);



#####
# TestPermutationProd2
#####

InstallGlobalFunction(  TestPermutationProd2,
function(op, np, tn, l, n)
    local gno, gnn, oc, nc, i, ii;
    
    oc := FindCorrectCycel(op,tn);
    nc := FindCorrectCycel(np,tn);
    
    gno := 0;
    gnn := 0;

    for i in [1..(n/2)] do
        if i^oc <> i then
            gno := gno + 1;
        fi;
        if i^nc <> i then
            gnn := gnn + 1;
        fi;
    od;
    
    if gnn/Order(nc) > gno/Order(oc) then
        for i in [(n/2)+1..n] do
            if l[i] then
                gno := 0;
                gnn := 0;
                oc := FindCorrectCycel(op,n-i+1);
                nc := FindCorrectCycel(np,n-i+1);
                if nc = () then
                
                else
                    for ii in [1..(n/2)] do
                        if ii^oc <> ii then
                            gno := gno + 1;
                        fi;
                        if ii^nc <> ii then
                            gnn := gnn + 1;
                        fi;
                    od;
                    if gnn/Order(nc) < gno/Order(oc) then
                        return false;
                    fi;
                fi;
            fi;
        od;
        return true;
    else
        return false;
    fi;
    
end
);



#####
# MonomialMatrixToEasyForm
#####

InstallGlobalFunction(  MonomialMatrixToEasyForm,
function (M)
    local list, perm, i, j, n, fld;
    
    n := Length(M);
    fld := FieldOfMatrixList( [M] );
    list := [];
    
    for i in [1..n] do
        for j in [1..n] do
            if M[j][i] <> Zero(fld) then
                Add(list,M[j][i]);
                break;
            fi;
        od;
    od;
    
    perm := PermutationMonomialMatrix( M )[2];
    
    return [list,perm];
    
end
);



#####
# EasyFormToMonomialMatrix
#####

InstallGlobalFunction(  EasyFormToMonomialMatrix,
function( tupel, n, fld )
    local M, i, j;
    
    M := PermutationMat(tupel[2],n,fld);
    for i in [1..n] do
        for j in [1..n] do
            if M[j][i] <> Zero(fld) then
                M[j][i] := tupel[1][i];
            fi;
        od;
    od;
    
    return M;
end
);



#####
# MultiplicationOfEasyForm
#####

InstallGlobalFunction(  MultiplicationOfEasyForm,
function ( tupel1, tupel2)
    local perm1, perm2, list1, list2, perm, list, i;
    
    list1 := tupel1[1];
    perm1 := tupel1[2];
    list2 := tupel2[1];
    perm2 := tupel2[2];
    
    perm := perm1*perm2;
    list := ShallowCopy(list1);
    
    for i in [1..Length(list1)] do
        list[i^(perm2)] := list1[i] * list2[i^(perm2)];
    od;
    
    return [list,perm];

end
);



#####
# DiagSLPSOPlus
#####

InstallGlobalFunction(  DiagSLPSOPlus,
function( arg )

    local stdgens, diag, fld, slp, a_i, d, omega, delta, u, v, cnt, hiposm, hipos, respos, hres, instr, i, decomp, y, x, startpower;

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

        cnt := arg[4]; # <--- Laesst sich das umgehen? Jeweils den hoechsten Slot mitzaehlen?
        # Info( InfoBruhat, 2, " and additional:  ",3," memory slots ", "in DiagonalDecomposition()\n");

    else
        # We write an SLP into the variable slp
        # The first 10 entries are the stdgens and their inverses
        # s^-1 t^-1  del^-1    v^-1    x^-1
        # The entries #13 (resAEM),#14 (tmpAEM) are used to save AEM-values
        slp := [    [1, 1], [2, 1], [3, 1], [4, 1], [5, 1], [6, 1], [7, 1], [8, 1], [9, 1],
                    [1,-1], [2,-1], [3,-1], [4,-1], [5,-1], [6,-1], [7,-1], [8,-1], [9,-1],
                    [1, 0], [1, 0]    ];

        cnt := 20;
        # Info( InfoBruhat, 2, "Memory Usage is: ",3," memory slots ", "in DiagonalDecomposition()\n");
    fi;

    # Initialize the additional memory quota
    #hi-2
    Add(slp, [ [1,0], cnt + 1 ] );    hiposm := cnt + 1;     #15 or 27+3f
    #hi-1
    Add(slp, [ [1,0], cnt + 2 ] );    hipos := cnt + 2;     #16 or 28+3f
    # result
    Add(slp, [ [1,0], cnt + 3 ] );    respos := cnt + 3;     #17 or 29+3f

    # Needed elements for calculations
    d := Length( diag );
    omega := (stdgens[5])[1][1];
    delta := IdentityMat(d,GF(Size(fld)));
    delta[1][1] := omega;
    delta[d][d] := omega^(-1);

    # Easy case
    if diag = One(diag) then
        Add( slp, [ [1,0], respos ] );
        Add( slp, [ respos, 1]);
        return [ slp];
    fi;

    # Find start element
    decomp := FindPrimePowerDecomposition(Size(fld));
    y := decomp[1];
    x := decomp[2];
    
    #for i in [0..(Size(fld)-1)] do
    #    if ((2*i+x-1) mod (Size(fld)-1)) = 0 then
    #        startpower := i;
    #        break;
    #    fi;
    #od;
    
    startpower := (Size(fld)-x)/2;
    
    instr := AEM( 5, 19, 20, startpower );
    Append( slp, instr );
    Add(slp, [[19,1,9,1], hipos]);
    instr := AEM( 6, 19, 20, startpower );
    Append( slp, instr );
    Add(slp, [[19,1,hipos,1], hipos]);
    Add(slp, [[8,1], hiposm]);

    for i in [ 1..(d/2) ] do

        a_i := LogFFE( diag[i][i], omega );
        # The memory slots 13 and 14 are res and tmp-slot for AEM
        instr := AEM( hipos, 19, 20, a_i );
        Append( slp, instr );
        Add( slp, [ [respos, 1, 19, 1 ], respos ] );
        Add( slp, [ [hiposm, -1 , hipos, 1, hiposm,1 ], hipos ] );

    od;

    Add( slp, [ respos ,1 ] );

    return [slp];

end
);



#####
# DiagSLPSOCircle
#####

InstallGlobalFunction(  DiagSLPSOCircle,
function(arg)
    local stdgens, diag, fld, slp, a_i, d, omega, cnt, hiposm, hipos, respos, hres, instr, i, q, decomp, y, x, startpower;

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

        cnt := HighestSlotOfSLP( slp );  # <--- Laesst sich das umgehen? Jeweils den hoechsten Slot mitzaehlen?
        #cnt := arg[4]; # <--- Laesst sich das umgehen? Jeweils den hoechsten Slot mitzaehlen?
        #Info( InfoBruhat, 2, " and additional:  ",3," memory slots ", "in DiagonalDecomposition()\n");

    else
        # We write an SLP into the variable slp
        # The first 14 entries are the stdgens and their inverses
        # s^-1 t^-1  del^-1    v^-1    x^-1
        # The entries #15 (resAEM),#16 (tmpAEM) are used to save AEM-values
        slp := [    [1, 1], [2, 1], [3, 1], [4, 1], [5, 1], [6, 1],
                    [1,-1], [2,-1], [3,-1], [4,-1], [5,-1], [6,-1],
                    [1, 0], [1, 0] ];

        cnt := 14;
        #Info( InfoBruhat, 2, "Memory Usage is: ",3," memory slots ", "in DiagonalDecomposition()\n");
    fi;

    # Initialize the additional memory quota
    #hi-2
    Add(slp, [ [1,0], cnt + 1 ] );    hipos := cnt + 1;     #17 or 28+3f
    # result
    Add(slp, [ [1,0], cnt + 2 ] );    respos := cnt + 2;     #18 or 29+3f

    d := Length( diag );
    omega := PrimitiveElement(GF(Size(fld)));

    # Easy case
    if diag = One(diag) then
        Add( slp, [ [1,0], respos ] );
        Add( slp, [ respos, 1]);
        return [slp];
    fi;

    # Find start element
    decomp := FindPrimePowerDecomposition(Size(fld));
    y := decomp[1];
    x := decomp[2];
    
    #for i in [0..(Size(fld)-1)] do
    #    if ((2*i+x-1) mod (Size(fld)-1)) = 0 then
    #        startpower := i;
    #        break;
    #    fi;
    #od;
    
    startpower := (Size(fld)-x)/2;
    
    instr := AEM( 3, 13, 14, startpower );
    Append( slp, instr );
    Add(slp, [[13,1,6,1], hipos]);
    
    for i in [ 1..((d-1)/2) ] do

        a_i := LogFFE( diag[i][i], omega );

        # The memory slots 15 and 16 are res and tmp-slot for AEM
        instr := AEM( hipos, 13, 14, a_i );
        Append( slp, instr );
        Add( slp, [ [respos, 1, 13, 1 ], respos ] );
        Add( slp, [ [5, -1 , hipos, 1, 5,1 ], hipos ] );

    od;

    Add( slp, [ respos ,1 ] );

    return [slp];

end
);



#####
# DiagSLPSOMinus
#####

InstallGlobalFunction(  DiagSLPSOMinus,
function( arg )

    local stdgens, diag, fld, slp, a_i, d, omega, delta, u, v, cnt, hiposm, hipos, respos, hres, instr, i, decomp, y, x, startpower, tmpv;

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

        cnt := arg[4]; # <--- Laesst sich das umgehen? Jeweils den hoechsten Slot mitzaehlen?
        # Info( InfoBruhat, 2, " and additional:  ",3," memory slots ", "in DiagonalDecomposition()\n");

    else
        # We write an SLP into the variable slp
        # The first 10 entries are the stdgens and their inverses
        # s^-1 t^-1  del^-1    v^-1    x^-1
        # The entries #13 (resAEM),#14 (tmpAEM) are used to save AEM-values
        slp := [    [1, 1], [2, 1], [3, 1], [4, 1], [5, 1], [6, 1],
                    [1,-1], [2,-1], [3,-1], [4,-1], [5,-1], [6,-1],
                    [1, 0], [1, 0]    ];

        cnt := 14;
        # Info( InfoBruhat, 2, "Memory Usage is: ",3," memory slots ", "in DiagonalDecomposition()\n");
    fi;

    # Initialize the additional memory quota
    #hi-2
    Add(slp, [ [1,0], cnt + 1 ] );    hiposm := cnt + 1;     #15 or 27+3f
    #hi-1
    Add(slp, [ [1,0], cnt + 2 ] );    hipos := cnt + 2;     #16 or 28+3f
    # result
    Add(slp, [ [1,0], cnt + 3 ] );    respos := cnt + 3;     #17 or 29+3f

    # Needed elements for calculations
    d := Length( diag );
    omega := (stdgens[3])[1][1];

    # Easy case
    if diag = One(diag) then
        Add( slp, [ [1,0], respos ] );
        Add( slp, [ respos, 1]);
        return [ slp];
    fi;
    
    if (Size(fld)= 3) then
        Add(slp, [[6,1], hipos]);
        Add(slp, [[5,1], hiposm]);
        
        for i in [ 1..(d/2)-1 ] do

            a_i := LogFFE( diag[i][i], omega );
            # The memory slots 13 and 14 are res and tmp-slot for AEM
            instr := AEM( hipos, 13, 14, a_i );
            Append( slp, instr );
            Add( slp, [ [respos, 1, 13, 1 ], respos ] );
            Add( slp, [ [hiposm, -1 , hipos, 1, hiposm,1 ], hipos ] );

        od;
        
        if diag[d/2][d/2] <> One(fld) then
            Add( slp, [ [3, 2, respos, 1 ], respos ] );
        fi;
    
    else
        if diag[d/2][d/2] <> One(fld) then
            instr := AEM( 3, 13, 14, (Size(fld)+1)/2 );
            Append( slp, instr );
            Add(slp, [[13,1], hipos]);
            Add(slp, [[13,1], respos]);
            tmpv := ((stdgens[3])[1][1])^((Size(fld)+1)/2);
            instr := AEM( hipos, 13, 14, (Size(fld)+1)/2 );
            Append( slp, instr );
            Add(slp, [[13,1], hipos]);
            Add(slp, [[hipos,1,6,1], hipos]);
            Add(slp, [[5,1], hiposm]);
            
            a_i := LogFFE( diag[1][1]*tmpv^(-1), omega );
            instr := AEM( hipos, 13, 14, a_i );
            Append( slp, instr );
            Add( slp, [ [respos, 1, 13, 1 ], respos ] );
            Add( slp, [ [hiposm, -1 , hipos, 1, hiposm,1 ], hipos ] );
            
            for i in [ 2..(d/2)-1 ] do

                a_i := LogFFE( diag[i][i], omega );
                # The memory slots 13 and 14 are res and tmp-slot for AEM
                instr := AEM( hipos, 13, 14, a_i );
                Append( slp, instr );
                Add( slp, [ [respos, 1, 13, 1 ], respos ] );
                Add( slp, [ [hiposm, -1 , hipos, 1, hiposm,1 ], hipos ] );

            od;
        
        else
            instr := AEM( 3, 13, 14, ((Size(fld)+1)/2)^2 );
            Append( slp, instr );
            Add(slp, [[13,1], hipos]);
            Add(slp, [[hipos,1,6,1], hipos]);
            Add(slp, [[5,1], hiposm]);
            
            for i in [ 1..(d/2)-1 ] do

                a_i := LogFFE( diag[i][i], omega );
                # The memory slots 13 and 14 are res and tmp-slot for AEM
                instr := AEM( hipos, 13, 14, a_i );
                Append( slp, instr );
                Add( slp, [ [respos, 1, 13, 1 ], respos ] );
                Add( slp, [ [hiposm, -1 , hipos, 1, hiposm,1 ], hipos ] );

            od;
        fi;
    fi;

    Add( slp, [ respos ,1 ] );

    return [slp];

end
);



#####
#   BruhatDecompositionSO
#####

InstallGlobalFunction(  BruhatDecompositionSO,
function(stdgens, g)

    local slp, u1, pm, u2, p_sign, diag, res1, res2, res3, lastline, line, pgr;

    if (Length(g) mod 2) = 0 then
    
        if (g in MSO(1,Length(g),Size(FieldOfMatrixList( stdgens )))) then

            # We write an SLP into the variable slp
            # The first 12 entries are the stdgens and their inverses
            # s, t, del, v, u, x, s^-1, t^-1, del^-1, v^-1, u^-1, x^-1

            #Info( InfoBruhat, 1, "returns an SLP to generate u1, u2, p_sign, diag\n"    );

            # Compute the matrices u1,u2 of Bruhat-Decomposition and the instructions
            # for an SLP that compute u1 and u2
            res1 := UnitriangularDecompositionSOPlus( stdgens, g);

            slp := res1[1];
            u1 := res1[2][2];
            pm := res1[2][1];    # the monomial matrix w
            u2 := res1[2][3];

            lastline := ShallowCopy( slp[ Length(slp) ] ); # remember famous last words
            # Since entries of the form [list1,list2] should only occur at the end
            Remove(slp);

            # Decompose w in to a signed Permutation-Matrix generated by <s,v,x>
            # and a Diagonal-Matrix diag.

            res2 := MonomialSLPSOPlus(stdgens, pm, slp );

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
            res3 := DiagSLPSOPlus(stdgens, diag, slp, res1[3]+10);
            slp := res3[1];

            # Here the last entry is of admissible form. Just add it to the end.
            Append( lastline, [ slp[ Length(slp)] ] ); # remember famous last words
            Remove( slp );
            Append( slp, [lastline] );

            # Info( InfoBruhat, 2, "The Total Memory Usage is: " , res1[3]+9+14, " memory slots\n" );

            pgr := MakeSLP(slp,9);

            # The result R of pgr satisfies:
            #    R[1]^-1*R[3]*R[4]*R[2]^-1    and
            #    R[1] = u1, R[2] = u2, R[3] = p_sign, R[4] = diag
            return [pgr, [ u1, u2, p_sign^(-1), diag ]];
        
        elif (g in MSO(-1,Length(g),Size(FieldOfMatrixList( stdgens )))) then
    
            # We write an SLP into the variable slp
            # The first 12 entries are the stdgens and their inverses
            # s, t, del, v, u, x, s^-1, t^-1, del^-1, v^-1, u^-1, x^-1

            #Info( InfoBruhat, 1, "returns an SLP to generate u1, u2, p_sign, diag\n"    );

            # Compute the matrices u1,u2 of Bruhat-Decomposition and the instructions
            # for an SLP that compute u1 and u2
            res1 := UnitriangularDecompositionSOMinus( stdgens, g);

            slp := res1[1];
            u1 := res1[2][2];
            pm := res1[2][1];    # the monomial matrix w
            u2 := res1[2][3];

            lastline := ShallowCopy( slp[ Length(slp) ] ); # remember famous last words
            # Since entries of the form [list1,list2] should only occur at the end
            Remove(slp);

            # Decompose w in to a signed Permutation-Matrix generated by <s,v,x>
            # and a Diagonal-Matrix diag.

            res2 := MonomialSLPSOMinus(stdgens, pm, slp );

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
            res3 := DiagSLPSOMinus(stdgens, diag, slp, res1[3]+10);
            slp := res3[1];

            # Here the last entry is of admissible form. Just add it to the end.
            Append( lastline, [ slp[ Length(slp)] ] ); # remember famous last words
            Remove( slp );
            Append( slp, [lastline] );

            # Info( InfoBruhat, 2, "The Total Memory Usage is: " , res1[3]+9+14, " memory slots\n" );

            pgr := MakeSLP(slp,6);

            # The result R of pgr satisfies:
            #    R[1]^-1*R[3]*R[4]*R[2]^-1    and
            #    R[1] = u1, R[2] = u2, R[3] = p_sign, R[4] = diag
            return [pgr, [ u1, u2, p_sign^(-1), diag ]];
        
        else
            Print("g is not an element of the orthogonal group. Abort.");
        fi;

    elif (g in MSO(0,Length(g),Size(FieldOfMatrixList( stdgens )))) then

        # We write an SLP into the variable slp
        # The first 12 entries are the stdgens and their inverses
        # s, t, del, v, u, x, s^-1, t^-1, del^-1, v^-1, u^-1, x^-1

        #Info( InfoBruhat, 1, "returns an SLP to generate u1, u2, p_sign, diag\n"    );

        # Compute the matrices u1,u2 of Bruhat-Decomposition and the instructions
        # for an SLP that compute u1 and u2
        res1 := UnitriangularDecompositionSOCircle( stdgens, g);

        slp := res1[1];
        u1 := res1[2][2];
        pm := res1[2][1];    # the monomial matrix w
        u2 := res1[2][3];

        lastline := ShallowCopy( slp[ Length(slp) ] ); # remember famous last words
        # Since entries of the form [list1,list2] should only occur at the end
        Remove(slp);

        # Decompose w in to a signed Permutation-Matrix generated by <s,v,x>
        # and a Diagonal-Matrix diag.

        res2 := MonomialSLPSOCircle(stdgens, pm, slp );

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
        res3 := DiagSLPSOCircle(stdgens, diag, slp);
        slp := res3[1];

        # Here the last entry is of admissible form. Just add it to the end.
        Append( lastline, [ slp[ Length(slp)] ] ); # remember famous last words
        Remove( slp );
        Append( slp, [lastline] );

        # Info( InfoBruhat, 2, "The Total Memory Usage is: " , res1[3]+9+14, " memory slots\n" );
        
        pgr := MakeSLP(slp,6);

        # The result R of pgr satisfies:
        #    R[1]^-1*R[3]*R[4]*R[2]^-1    and
        #    R[1] = u1, R[2] = u2, R[3] = p_sign, R[4] = diag
        return [pgr, [ u1, u2, p_sign^(-1), diag ]];
    
    else
        Print("g is not an element of the orthogonal group. Abort.");
    fi;

end
);



InstallGlobalFunction(  BruhatDecompositionSOMinus,
function(stdgens, g)

    local slp, u1, pm, u2, p_sign, diag, res1, res2, res3, lastline, line, pgr;

    if (Length(g) mod 2) = 0 then
    
        if (g in MSO(-1,Length(g),Size(FieldOfMatrixList( stdgens )))) then
    
            # We write an SLP into the variable slp
            # The first 12 entries are the stdgens and their inverses
            # s, t, del, v, u, x, s^-1, t^-1, del^-1, v^-1, u^-1, x^-1

            #Info( InfoBruhat, 1, "returns an SLP to generate u1, u2, p_sign, diag\n"    );

            # Compute the matrices u1,u2 of Bruhat-Decomposition and the instructions
            # for an SLP that compute u1 and u2
            res1 := UnitriangularDecompositionSOMinus( stdgens, g);

            slp := res1[1];
            u1 := res1[2][2];
            pm := res1[2][1];    # the monomial matrix w
            u2 := res1[2][3];

            lastline := ShallowCopy( slp[ Length(slp) ] ); # remember famous last words
            # Since entries of the form [list1,list2] should only occur at the end
            Remove(slp);

            # Decompose w in to a signed Permutation-Matrix generated by <s,v,x>
            # and a Diagonal-Matrix diag.

            res2 := MonomialSLPSOMinus(stdgens, pm, slp );

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
            res3 := DiagSLPSOMinus(stdgens, diag, slp, res1[3]+10);
            slp := res3[1];

            # Here the last entry is of admissible form. Just add it to the end.
            Append( lastline, [ slp[ Length(slp)] ] ); # remember famous last words
            Remove( slp );
            Append( slp, [lastline] );

            # Info( InfoBruhat, 2, "The Total Memory Usage is: " , res1[3]+9+14, " memory slots\n" );

            pgr := MakeSLP(slp,6);

            # The result R of pgr satisfies:
            #    R[1]^-1*R[3]*R[4]*R[2]^-1    and
            #    R[1] = u1, R[2] = u2, R[3] = p_sign, R[4] = diag
            return [pgr, [ u1, u2, p_sign^(-1), diag ]];
        
        else
            Print("g is not an element of the orthogonal group. Abort.");
        fi;
        
    else
        Print("g is not an element of the orthogonal group. Abort.");
    fi;

end
);

