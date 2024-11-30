# Inspired from Magma Code: GuessAltsymDegree, in magma/package/Group/GrpFin/SimpleRecog/altsym.m
# Returns a guess at alternating or symmetric and degree n
# (It won't work for Sym(3) or Sym(6)!)
#
# This function samples projective orders of elements, and attempts to guess
# degree n and whether it is Alternating or Symmetric.
# Returns a record with entries:
#   - type   : string "Alternating" or "Symmetric"
#   - degree : integer n
# Returns fail if n<=6 or maxtries elements are sampled with
# no decision made.
#
# At least Max(mintries,fac*n*Log(n)) random elements are chosen without
# the answer changing, where mintries, fac can be given as an optional
# arguments.
#
# TODO: Investigate why Alt(9) and Sym(8) return fail
# TODO: Might be inspired from
# "Fast Constructive Recognition of a Black Box Group Isomorphic to Sn or An using Goldbach’s Conjecture"
# by Sergey Bratus and Igor Pak,
# in Chapter 9. "What To Do If n is Not Known?"

RECOG.GuessSnAnDegree := function(ri, optionlist...)
    local G, r, options, mintries, maxtries, fac, mindego, mindege, ct, cto, cte, proc, g, o, mindeg, o_fact, mindegforg;
    # mindego and mindege will be respectively the smallest possible
    # degrees of symmetric groups that contain the elements of odd and
    # even orders, in the random sample.
    # If mindego > mindege we assume the group is alternating, otherwise
    # that it is symmetric.

    G := Grp(ri);
    if  (IsPermGroup(G) and NrMovedPoints(G) <= 6)
                or (IsMatrixGroup(G) and DimensionOfMatrixGroup(G) < 3) then
        Print("GuessAltsymDegree works only for degree > 6\n");
        return fail;
    fi;

    # Set options
    options := rec(
        mintries := 100,
        maxtries := 5000,
        fac := 4
    );

    if Length(optionlist) > 0 then
        for r in RecNames(optionlist[1]) do
            if not IsBound(options.(r)) then
                ErrorNoReturn("Invalid option to GuessSnAnDegree: ", r);
            fi;
            options.(r) := optionlist[1].(r);
        od;
    fi;

    mintries := options.mintries;
    maxtries := options.maxtries;
    fac := options.fac;

    # Init Loop
    mindego := 0;
    mindege := 0;
    cto := 0;
    cte := 0;
    ct := 0;
    mindeg := 0;
    if mintries < 1 then
        mintries := 1;
    fi;

    # Main Loop
    while (ct < Maximum(mintries, fac * mindeg * Int(Ceil(Log(Float(mindeg+1)))))
                or mindego = mindege+1) and ct <= maxtries do
        # The situation mindego = mindege+1 was responsible for most errors
        # in the first version! Alt(n+1) was returned instead of Sym(n).
        g := RandomElm(ri, "GuessSnAnDegree", false)!.el;;
        o := ri!.order(g);
        ct := ct + 1; # counter of loop, as long as no new larger degree was detected
        if o = 1 then
            continue;
        fi;
        o_fact := Collected(Factors(o));
        mindegforg := Sum(o_fact, f -> f[1] ^ f[2]); # minimum degree is sum over all prime-powers in factorization
        if o mod 2 = 0 then
            cte := cte + 1; # counter for even orders
            if mindegforg > mindege then
                mindege := mindegforg;
                if mindege > mindeg then
                    mindeg := mindege;
                fi;
            ct := 0;
            # vprintf IsAltsym: "New E, E = %o, O = %o, elt order = %o, Randoms = %o\n", mindege, mindego, o_fact, cte+cto;
            fi;
        else
            cto := cto + 1; # counter for odd orders
            if mindegforg > mindego then
                mindego := mindegforg;
                if mindego > mindeg then
                    mindeg := mindego;
                fi;
                ct := 0;
            # vprintf IsAltsym: "New O, E = %o, O = %o, elt order = %o, Randoms = %o\n", mindege, mindego, o_fact, cte+cto;
            fi;
        fi;
    od;

    if ct > maxtries then
        # vprintf IsAltsym: "maxtries exceeded - giving up!";
        return fail;
    fi;

    # vprintf IsAltsym: "E = %o, O = %o, Randoms = %o\n", mindege, mindego, cte+cto;

    if mindego > mindege then
        if mindego <= 6 then
            # vprintf IsAltsym: "GuessAltsymDegree works only for degree > 6";
            return fail;
        else
            # vprintf IsAltsym: "Alternating of degree %o\n", mindego;
            return rec(type := "Alternating", degree := mindego);
        fi;
    else
        if mindege <= 6 then
            # vprintf IsAltsym: "GuessAltsymDegree works only for degree > 6";
            return fail;
        else
            # vprintf IsAltsym: "Symmetric of degree %o\n", mindege;
            return rec(type := "Symmetric", degree := mindege);
        fi;
    fi;
end;
