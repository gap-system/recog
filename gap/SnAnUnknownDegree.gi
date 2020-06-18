# Input: Group G, upper error bound eps, upper degree bound N
#
# The following algorithm constructs a set of possible 3-cycles. It is based
# on the simple observation that the product of two involutions t1, t2, which
# only move one common point, squares to a 3-cycle.
#
# Either returns a list of elements of G or NeverApplicable
# TODO: Rewrite this to a kind of iterator function since each candidate is tested one by one
BindGlobal("ThreeCycleCandidates",
function(G, eps, N, groupIsOne, groupIsEq)
    local
        # list, a set of three cycle candidates
        threeCycleCandidates,
        # list, a set of involutions
        involutions,
        # integers, number of iterations
        M,B,T,C,
        # integer, prime, loop variable
        p,
        # integer, loop variable
        i,a,
        # elements, in G
        r,t,tPower,tPowerOld,c,
        # integer, max power we need to consider in 3. Step
        maxPower,
        # integer, loop variables in 4. Step
        nrNewCandidates, nrIterations;
    # 1. Step
    # TODO: better iteration over primes
    M := 1;
    p := 3;
    while p <= N do
        M := M * p ^ LogInt(N, p);
        p := NextPrimeInt(p);
    od;
    B := Int(Ceil(13 * Log2(Float(N)) * Log2(3 / Float(eps))));
    T := Int(Ceil(3 * Log2(3 / Float(eps))));
    C := Int(Ceil(Float(3 * N * T / 5)));
    # 2. + 3. Step
    # construct involutions
    involutions := [];
    maxPower := LogInt(N, 2);
    for i in [1 .. B] do
        r := PseudoRandom(G);
        t := r^M;
        a := 0;
        tPower := t;
        # invariant: tPower = t ^ (2 ^ a)
        repeat
            a := a + 1;
            tPowerOld := tPower;
            tPower := tPower ^ 2;
        until a = maxPower or groupIsOne(tPower);
        if a = maxPower then
            return NeverApplicable;
        fi;
        Add(involutions, tPowerOld);
    od;
    # 4. + 5. Step
    # use the observation described in the comment above this function to
    # generate candidate for three-cycles from the involutions.
    threeCycleCandidates := [];
    for t in involutions do
        nrNewCandidates := 0;
        nrIterations := 0;
        while nrIterations < C and nrNewCandidates < T do
            c := t ^ PseudoRandom(G);
            # TODO: form a set. Can we assume that group elements have an
            # ordering and simply call Set? Benchmark this with groups that are
            # so small that we possibly generate lots of the same elements.
            if not groupIsEq(t * c, c * t) then
                Add(threeCycleCandidates, (t * c) ^ 2);
                nrNewCandidates := nrNewCandidates + 1;
            fi;
            nrIterations := nrIterations + 1;
        od;
    od;
    return threeCycleCandidates;
end);

# G: the group to recognize
# c: possibly a 3-cycle
# returns a list of group elements. If G is isomorphic to an alternating or
# symmetric group and c is a 3-cycle, then this function returns a list of
# bolstering elements with respect to c.
BindGlobal("BolsteringElements",
function(G, c, eps, N, groupIsOne, groupIsEq)
    local result, R, S, prebolsteringElms, i, r, cr, cr2;
    result := [];
    R := Int(Ceil(7 / 4 * Log2(Float(eps ^ -1))));
    S := 7 * N * R;
    prebolsteringElms := [];
    i := 0;
    # find pre-bolstering elements
    while i <= S and Length(prebolsteringElms) <= R do
        r := PseudoRandom(G);
        # test whether r is pre-bolstering
        cr := c ^ r;
        cr2 := c ^ (r ^ 2);
        if not groupIsOne(Comm(cr, c))
                and not groupIsEq(cr2, c)
                and not groupIsEq(cr2, c ^ 2)
                and groupIsOne(Comm(cr2, c))
        then
            Add(prebolsteringElms, r);
        fi;
        i := i + 1;
    od;
    # construct bolstering elements
    for r in prebolsteringElms do
        if groupIsOne((c ^ (r * c * r)
                      * c ^ (r * c ^ (r ^ 2) * c)) ^ 3)
        then
            Add(result, c ^ 2 * r);
        else
            Add(result, cr);
        fi;
    od;
    return result;
end);

# g: a cycle matching c of a group G
# c: a 3-cycle of a group G
# r: arbitrary element of a group G
# The supports of c and c^(g^2) have exactly one point, say alpha, in common.
# Let phi be an isomorphism from G to a natural alternating or symmetric group.
# This function decides whether alpha is a fixed point of phi(r).
BindGlobal("IsFixedPoint",
function(g, c, r, groupIsOne, groupIsEq)
    local
        # respectively c ^ (g ^ i)
        cg, cg2, cg3, cg4,
        # temporary holder of H1, H2
        temp,
        # (sets of) elements of G
        H1, H2, x1, x2, x3,
        # helper function
        isElmPassingTest;
    # Helper function
    isElmPassingTest := function(x, H, groupIsOne)
        local nrTrivialComm, h;
        nrTrivialComm := 0;
        for h in H do
            if groupIsOne(Comm(x, h)) then
                nrTrivialComm := nrTrivialComm + 1;
            fi;
            if nrTrivialComm >= 2 then
                return false;
            fi;
        od;
        return true;
    end;
    cg := c ^ g;
    cg2 := cg ^ g;
    cg3 := cg2 ^ g;
    cg4 := cg3 ^ g;
    H1 := [ c ^ 2, c ^ cg, ~[2] ^ cg3, ~[3] ^ cg3, ~[4] ^ cg4 ];
    # Test whether an elm of the set X commutes with at least
    # two elements of H1.
    x1 := c ^ r;
    if not isElmPassingTest(x1, H1, groupIsOne) then return false; fi;
    x2 := cg2 ^ r;
    if not isElmPassingTest(x2, H1, groupIsOne) then return false; fi;
    x3 := ((cg2 ^ cg3) ^ cg4) ^ r;
    if not isElmPassingTest(x3, H1, groupIsOne) then return false; fi;
    # Test whether an elm of the set X commutes with at least
    # two elements of H2.
    H2 := [c, cg, ~[2] ^ cg3, ~[3] ^ cg3, ~[4] ^ cg4];
    if not isElmPassingTest(x1, H2, groupIsOne) then return false; fi;
    if not isElmPassingTest(x2, H2, groupIsOne) then return false; fi;
    if not isElmPassingTest(x3, H2, groupIsOne) then return false; fi;
    return true;
end);

# g: a k-cycle matching c of a group G
# c: a 3-cycle of a group G
# r: element of a group G
# W.l.o.g. let g = (1, ..., k) and c = (1, 2, 3).
# If the support of g has at least one point in common with the support of r
# and at least two points of support of g are fixed by r,
# then the algorithm returns a conjugate r^x such that r fixes the points 1, 2
# but not the point 3.
BindGlobal("AdjustCycle",
function(g, c, r, k, groupIsOne, groupIsEq)
    local
        # list of 4 booleans, is point j fixed point
        F,
        # smallest fixed point
        f1,
        # second smallest fixed point
        f2,
        # smallest non-fixed point
        m,
        # integer, loop variable over [1 .. k]
        j,
        # element of G, loop variable
        t,
        # conjugating element
        x;
    F := [false, false, false, false];
    f1 := fail;
    f2 := fail;
    m := fail;
    j := 0;
    t := c ^ (g ^ -3);
    # invariant: t = c ^ (g ^ (j - 3))
    repeat
        j := j + 1;
        t := t ^ g;
        if IsFixedPoint(g, t, r, groupIsOne, groupIsEq) then
            if j <= 4 then
                F[j] := true;
            fi;
            if f1 = fail then
                f1 := j;
            elif f2 = fail then
                f2 := j;
            fi;
        elif m = fail then
            m := j;
        fi;
    until j >= k or (j >= 4 and f1 <> fail and f2 <> fail and m <> fail);
    if f1 = fail or f2 = fail or m =fail then
        return fail;
    fi;
    # case distinction on F as in the table of Algorithm 4.20
    if F[1] then
        if F[2] then
            if F[3] then
                # 1. Case
                x := c ^ ((g * c ^ 2) ^ (m - 3) * c) * c;
            else
                # 2. Case
                x := One(c);
            fi;
        else
            if F[3] then
                if F[4] then
                    # 3. Case
                    x := c ^ g;
                else
                    # 4. Case
                    x := (c ^ 2) ^ g;
                fi;
            else
                # 5. Case
                x := c ^ ((g * c ^ 2) ^ (f2 - 3) * c);
            fi;
        fi;
    else
        if F[2] then
            if F[4] then
                # 6. Case
                x := c ^ (c ^ g);
            else
                if F[3] then
                    # 7. Case
                    x := (c ^ 2) ^ (c ^ g);
                else
                    # 8. Case
                    x := c ^ ((g * c ^ 2) ^ (f2 - 3) * c ^ g);
                fi;
            fi;
        else
            if F[3] then
                # 9. Case
                x := (c ^ 2) ^ ((g * c ^ 2) ^ (f2 - 3)) * c ^ 2;
            else
                # 10. Case
                x := c ^ ((g * c ^ 2) ^ (f2 - 3)) * c ^ ((g * c ^ 2) ^ (f1 - 3));
            fi;
        fi;
    fi;
    return r^x;
end);