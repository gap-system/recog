#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This files's authors include Friedrich Rober and Sergio Siccha.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
##
##  This file provides code for recognising whether a permutation group
##  is isomorphic to an alternating or symmetric group. It implements
##  <Cite Key="JLNP13"/>.
##
#############################################################################

# eps : real number, the error bound
# N : integer, upper bound for the degree of G
#
# Returns a record of constants used in ThreeCyclesCanditatesIterator.
RECOG.ThreeCycleCandidatesConstants := function(eps, N)
    local M, p;
    # Constants
    M := 1;
    RECOG.CachePrimesUpTo(N);
    for p in RECOG.PrimesCache do
        if p = 2 then continue; fi;
        if p > N then break; fi;
        M := M * p ^ LogInt(N, p);
    od;
    return rec(
        M := M,
        B := Int(Ceil(13 * Log(Float(N)) * Log(3 / Float(eps)))),
        T := Int(Ceil(3 * Log(3 / Float(eps)))),
        C := Int(Ceil(Float(3 * N * ~.T / 5))),
        logInt2N := LogInt(N, 2)
    );
end;

# Return false if c can not be a three cycle. This uses cheap tests to
# determine this. It is based on the Magma function heuristicThreeCycleTest.
RECOG.HeuristicThreeCycleTest := function(ri, c, logInt2N, R)
    local r, y, yTo5, k;
    c := StripMemory(c);
    if not isone(ri)(c ^ 3) then
        return false;
    fi;
    for k in [1 .. logInt2N + 1] do
        r := R[k];
        # c * c ^ r is a product of two three-cycles, so it should have order
        # 1, 2, 3 or 5.
        y := c * c ^ r;
        yTo5 := y ^ 5;
        if not isone(ri)(yTo5) and not isone(ri)(yTo5 * y) then
            return false;
        fi;
    od;
    return true;
end;

# ri : recognition node with group G
# constants : a record with components M, B, T, C, and logInt2N
#
# The following algorithm constructs a set of possible 3-cycles. It is based
# on the simple observation that the product of two involutions t1, t2, which
# only move one common point, squares to a 3-cycle.
#
# Creates and returns a function, here called oneThreeCycleCandidate. The
# function oneThreeCycleCandidate returns one of the following:
# - a three cycle candidate, i.e. an element of G
# - TemporaryFailure, if we exhausted all attempts
# - NeverApplicable, if we found out that G can't be an Sn or An
#
# Lower Bounds need n >= 9.
RECOG.ThreeCycleCandidatesIterator := function(ri, constants)
    local
        # involution
        t,
        # integers, controlling the number of iterations
        M, B, T, C, logInt2N,
        # list of random elements for heuristic three cycle test
        R,
        # counters
        nrInvolutions, nrTriedConjugates, nrThreeCycleCandidates,
        # helper functions
        tryThreeCycleCandidate, oneThreeCycleCandidate;
    # Step 1: Initialization
    # The current involution t_i
    t := fail;

    M := constants.M;
    B := constants.B;
    T := constants.T;
    C := constants.C;
    logInt2N := constants.logInt2N;

    R := List([1 .. logInt2N + 1], k -> StripMemory(RandomElm(ri, "SnAnUnknownDegree", true)!.el));

    # Counters
    # Counts the constructed involutions t_i in steps 2 & 3.
    nrInvolutions := 0;
    # Counts the elements c in step 4 that we use to conjugate the current
    # involution t_i.  We initialize nrTriedConjugates to C such that "steps 2
    # & 3" in tryThreeCycleCandidate immediately construct an involution.
    nrTriedConjugates := C;
    # counts the size of the set Gamma_i in step 4 for the current involution
    # t_i
    nrThreeCycleCandidates := 0;

    # Helper functions
    # tryThreeCycleCandidate returns one of the following:
    # - a three cycle candidate, i.e. an element of G
    # - fail, if the random conjugate c from step 4 and t commute. Then we have
    #   to call tryThreeCycleCandidate again
    # - NeverApplicable, if G can not be an Sn or An
    tryThreeCycleCandidate := function()
        local
            # integer, loop variable
            a,
            # elements, in G
            r, tPower, tPowerOld, c,
            # the three cycle candidate
            candidate;
        # Steps 2 & 3: New involution
        # Check if we either tried enough conjugates or constructed enough
        # three cycle candidates for the current involution t.
        # If this is the case, we need to construct the next involution
        if nrTriedConjugates >= C or nrThreeCycleCandidates >= T then
            r := RandomElm(ri, "SnAnUnknownDegree", true)!.el;
            # In the paper, we have t = r ^ M.
            # Invariant: tPower = (r ^ M) ^ (2 ^ a)
            tPower := r ^ M;
            # We make a small improvement to the version described in
            # <Cite Key="JLNP13"/>. The order of r ^ M is a 2-power.
            # It can be at most 2 ^ logInt2N. Thus, if we find an r such that
            # (r ^ M) ^ (2 ^ logInt2N) is non-trivial, then we can return
            # NeverApplicable.
            for a in [1 .. logInt2N] do
                tPowerOld := tPower;
                tPower := tPower ^ 2;
                if isone(ri)(tPower) then break; fi;
            od;
            if not isone(ri)(tPower) then
                return NeverApplicable;
            fi;
            t := tPowerOld;
            nrInvolutions := nrInvolutions + 1;
            nrTriedConjugates := 0;
            nrThreeCycleCandidates := 0;
        fi;
        # Steps 4 & 5: new three cycle candidate
        # Try to construct a three cycle candidate via a conjugate of t. See
        # the comment above this function.
        nrTriedConjugates := nrTriedConjugates + 1;
        c := t ^ RandomElm(ri, "SnAnUnknownDegree", true)!.el;
        if isequal(ri)(t * c, c * t) then
            # we have to call tryThreeCycleCandidate again
            return fail;
        fi;
        candidate := (t * c) ^ 2;
        # We now use a one-sided heuristic to test whether candidate can be a
        # three cycle, that is the heuristic can detect whether candidate can
        # not be a three cycle, e.g. if it does not have order three.
        nrThreeCycleCandidates := nrThreeCycleCandidates + 1;
        if RECOG.HeuristicThreeCycleTest(ri, candidate, logInt2N, R) then
            return candidate;
        else
            return fail;
        fi;
    end;
    # construct the iterator
    oneThreeCycleCandidate := function()
        local candidate;
        repeat
            if nrInvolutions >= B
                and (nrTriedConjugates >= C or nrThreeCycleCandidates >= T)
            then
                # With probability at least 1 - eps we constructed at least one
                # three cycle with this iterator.
                return fail;
            fi;
            candidate := tryThreeCycleCandidate();
            if candidate = NeverApplicable then
                return NeverApplicable;
            fi;
        until candidate <> fail;
        return candidate;
    end;
    return oneThreeCycleCandidate;
end;

# ri : recognition node with group G
# c : element of G,
#     should be a 3-cycle
# eps : real number, the error bound
# N : integer, upper bound for the degree of G
#
# Returns a list of elements of G.
#
# If the input is as assumed, then this function returns a list of bolstering
# elements with respect to c.
#
# Lower Bounds need n >= 9.
# Bolstering Elements are only defined for n >= 7.
RECOG.BolsteringElements := function(ri, cWithMem, eps, N)
    local result, R, S, nrPrebolsteringElms, i, c, rWithMem, r, cr, cr2;
    result := [];
    c := StripMemory(cWithMem);
    R := Int(Ceil(7 / 4 * Log(Float(eps ^ -1))));
    S := 7 * N * R;
    # find pre-bolstering elements
    for i in [0 .. S] do
        rWithMem := RandomElm(ri, "SnAnUnknownDegree", true)!.el;
        r := StripMemory(rWithMem);
        # test whether r is pre-bolstering
        cr := c ^ r;
        cr2 := cr ^ r;
        if not docommute(ri)(cr, c)
                and not isequal(ri)(cr2, c)
                and not isequal(ri)(cr2, c ^ 2)
                and docommute(ri)(cr2, c)
        then
            if isone(ri)((cr ^ (c * r)
                      * cr ^ (cr2 * c)) ^ 3)
            then
                Add(result, cWithMem ^ 2 * rWithMem);
            else
                Add(result, cWithMem * rWithMem);
            fi;
        fi;
        if Length(result) > R then break; fi;
    od;
    return result;
end;

# ri : recognition node with group G
# g : element of G,
#     should be a cycle matching c
# c : element of G,
#     should be a 3-cycle
# r : element of G
#
# Returns a boolean.
#
# If the input is as assumed, that is in particular the supports of c and
# c^(g^2) have exactly one point, say alpha, in common, then this function
# returns whether alpha is a fixed point of r.
RECOG.IsFixedPoint := function(ri, g, c, r)
    local
        # respectively c ^ (g ^ i)
        cg, cg2, cg3, cg4,
        # temporary holder of H1, H2
        temp,
        # (sets of) elements of G
        H1, H2, x1, x2, x3,
        # helper function
        commutesWithAtMostOne;
    # Helper function
    commutesWithAtMostOne := function(ri, x, H)
        local nrTrivialComm, h;
        nrTrivialComm := 0;
        for h in H do
            if docommute(ri)(x, h) then
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
    # Test whether an element of the set X commutes with at least
    # two elements of H1.
    x1 := c ^ r;
    if not commutesWithAtMostOne(ri, x1, H1) then return false; fi;
    x2 := cg2 ^ r;
    if not commutesWithAtMostOne(ri, x2, H1) then return false; fi;
    x3 := ((cg2 ^ cg3) ^ cg4) ^ r;
    if not commutesWithAtMostOne(ri, x3, H1) then return false; fi;
    # Test whether an elm of the set X commutes with at least
    # two elements of H2.
    H2 := [c, cg, ~[2] ^ cg3, ~[3] ^ cg3, ~[4] ^ cg4];
    if not commutesWithAtMostOne(ri, x1, H2) then return false; fi;
    if not commutesWithAtMostOne(ri, x2, H2) then return false; fi;
    if not commutesWithAtMostOne(ri, x3, H2) then return false; fi;
    return true;
end;

# ri : recognition node with group G
# g : element of G,
#     should be a k-cycle matching c
# c : element of G,
#     should be a 3-cycle
# r : element of G,
#     should have at least one moved point in common with g and should fix at
#     least two moved points of g
# k : integer,
#     should be length of cycle g
#
# Returns fail or a conjugate of r.
#
# W.l.o.g. let g = (1, ..., k) and c = (1, 2, 3).
# If the input is as assumed, then the algorithm returns a conjugate r ^ x such
# that r ^ x fixes the points 1, 2 but not the point 3.
RECOG.AdjustCycle := function(ri, g, c, r, k)
    local
        # list of 4 booleans, is point j fixed point
        F4,
        # smallest fixed point
        f1,
        # second smallest fixed point
        f2,
        # smallest non-fixed point
        m,
        # bool, false if |F| < 2 or |F| = k
        success,
        # integer, loop variable over [1 .. k]
        j,
        # element of G, loop variable
        t,
        # conjugating element
        x;
    # According to the paper we have:
    # F := { 1 <= j <= k | RECOG.IsFixedPoint(g, c ^ (g ^ (j - 3)), r) = true }
    # f1 := smallest number in F
    # f2 := second smallest number in F
    # m := smallest number *not* in F
    # We do not store F explicitely. Instead we store the intersection of F and
    # {1, 2, 3, 4} in the variable F4.
    F4 := [false, false, false, false];
    f1 := fail;
    f2 := fail;
    m := fail;
    t := c ^ (g ^ -3);
    for j in [1 .. k] do
        # invariant: t = c ^ (g ^ (j - 3))
        t := t ^ g;
        if RECOG.IsFixedPoint(ri, g, t, r) then
            if j <= 4 then
                F4[j] := true;
            fi;
            if f1 = fail then
                f1 := j;
            elif f2 = fail then
                f2 := j;
            fi;
        elif m = fail then
            m := j;
        fi;
        # f1 and f2 not being fail is equivalent to |F| >= 2
        # m not being fail is equivalent to |F| < k
        success := f1 <> fail and f2 <> fail and m <> fail;
        if success then
            if j >= 4 then
                break;
            # case 2, we do not need to compute F4[4]
            elif f1 = 1 and f2 = 2 and m = 3 then
                return r;
            fi;
        fi;
    od;
    if not success then
        return fail;
    fi;
    # case distinction on F as in the table of Algorithm 4.20
    # via a decision tree
    if F4[1] then
        if F4[2] then
            # We are in case 1, since case 2 is handled during the
            # computation of F4 above.
            x := c ^ ((g * c ^ 2) ^ (m - 3) * c) * c;
        else
            if F4[3] then
                if F4[4] then
                    # case 3
                    x := c ^ g;
                else
                    # case 4
                    x := (c ^ 2) ^ g;
                fi;
            else
                # case 5
                x := c ^ ((g * c ^ 2) ^ (f2 - 3) * c);
            fi;
        fi;
    else
        if F4[2] then
            if F4[4] then
                # case 6
                x := c ^ (c ^ g);
            else
                if F4[3] then
                    # case 7
                    x := (c ^ 2) ^ (c ^ g);
                else
                    # case 8
                    x := c ^ ((g * c ^ 2) ^ (f2 - 3) * c ^ g);
                fi;
            fi;
        else
            if F4[3] then
                # case 9
                x := (c ^ 2) ^ ((g * c ^ 2) ^ (f2 - 3)) * c ^ 2;
            else
                # case 10
                x := c ^ ((g * c ^ 2) ^ (f2 - 3)) * c ^ ((g * c ^ 2) ^ (f1 - 3));
            fi;
        fi;
    fi;
    return r^x;
end;

# ri : recognition node with group G
# g : element of G,
#     should be a k-cycle matching c
# c : element of G,
#     should be a 3-cycle
# r : element of G,
#     should be a cycle as in the return value of RECOG.AdjustCycle. If e.g.
#     g = (1, 2, ..., k), then r would be a cycle fixing 1 and 2 and moving 3.
# s : element of group G,
#     should be a storage cycle
# k : integer,
#     should be length of cycle g
# k0 : integer,
#      should be length of cycle r
#
# Returns a list consisting of:
# - gTilde: element of G,
#           should be a cycle matching g
# - sTilde: element of G,
#           should be current storage cycle, since we may call RECOG.AppendPoints
#           several times and may not have used the last sTilde.
# - kTilde: integer,
#           should be the length of gTilde
#
# The algorithm appends new points to the cycle g. Since g will always be a
# cycle of odd length, new points can only be appended in pairs. We identify
# the point j in {1, ..., k} with the 3-cycle c ^ (g ^ (j - 3)). We store new
# points in the storage cycle sTilde until we have found two different points.
# Then we append these to g.
RECOG.AppendPoints := function(ri, g, c, r, s, k, k0)
    local gTilde, sTilde, kTilde, gc2, x, j;
    gTilde := g;
    sTilde := s;
    kTilde := k;
    x := c;
    for j in [1 .. k0 - 1] do
        # invariant: x = c ^ (r ^ j)
        x := x ^ r;
        if docommute(ri)(x, gTilde * c ^ 2) then
            # If sTilde doesn't already store a point, then store x.
            if isone(ri)(sTilde) then
                sTilde := x;
            fi;
            # Do we now have two different points? If so, append them.
            if not isone(ri)(sTilde) and not isequal(ri)(sTilde, x) then
                kTilde := kTilde + 2;
                gTilde := gTilde * sTilde ^ (x ^ 2);
                sTilde := One(gTilde);
            fi;
        fi;
    od;
    return [gTilde, sTilde, kTilde];
end;

# ri : recognition node with group G
# g : element of G
# p : prime
# Returns whether g is an element of order p.
RECOG.IsElmOfPrimeOrder := function(ri, g, p)
    if not isone(ri)(g) and isone(ri)(g ^ p) then
        return true;
    else
        return false;
    fi;
end;

# ri : recognition node with group G
# c : a 3-cycle of a group G
# x : bolstering element with respect to c
# N : integer, upper bound for the degree of G
#
# returns either fail or a list consisting of:
# - g, cycle matching c
# - k, length of cycle g.
#
# We return fail if one of the following holds:
# - N is not an upper bound for the degree of G
# - c is not a 3-cycle
RECOG.BuildCycle := function(ri, c, x, N)
    local
        # integers
        m, mDash,
        # group elements
        d, y, dx, e, z, f, g, x2;
    # Compute m.
    # m is the least natural number such that with
    # d = c ^ (x ^ (m + 1))
    # we have Order(d * c) <> 5. Note that m >= 1.
    # We also compute
    # y = c * (c ^ x) * (c ^ (x ^ 2)) * ... * (c ^ (x ^ m)).
    # The next three lines correspond to m = 1
    # We use x ^ 2 several times.
    x2 := x ^ 2;
    m := 1;
    y := c * (c ^ x);
    d := c ^ x2;
    while true do
        if m >= N / 2 then
            return fail;
        elif RECOG.IsElmOfPrimeOrder(ri, d * c, 5) then
            m := m + 1;
        else
            break;
        fi;
        y := y * d;
        d := d ^ x;
    od;
    if m = 1 then
        return fail;
    fi;
    # case |alpha - beta| = 0
    if isequal(ri)(d, c) or isequal(ri)(d, c ^ 2) then
        return [y, 2 * m + 3];
    fi;
    # case |alpha - beta| = 1
    dx := d ^ x;
    if not RECOG.IsElmOfPrimeOrder(ri, dx * c, 5) then
        return [y, 2 * m + 3];
    fi;
    # case |alpha - beta| >= 2
    # case distinction on element e
    # w in v ^ <x>
    if not RECOG.IsElmOfPrimeOrder(ri, d * c, 2) then
        # case 1, alpha > beta
        if docommute(ri)(dx, d ^ c) then
            e := dx ^ c;
        # case 2, alpha < beta
        else
            e := (dx ^ (c ^ 2)) ^ 2;
        fi;
    # w not in v ^ <x>
    else
        # case 3, alpha > beta
        if not docommute(ri)(dx, d ^ c) then
            e := dx ^ (c ^ 2);
        # case 4, alpha < beta
        else
            e := (dx ^ c) ^ 2;
        fi;
    fi;
    z := d ^ e;
    # Compute m' (here mDash).
    # mDash is the least natural number such that with
    # f := z ^ (x ^ (2 * mDash))
    # we have Order(f * c) <> 5. Note that mDash >= 1.
    # We also compute
    # g = y * z * (z ^ (x ^ 2)) * ... * (z ^ (x ^ (2 * (mDash - 1)))).
    # The next three lines correspond to mDash = 1
    mDash := 1;
    g := y * z;
    f := z ^ x2;
    while true do
        if mDash >= N / 2 then
            return fail;
        elif RECOG.IsElmOfPrimeOrder(ri, f * c, 5) then
            mDash := mDash + 1;
        else
            break;
        fi;
        g := g * f;
        f := f ^ x2;
    od;
    return [g, 2 * mDash + 2 * m + 3];
end;

# ri : recognition node with group G
# c : element of G,
#     should be a 3-cycle
# eps : real number, the error bound
# N : integer, upper bound for the degree of G
#
# Returns fail or a list [g, k] consisting of:
# - g: element of G,
#      should be a k-cycle matching c
# - k: integer,
#      should be length of cycle g.
#
# Note that the order of the returned list is reversed with respect to the
# paper to be consistent with the return values of the other functions.
#
# We return fail if one of the following holds:
# - the list of bolstering elements is too small
# - N is not an upper bound for the degree of G
# - c is not a 3-cycle
RECOG.ConstructLongCycle := function(ri, c, eps, N)
    local g, k, tmp, B, x;
    B := RECOG.BolsteringElements(ri, c, Float(eps) / 2., N);
    if Length(B) < Int(Ceil(7. / 4. * Log(2. / Float(eps)))) then
        return fail;
    fi;
    k := 0;
    for x in B do
        tmp := RECOG.BuildCycle(ri, c, x, N);
        if tmp = fail then
            return fail;
        elif tmp[2] > k then
            g := tmp[1];
            k := tmp[2];
        fi;
    od;
    return [g, k];
end;

# ri : recognition node with group G
# g : element of G,
#     should be a k-cycle matching c
# c : element of G,
#     should be a 3-cycle
# k : integer,
#     should be length of cycle g
# eps : real number, the error bound
# N : integer, upper bound for the degree of G
#
# Returns fail or a list consisting of:
# - gTilde : element of G,
#            long cycle, a standard generator of An < G
# - cTilde : element of G,
#            3-cycle, a standard generator of An < G
# - kTilde : integer,
#            degree of group An < G, that is generated by gTilde and cTilde
RECOG.SnAnStandardGenerators := function(ri, g, c, k, eps, N)
    local s, k0, c2, r, kTilde, gTilde, i, x, m, tmp, cTilde;
    s := One(g);
    k0 := k - 2;
    c2 := c ^ 2;
    r := g * c2;
    kTilde := k;
    gTilde := g;
    for i in [1 .. Int(Ceil(Log(10. / 3.) ^ (-1)
            * (Log(Float(N)) + Log(1 / Float(eps)))))] do
        x := r ^ RandomElm(ri, "SnAnUnknownDegree", true)!.el;
        m := RECOG.AdjustCycle(ri, gTilde, c, x, kTilde);
        if m = fail then return fail; fi;
        tmp := RECOG.AppendPoints(ri, gTilde, c, m, s, kTilde, k0);
        gTilde := tmp[1];
        s := tmp[2];
        kTilde := tmp[3];
        if kTilde > N then return fail; fi;
    od;
    if isone(ri)(s) then
        gTilde := c2 * gTilde;
        cTilde := c;
    else
        kTilde := kTilde + 1;
        gTilde := gTilde * s;
        cTilde := s;
    fi;
    if RECOG.SatisfiesAnPresentation(ri,
                                     StripMemory(gTilde),
                                     StripMemory(cTilde),
                                     kTilde) then
        return [gTilde, cTilde, kTilde];
    else
        return fail;
    fi;
end;

# The following two functions RECOG.FindAnElementMappingIToJ and
# RECOG.FindImageSnAnSmallDegree are used for small degrees, 5 <= n < 11, to
# compute a monomorphism into Sn based on Jonathan Conder's thesis <Cite
# Key="C12"/>.
#
# In Conder's Thesis: Algorithm 7, ConjugateMap
# Returns an element c such that under the monomorphism Grp(ri) -> S_n given by
# s and t the image of c maps the point i to j.
RECOG.FindAnElementMappingIToJ := function(s, t, i, j)
    if i < 3 then
        if j < 3 then
            return t^(j-i);
        else
            return t^(3-i)*s^(j-3);
        fi;
    else
        return s^(j-i);
    fi;
end;

# In Conder's Thesis: Algorithm 10, ElementToSmallDegreePermutation,
# correctness see Theorem 3.5.2.
# Returns the image of g under the monomorphism Grp(ri) -> S_n given by s and
# t, for n >= 5.
# Under that monomorphism s is mapped to a long cycle, t to a three cycle,
# and the list e (E in Conder's Thesis) to [(1,2,3), (1,2,4), (1,2,5)].
# Note that the arguments are in a different order than in the thesis, such
# that they are more consistent with the GAP function FindImageSn.
RECOG.FindImageSnAnSmallDegree := function(ri, n, g, s, t, e)
    local T, L, H, i, j, k, l, c, h, h1, h2, h2h1, h1h2Comm, S, m, continueI, continueJ;
    T := [ e[1], e[2], e[3], e[1] ^ 2 * e[2], e[1] ^ 2 * e[3], e[2] ^ 2 * e[3], e[1] * e[2] ^ 2,
           e[1] * e[3] ^ 2, e[2] * e[3] ^ 2, e[2] * e[3] ^ 2 * e[1] * e[2] ^ 2 ];
    L := [];
    # H = [ (1,2,3), (1,4,5) ]
    H := [T[1], T[6]];
    for l in [1 .. n] do
        for j in [1 .. n] do
            continueJ := false;
            if j = 1 then
                c := One(Grp(ri));
            else
                h := RECOG.FindAnElementMappingIToJ(s, t, j - 1, j);
                c := c * h;
            fi;

            for i in [1 .. Length(H)] do
                continueI := false;
                h1 := H[i] ^ g;
                S := [1, 1];
                for k in [1 .. Length(S)] do
                    h2 := T[5 * k - 4] ^ c;

                    h2h1 := h2 * h1;
                    if isone(ri)(h2h1) or isone(ri)(h2 * h2h1) then
                        continueI := true; # continue loop i
                        break;
                    fi;
                    h1h2Comm := Comm(h1, h2);
                    if isone(ri)(h1h2Comm) then
                        continueJ := true; # continue loop j
                        break;
                    elif isone(ri)(h1h2Comm ^ 2) then
                        S[k] := 2;
                    fi;
                od;
                # Jump to some outer loop.
                if continueI then
                    continue;
                elif continueJ then
                    break;
                fi;

                if S[1] = S[2] then
                    if S[1] = 1 then
                        for k in [2 .. 5] do
                            if docommute(ri)(h1, T[k] ^ c) then
                                continueJ := true; # continue loop j
                                break;
                            fi;
                        od;
                    fi;
                else
                    if S[1] > S[2] then
                        m := 6;
                    else
                        m := 8;
                    fi;
                    for k in [1 .. 2] do
                        if docommute(ri)(h1, T[m + k] ^ c) then
                            continueJ := true; # continue loop j
                            break;
                        fi;
                    od;
                fi;
                # Jump to some outer loop.
                if continueJ then
                    break;
                fi;
            od;

            if continueJ then
                continue;
            else
                Add(L, j);
                break;
            fi;
        od;

        c := RECOG.FindAnElementMappingIToJ(s, t, l, l + 1);
        for i in [1 .. Length(H)] do
            H[i] := H[i] ^ c;
        od;
    od;

    return PermList(L);
end;

# This function is based on the function RECOG.RecogniseSnAn in gap/SnAnBB.gi
# ri : recognition node with group G,
# n : degree
# stdGensAnWithMemory : standard generators of An < G
#
# Returns either fail or a record with components type and isoData, where:
# - type: the isomorphism type, that is either the string "Sn" or "An".
# - isoData: a list [stdGens, filter, n] where
#   - stdGens are the standard generators of G. They do not have memory.
#   - filter implicitly defines the isomorphism. It is used by
#     RECOG.FindImageSn, RECOG.FindImageAn, and RECOG.FindImageSnAnSmallDegree
#     to compute the isomorphism.
#   - n is the degree of the group.
# - slpToStdGens: an SLP from the generators of G to stdGens.
RECOG.ConstructSnAnIsomorphism := function(ri, n, stdGensAnWithMemory)
    local stdGensAn, filter, filterPart, gImage, foundOddPermutation, slp, eval,
        hWithMemory, bWithMemory, stdGensSnWithMemory, b, h, g;
    stdGensAn := StripMemory(stdGensAnWithMemory);
    # Construct filter. In <Cite Key="C12"/> filter is called E.
    # In <Cite Key="JLNP13"/> filter is called `xi`.
    if n < 11 then
        filterPart := [stdGensAn[2], (~[1] ^ stdGensAn[1]) ^ (2 * (n mod 2) - 1),
                       (~[2] ^ stdGensAn[1]) ^ (2 * (n mod 2) - 1)];
        filter := [[stdGensAn[1], stdGensAn[2]], filterPart];
    else
        filter := RECOG.ConstructXiAn(n, stdGensAn[1], stdGensAn[2]);
    fi;
    foundOddPermutation := false;
    # For each generator, check whether its image und the monomorphism into the
    # S_n has odd sign. If so, switch to recognizing S_n.
    # For each generator also check whether the SLP for its image in the A_n
    # was computed correctly.
    for g in ri!.gensHmem do
        if n < 11 then
            gImage := RECOG.FindImageSnAnSmallDegree(ri, n, StripMemory(g),
                                                     filter[1][1], filter[1][2],
                                                     filter[2]);
        else
            gImage := RECOG.FindImageAn(ri, n, StripMemory(g),
                                        stdGensAn[1], stdGensAn[2],
                                        filter[1], filter[2]);
        fi;
        if gImage = fail then return fail; fi;
        if SignPerm(gImage) = -1 then
            # we found an odd permutation,
            # so the group cannot be An
            foundOddPermutation := true;
            break;
        fi;
        slp := RECOG.SLPforAn(n, gImage);
        eval := ResultOfStraightLineProgram(slp,
                                            [stdGensAn[2], stdGensAn[1]]);
        if not isequal(ri)(eval, StripMemory(g)) then return fail; fi;
    od;
    if not foundOddPermutation then
        return rec(type := "An",
                   isoData := [[stdGensAn[1], stdGensAn[2]], filter, n],
                   slpToStdGens := SLPOfElms(stdGensAnWithMemory));
    fi;
    # Construct standard generators for Sn: [bWithMemory, hWithMemory].
    slp := RECOG.SLPforAn(n, (1,2) * gImage);
    eval := ResultOfStraightLineProgram(
        slp, [stdGensAnWithMemory[2], stdGensAnWithMemory[1]]
    );
    hWithMemory := eval * g ^ -1;
    bWithMemory := stdGensAnWithMemory[1] * stdGensAnWithMemory[2];
    if n mod 2 = 0 then
        bWithMemory := hWithMemory * bWithMemory;
    fi;
    stdGensSnWithMemory := [bWithMemory, hWithMemory];
    b := StripMemory(bWithMemory);
    h := StripMemory(hWithMemory);
    if not RECOG.SatisfiesSnPresentation(ri, n, b, h) then
        return fail;
    fi;
    if n >= 11 then
        filter := RECOG.ConstructXiSn(n, b, h);
    fi;
    for g in ri!.gensHmem do
        if n < 11 then
            gImage := RECOG.FindImageSnAnSmallDegree(ri, n, StripMemory(g),
                                                     filter[1][1], filter[1][2],
                                                     filter[2]);
        else
            gImage := RECOG.FindImageSn(ri, n, StripMemory(g),
                                        b, h,
                                        filter[1], filter[2]);
        fi;
        if gImage = fail then return fail; fi;
        slp := RECOG.SLPforSn(n, gImage);
        eval := ResultOfStraightLineProgram(slp, [h, b]);
        if not isequal(ri)(eval, StripMemory(g)) then return fail; fi;
    od;
    return rec(type := "Sn",
               isoData := [[b, h], filter, n],
               slpToStdGens := SLPOfElms(stdGensSnWithMemory));
end;

# This method is an implementation of <Cite Key="JLNP13"/>. It is the main
# function of SnAnUnknownDegree.
# From <Cite Key="JLNP13" Where="Theorem 1.1"/>:
# RECOG.RecogniseSnAn is a one-sided Monte-Carlo algorithm with the following
# properties. It takes as input a black-box group <A>G</A>, a natural number
# <A>N</A> and a real number <A>eps</A> with 0 < <A>eps</A> < 1. If <A>G</A> is
# isomorphic to An or Sn for some 9 <= <A>n</A> <= <A>N</A>, it returns with
# probability at least 1 - <A>eps</A> the degree <A>n</A> and an
# isomorphism from <A>G</A> to An or Sn.
RECOG.RecogniseSnAn := function(ri, eps, N)
    local T, foundPreImagesOfStdGens, constants, iterator, c, tmp, recogData, i;
    T := Int(Ceil(Log2(1 / Float(eps))));
    foundPreImagesOfStdGens := false;
    constants := RECOG.ThreeCycleCandidatesConstants(1. / 4., N);
    for i in [1 .. T] do
        iterator := RECOG.ThreeCycleCandidatesIterator(ri, constants);
        c := iterator();
        while c <> fail do
            if c = NeverApplicable then return NeverApplicable; fi;
            tmp := RECOG.ConstructLongCycle(ri, c, 1. / 8., N);
            if tmp = fail then
                c := iterator();
                continue;
            fi;
            # Now tmp contains [g, k] where
            #   g corresponds to a long cycle
            #   k is its length
            tmp := RECOG.SnAnStandardGenerators(ri, tmp[1], c, tmp[2], 1. / 8., N);
            if tmp = fail then
                c := iterator();
                continue;
            fi;
            # Now tmp contains [g, c, n] where
            #   g, c correspond to standard generators of An
            recogData := RECOG.ConstructSnAnIsomorphism(ri, tmp[3], tmp{[1,2]});
            if recogData = fail then continue; fi;
            return recogData;
        od;
    od;
    return TemporaryFailure;
end;

# #! @BeginChunk SnAnSmallUnknownDegree
# #! This method checks element orders to rule out whether the input group might
# #! be A_5, S_5, A_6, S_6, or Aut(A_6). If it wasn't able to rule that out it
# #! tries to find a small orbit, which must exist if the input group is
# #! isomorphic to one of the groups in question.
# #! This method only takes matrix or projective inputs.
# #! @EndChunk SnAnSmallUnknownDegree
# BindRecogMethod(FindHomMethodsGeneric, "SnAnSmallUnknownDegree",
# "find small orbit if the group might be A_5, S_5, A_6, S_6, or Aut(A_6)",
# function(ri, G)
#     local orders, orbit;
#     orders := Set(List(
#         [1..30],
#         i -> RandomElmOrd(ri, "SnAnSmallUnknownDegree", false).order
#     ));
#     # Orders which are not in Aut(A_6):
#     if ForAny(orders, x -> x >= 11) or 7 in orders or 9 in orders then
#         return NeverApplicable;
#     fi;
#     orbit := Orb(G, One(G)[1], OnPoints, rec(storenumbers := true));
#     Enumerate(orbit, 1441);
#     if Length(orbit) <= 1440 then
#         # Our reduction is that we found a smallish orbit.
#         SetHomom(ri, OrbActionHomomorphism(G, orbit));
#         Setmethodsforimage(ri, FindHomDbPerm);
#         return Success;
#     fi;
#     return NeverApplicable;
# end);

RECOG.LowerBoundForDegreeOfSnAnViaOrders := function(ri)
    local G, orders;
    G := Grp(ri);
    orders := Set(List(
        [1..30],
        i -> RandomElmOrd(ri, "LowerBoundForDegreeOfSnAnViaOrders", false).order
    ));
    return Maximum(List(
        orders,
        # For a given order, the sum over its factorisation into prime powers,
        # gives a lower bound for the degree of the smallest symmetric group,
        # that can contain an element of such an order.
        o -> Sum(Collected(FactorsInt(o)),
                 tup -> tup[1] ^ tup[2])
    ));
end;

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

RECOG.SnAnUpperBoundForDegree := function(ri)
    local G, N, p, d, M;
    G := Grp(ri);
    # N = upper bound for degree
    # Check magma
    if IsPermGroup(G) then
        # We assume that G is primitive and not a giant.
        # The smallest non-natural primitive action of Sn or An induces
        # a large base group. Thus by [L84] its degree is smallest, when the
        # action is on 2-subsets. Thus its degree is at least n * (n-1) / 2.
        # Thus for a given degree k, we have
        # n >= 1/2 + Sqrt(1/4 + 2*k).
        N := Int(Ceil(1/2 + Sqrt(Float(1/4 + 2 * NrMovedPoints(G)))));
    elif IsMatrixGroup(G) then
        p := Characteristic(DefaultFieldOfMatrixGroup(G));
        d := DimensionOfMatrixGroup(G);
        # Let N be the largest integer such that A_N has a representation of
        # dimension d.
        if ri!.projective then
            # If n >= 9, then the smallest irreducible projective An-module has
            # dimension n-2, see [KL90], Proposition 5.3.7.
            # Assume N >= 9 and use the comment above to compute N. If we
            # arrive at a value < 9 for N, then we must have been in the case N
            # < 9.
            # TODO: The table in [KL90], Proposition 5.3.7. has more detailed
            # values for 5 <= n < 9. Do we want to use that?
            N := Maximum(8, d + 2);
        else
            # If n >= 10, then the smallest irreducible An-module is the
            # fully deleted permutation module, see [KL90], Proposition 5.3.5.
            # It has dimension n-2 if p|n and dimension n-1 otherwise.
            # Assume N >= 10 and use the comment above to compute N. If we
            # arrive at a value < 10 for N, then we must have been in the case
            # N < 10.
            if (d + 2) mod p = 0 then
                N := d + 2;
            else
                N := d + 1;
            fi;
            N := Maximum(9, N);
        fi;
    else
        N := ErrorNoReturn("SnAnUnknownDegree: no method to compute bound",
                           " <N>, Grp(<ri>) must be an IsPermGroup or an",
                           " IsMatrixGroup");
    fi;
    # N = lower bound for degree
    M := RECOG.LowerBoundForDegreeOfSnAnViaOrders(ri);
    # Our upper bound is smaller than our lower bound.
    if N < M then
        return NeverApplicable;
    fi;
    # Lower bound does not exclude A5, S5, A6 or S6
    # If the input group is isomorphic to a symmetric or alternating group of
    # degrees 5 or 6, then this method might not exit quickly.
    if M <= 6 then
        return TemporaryFailure;
    fi;

    return N;
end;

#! @BeginChunk SnAnUnknownDegree
#! This method tries to determine whether the input group given by <A>ri</A> is
#! isomorphic to a symmetric group Sn or alternating group An with
#! <M>9 \leq n</M>.
#! It is an implementation of <Cite Key="JLNP13"/>.
#!
#! If <A>Grp(ri)</A> is a permutation group, we assume that it is primitive and
#! not a giant (a giant is Sn or An in natural action).
#!
#! This method can also recognise a symmetric group Sn or alternating group An with
#! <M>n = 7</M> or <M>n = 8</M>, but is not required to return a result with
#! the specified error probability.
#!
#! This method cannot recognise a symmetric group Sn or alternating group An with
#! <M>n = 5</M> or <M>n = 6</M>, since it uses pre-bolstering elements,
#! which need at least 7 moved points.
#! If the input group is isomorphic to a symmetric or alternating group of
#! degrees 5 or 6, then this method might not exit quickly.
#!
#! @EndChunk
BindRecogMethod(FindHomMethodsGeneric, "SnAnUnknownDegree",
"method groups isomorphic to Sn or An with n >= 9",
function(ri, G)
    local eps, N, degreeData, recogData, isoData, degree, swapSLP;
    # if IsBound(ri!.fhmethsel) and not "SnAnSmallUnknownDegree"
    #         in NamesOfComponents(ri!.fhmethsel.inapplicableMethods) then
    #     ErrorNoReturn("If called via CallMethods then SnAnSmallUnknownDegree must be tried before ",
    #                   "SnAnUnknownDegree.");
    # fi;
    eps := 1 / 10^2;
    N := RECOG.SnAnUpperBoundForDegree(ri);
    if not IsInt(N) then
        return N;
    fi;
    # This is usually much smaller than RECOG.SnAnUpperBoundForDegree
    if N > 20 then
        degreeData := RECOG.GuessSnAnDegree(ri);
        if degreeData = fail then
            return TemporaryFailure;
        fi;
        N := Minimum(N, degreeData.degree);
    fi;
    # Try to find an isomorphism
    recogData := RECOG.RecogniseSnAn(ri, eps, N);
    # RECOG.RecogniseSnAn returned NeverApplicable or TemporaryFailure
    if not IsRecord(recogData) then
        return recogData;
    fi;
    isoData := recogData.isoData;
    ri!.SnAnUnknownDegreeIsoData := isoData;
    SetFilterObj(ri, IsLeaf);
    degree := isoData[3];
    if recogData.type = "Sn" then
        SetSize(ri, Factorial(degree));
        SetIsRecogInfoForAlmostSimpleGroup(ri, true);
    else
        SetSize(ri, Factorial(degree) / 2);
        SetIsRecogInfoForSimpleGroup(ri, true);
    fi;
    # Note that when setting the nice generators we reverse their order, such
    # that it fits to the SLPforSn/SLPforAn function!
    SetNiceGens(ri, Reversed(isoData[1]));
    swapSLP := StraightLineProgram([[[2, 1], [1, 1]]], 2);
    Setslptonice(ri,
                 CompositionOfStraightLinePrograms(swapSLP,
                                                   recogData.slpToStdGens));
    if recogData.type = "Sn" then
        if degree < 11 then
            Setslpforelement(ri, SLPforElementFuncsGeneric.SnSmallDegree);
        else
            Setslpforelement(ri, SLPforElementFuncsGeneric.SnUnknownDegree);
        fi;
    else
        if degree < 11 then
            Setslpforelement(ri, SLPforElementFuncsGeneric.AnSmallDegree);
        else
            Setslpforelement(ri, SLPforElementFuncsGeneric.AnUnknownDegree);
        fi;
    fi;
    return Success;
end);

# The SLP function if G is isomorphic to Sn with small degree.
SLPforElementFuncsGeneric.SnSmallDegree := function(ri, g)
    local isoData, degree, image;
    isoData := ri!.SnAnUnknownDegreeIsoData;
    degree := isoData[3];
    image := RECOG.FindImageSnAnSmallDegree(ri, degree, g, isoData[2][1][1], isoData[2][1][2],
                       isoData[2][2]);
    return RECOG.SLPforSn(degree, image);
end;

# The SLP function if G is isomorphic to An with small degree.
SLPforElementFuncsGeneric.AnSmallDegree := function(ri, g)
    local isoData, degree, image;
    isoData := ri!.SnAnUnknownDegreeIsoData;
    degree := isoData[3];
    image := RECOG.FindImageSnAnSmallDegree(ri, degree, g, isoData[2][1][1], isoData[2][1][2],
                       isoData[2][2]);
    return RECOG.SLPforAn(degree, image);
end;

# The SLP function if G is isomorphic to Sn.
SLPforElementFuncsGeneric.SnUnknownDegree := function(ri, g)
    local isoData, degree, image;
    isoData := ri!.SnAnUnknownDegreeIsoData;
    degree := isoData[3];
    image := RECOG.FindImageSn(ri, degree, g, isoData[1][1], isoData[1][2],
                       isoData[2][1], isoData[2][2]);
    return RECOG.SLPforSn(degree, image);
end;

# The SLP function if G is isomorphic to An.
SLPforElementFuncsGeneric.AnUnknownDegree := function(ri, g)
    local isoData, degree, image;
    isoData := ri!.SnAnUnknownDegreeIsoData;
    degree := isoData[3];
    image := RECOG.FindImageAn(ri, degree, g, isoData[1][1], isoData[1][2],
                       isoData[2][1], isoData[2][2]);
    return RECOG.SLPforAn(degree, image);
end;
