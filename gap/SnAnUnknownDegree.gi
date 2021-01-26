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
##  is isomorphic to an alternating or symmetric group. It implements [JLNP13].
##
#############################################################################
#
# FIXME: Move me into GAP
# Helper function to compute all primes up to a given integer via a prime sieve
BindGlobal("AllPrimesUpTo",
function(n)
    local i, j, sieve, result;
    if n <= 1000 then
      return Primes{[1..PositionSorted(Primes, n+1)-1]};
    fi;
    sieve := BlistList([1..n], [1..n]);
    sieve[1] := false;
    for i in [2..Int(n/2)] do
        sieve[i*2] := false;
    od;
    i := 3;
    while i * i <= n do
        if sieve[i] then
            j := 3*i;
            while j <= n do
                sieve[j] := false;
                j := j + 2*i;
            od;
        fi;
        i := i + 2;
    od;
    return ListBlist([1..n], sieve);
end);

# eps : real number, the error bound
# N : integer, upper bound for the degree of G
#
# Returns a record of constants used in ThreeCyclesCanditatesIterator.
BindGlobal("ThreeCycleCandidatesConstants",
    function(eps, N)
    local M, allPrimes, i, p;
    # Constants
    M := 1;
    allPrimes := AllPrimesUpTo(N);
    for i in [2 .. Length(allPrimes)] do
        p := allPrimes[i];
        M := M * p ^ LogInt(N, p);
    od;
    return rec(
        M := M,
        B := Int(Ceil(13 * Log2(Float(N)) * Log2(3 / Float(eps)))),
        T := Int(Ceil(3 * Log2(3 / Float(eps)))),
        C := Int(Ceil(Float(3 * N * ~.T / 5))),
        logInt2N := LogInt(N, 2)
    );
end);

# ri : recog info record with group G
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
BindGlobal("ThreeCycleCandidatesIterator",
    function(ri, constants)
    local
        # involution
        t,
        # integers, controlling the number of iterations
        M, B, T, C, logInt2N,
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
            r, tPower, tPowerOld, c;
        # Steps 2 & 3: New involution
        # Check if we either tried enough conjugates or constructed enough
        # three cycle candidates for the current involution t.
        # If this is the case, we need to construct the next involution
        if nrTriedConjugates >= C or nrThreeCycleCandidates >= T then
            r := RandomElm(ri, "SnAnUnknownDegree", true)!.el;
            tPower := r ^ M;
            # Invariant: tPower = (r ^ M) ^ (2 ^ a)
            # We make a small improvement to the version described in the
            # algorithm. The order of r ^ M is a 2-power. It can be at most
            # 2 ^ logInt2N. Thus, if we find an r such that
            # (r ^ M) ^ (2 & logInt2N) is non-trivial, then we can return
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
        if not isequal(ri)(t * c, c * t) then
            nrThreeCycleCandidates := nrThreeCycleCandidates + 1;
            return (t * c) ^ 2;
        else
            # we have to call tryThreeCycleCandidate again
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
end);

# ri : recog info record with group G
# c : element of G,
#     should be a 3-cycle
# eps : real number, the error bound
# N : integer, upper bound for the degree of G
#
# Returns a list of elements of G.
#
# If the input is as assumed, then this function returns a list of bolstering
# elements with respect to c.
BindGlobal("BolsteringElements",
function(ri, c, eps, N)
    local result, R, S, nrPrebolsteringElms, i, r, cr, cr2;
    result := [];
    R := Int(Ceil(7 / 4 * Log2(Float(eps ^ -1))));
    S := 7 * N * R;
    # find pre-bolstering elements
    for i in [0 .. S] do
        r := RandomElm(ri, "SnAnUnknownDegree", true)!.el;
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
                Add(result, c ^ 2 * r);
            else
                Add(result, c * r);
            fi;
        fi;
        if Length(result) > R then break; fi;
    od;
    return result;
end);

# ri : recog info record with group G
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
BindGlobal("IsFixedPoint",
function(ri, g, c, r)
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
end);

# ri : recog info record with group G
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
BindGlobal("AdjustCycle",
function(ri, g, c, r, k)
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
    # F := { 1 \leq j \leq k | IsFixedPoint(g, c ^ (g ^ (j - 3)), r) = true }
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
        if IsFixedPoint(ri, g, t, r) then
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
end);

# ri : recog info record with group G
# g : element of G,
#     should be a k-cycle matching c
# c : element of G,
#     should be a 3-cycle
# r : element of G,
#     should be a cycle as in the return value of AdjustCycle. If e.g.
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
#           should be current storage cycle, since we may call AppendPoints
#           several times and may not have used the last sTilde.
# - kTilde: integer,
#           should be the length of gTilde
#
# The algorithm appends new points to the cycle g. Since g will always be a
# cycle of odd length, new points can only be appended in pairs. We identify
# the point j in {1, ..., k} with the 3-cycle c ^ (g ^ (j - 3)). We store new
# points in the storage cycle sTilde until we have found two different points.
# Then we append these to g.
BindGlobal("AppendPoints",
function(ri, g, c, r, s, k, k0)
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
end);

# ri : recog info record with group G
# g : element of G
# p : prime
# Returns whether g is an element of order p.
BindGlobal("IsElmOfPrimeOrder",
function(ri, g, p)
    if not isone(ri)(g) and isone(ri)(g ^ p) then
        return true;
    else
        return false;
    fi;
end);

# ri : recog info record with group G
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
BindGlobal("BuildCycle",
function(ri, c, x, N)
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
        elif IsElmOfPrimeOrder(ri, d * c, 5) then
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
    if not IsElmOfPrimeOrder(ri, dx * c, 5) then
        return [y, 2 * m + 3];
    fi;
    # case |alpha - beta| >= 2
    # case distinction on element e
    # w in v ^ <x>
    if not IsElmOfPrimeOrder(ri, d * c, 2) then
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
        elif IsElmOfPrimeOrder(ri, f * c, 5) then
            mDash := mDash + 1;
        else
            break;
        fi;
        g := g * f;
        f := f ^ x2;
    od;
    return [g, 2 * mDash + 2 * m + 3];
end);

# ri : recog info record with group G
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
# Note that the order of the returned list is reversed with respect to the paper to be
# consistent with the return values of the other functions.
#
# We return fail if one of the following holds:
# - the list of bolstering elements is too small
# - N is not an upper bound for the degree of G
# - c is not a 3-cycle
BindGlobal("ConstructLongCycle",
function(ri, c, eps, N)
    local g, k, tmp, B, x;
    B := BolsteringElements(ri, c, Float(eps) / 2., N);
    if Length(B) < Int(Ceil(7. / 4. * Log(2. / Float(eps)))) then
        return fail;
    fi;
    k := 0;
    for x in B do
        tmp := BuildCycle(ri, c, x, N);
        if tmp = fail then
            return fail;
        elif tmp[2] > k then
            g := tmp[1];
            k := tmp[2];
        fi;
    od;
    return [g, k];
end);

# ri : recog info record with group G
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
BindGlobal("StandardGenerators",
function(ri, g, c, k, eps, N)
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
        m := AdjustCycle(ri, gTilde, c, x, kTilde);
        if m = fail then return fail; fi;
        tmp := AppendPoints(ri, gTilde, c, m, s, kTilde, k0);
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
    if SatisfiesAnPresentation(ri, gTilde, cTilde, kTilde) then
        return [gTilde, cTilde, kTilde];
    else
        return fail;
    fi;
end);

# This function is an excerpt of the function RecogniseSnAn in gap/SnAnBB.gi
# ri : recog info record with group G,
# n : degree
# stdGensAn : standard generators of An < G
#
# Returns either fail or a list [s, stdGens, xis], where:
# - s is the isomorphism type, that is either the string "Sn" or "An".
# - stdGens are the standard generators of G. Identical to stdGensAn if G is
#   isomorphic to An
# - xis implicitly defines the isomorphism. It is used by FindImageSn and
#   FindImageAn to compute the isomorphism.
BindGlobal("ConstructSnAnIsomorphism",
function(ri, n, stdGensAn)
    local grp, xis, gImage, gensWithoutMemory, bWithoutMemory, hWithoutMemory, slp, eval, h, b, g;
    grp := GroupWithMemory(Grp(ri));
    gensWithoutMemory := StripMemory(stdGensAn);
    xis := ConstructXiAn(n, gensWithoutMemory[1], gensWithoutMemory[2]);
    for g in GeneratorsOfGroup(grp) do
        gImage := FindImageAn(ri, n, StripMemory(g), gensWithoutMemory[1],
                          gensWithoutMemory[2], xis[1], xis[2]);
        if gImage = fail then return fail; fi;
        if SignPerm(gImage) = -1 then
            # we found an odd permutation,
            # so the group cannot be An
            slp := RECOG.SLPforAn(n, (1,2) * gImage);
            eval:=ResultOfStraightLineProgram(slp, [stdGensAn[2], stdGensAn[1]]);
            h := eval * g ^ -1;
            if n mod 2 <> 0 then
                b := stdGensAn[1] * stdGensAn[2];
            else
                b := h * stdGensAn[1] * stdGensAn[2];
            fi;
            if SatisfiesSnPresentation(ri, n, b, h) then
                bWithoutMemory := StripMemory(b);
                hWithoutMemory := StripMemory(h);
                xis := ConstructXiSn(n, bWithoutMemory, hWithoutMemory);
                for g in GeneratorsOfGroup(grp) do
                    gImage := FindImageSn(ri, n, StripMemory(g), bWithoutMemory, hWithoutMemory, xis[1], xis[2]);
                    if gImage = fail then return fail; fi;
                    slp := RECOG.SLPforSn(n, gImage);
                    eval := ResultOfStraightLineProgram(slp, [h, b]);
                    if not isequal(ri)(eval, StripMemory(g)) then return fail; fi;
                od;
                return ["Sn", [b, h], xis];
            else
                return fail;
            fi;
        else
            slp := RECOG.SLPforAn(n, gImage);
            eval:=ResultOfStraightLineProgram(slp, [gensWithoutMemory[2], gensWithoutMemory[1]]);
            if not isequal(ri)(eval, StripMemory(g)) then return fail; fi;
        fi;
    od;

    return ["An", [stdGensAn[1], stdGensAn[2]], xis];
end);

# This method is an implementation of <Cite Key="JLNP13"/>. It is the main
# function of SnAnUnknownDegree.
#
# From <Cite Key="JLNP13" Where="Theorem 1.1"/>:
# RecogniseSnAn is a one-sided Monte-Carlo algorithm with the following
# properties. It takes as input a black-box group <A>G</A>, a natural number
# <A>N</A> and a real number <A>eps</A> with 0 < <A>eps</A> < 1. If <A>G</A> is
# isomorphic to An or Sn for some 9 <= <A>n</A> <= <A>N</A>, it returns with
# probability at least 1 - <A>eps</A> the degree <A>n</A> and an
# isomorphism from <A>G</A> to An or Sn.
BindGlobal("RecogniseSnAn",
function(ri, eps, N)
    local T, foundPreImagesOfStdGens, constants, iterator, c, tmp, isoData, i;
    T := Int(Ceil(Log2(1 / Float(eps))));
    foundPreImagesOfStdGens := false;
    constants := ThreeCycleCandidatesConstants(1. / 4., N);
    for i in [1 .. T] do
        iterator := ThreeCycleCandidatesIterator(ri, constants);
        c := iterator();
        while c <> fail do
            if c = NeverApplicable then return NeverApplicable; fi;
            tmp := ConstructLongCycle(ri, c, 1. / 8., N);
            if tmp = fail then
                c := iterator();
                continue;
            fi;
            # Now tmp contains [g, k] where
            #   g corresponds to a long cycle
            #   k is its length
            tmp := StandardGenerators(ri, tmp[1], c, tmp[2], 1. / 8., N);
            if tmp = fail then
                c := iterator();
                continue;
            fi;
            # Now tmp contains [g, c, n] where
            #   g, c correspond to standard generators of An
            isoData := ConstructSnAnIsomorphism(ri, tmp[3], tmp{[1,2]});
            if isoData = fail then continue; fi;
            Add(isoData, tmp[3]);
            return isoData;
        od;
    od;
    return TemporaryFailure;
end);

#! @BeginChunk SnAnUnknownDegree
#! This method tries to determine whether the input group given by <A>ri</A> is
#! isomorphic to a symmetric group Sn or alternating group An with
#! <M>9 \leq n</M>.
#! It is an implementation of <Cite Key="JLNP13"/>.
#!
#! @EndChunk
FindHomMethodsGeneric.SnAnUnknownDegree := function(ri)
    local G, N, isoData, degree, p, d;
    G := Grp(ri);
    # TODO find value for eps
    eps := 1 / 10^2;
    # Check magma
    if IsPermGroup(G) then
        # TODO: Can we assume that recognition of natural Sn and An came first? Can
        # we explicitly check that by checking ri!.fhmethsel?
        N := NrMovedPoints(G);
    elif IsMatrixGroup(G) then
        p := Characteristic(DefaultFieldOfMatrixGroup(G));
        d := DimensionOfMatrixGroup(G);
        # Let N be the largest integer such that A_N has a representation of
        # dimension d.
        if ri!.projective then
            # If n >= 9, then the smallest irreducible projective An-module has
            # dimension n-2, see [KL90], Proposition 5.3.7.
            # Assume N >= 9 and use the comment above to compute N. If we arrive at a
            # value < 9 for N, then we must have been in the case N < 9.
            # TODO: do we want to use the table for the other cases?
            N := Maximum(8, d + 2);
        else
            # If n >= 10, then the smallest irreducible An-module is the
            # fully deleted permutation module, see [KL90], Proposition 5.3.5.
            # It has dimension n-2 if p|n and dimension n-1 otherwise.
            # Assume N >= 10 and use the comment above to compute N. If we arrive at a
            # value < 10 for N, then we must have been in the case N < 10.
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
    # Try to find an isomorphism
    isoData := RecogniseSnAn(ri, eps, N);
    # RecogniseSnAn returned NeverApplicable or TemporaryFailure
    if not IsList(isoData) then
        return isoData;
    fi;
    ri!.SnAnUnknownDegreeIsoData := isoData;
    SetFilterObj(ri, IsLeaf);
    degree := isoData[4];
    if isoData[1] = "Sn" then
        SetSize(ri, Factorial(degree));
        SetIsRecogInfoForAlmostSimpleGroup(ri, true);
    else
        SetSize(ri, Factorial(degree) / 2);
        SetIsRecogInfoForSimpleGroup(ri, true);
    fi;
    # Note that when putting the generators into the record, we reverse
    # their order, such that it fits to the SLPforSn/SLPforAn function!
    Setslptonice(ri, SLPOfElms(Reversed(isoData[2])));
    isoData[2] := StripMemory(isoData[2]);
    SetNiceGens(ri, Reversed(isoData[2]));
    if isoData[1] = "Sn" then
        Setslpforelement(ri, SLPforElementFuncsGeneric.SnUnknownDegree);
    else
        Setslpforelement(ri, SLPforElementFuncsGeneric.AnUnknownDegree);
    fi;
    return Success;
end;

# The SLP function if G is isomorphic to Sn.
SLPforElementFuncsGeneric.SnUnknownDegree := function(ri, g)
    local isoData, degree, image;
    isoData := ri!.SnAnUnknownDegreeIsoData;
    degree := isoData[4];
    image := FindImageSn(ri, degree, g, isoData[2][1], isoData[2][2],
                       isoData[3][1], isoData[3][2]);
    return RECOG.SLPforSn(degree, image);
end;

# The SLP function if G is isomorphic to An.
SLPforElementFuncsGeneric.AnUnknownDegree := function(ri, g)
    local isoData, degree, image;
    isoData := ri!.SnAnUnknownDegreeIsoData;
    degree := isoData[4];
    image := FindImageAn(ri, degree, g, isoData[2][1], isoData[2][2],
                       isoData[3][1], isoData[3][2]);
    return RECOG.SLPforAn(degree, image);
end;
