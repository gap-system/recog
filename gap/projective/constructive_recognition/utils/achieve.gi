#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This files's authors include Daniel Rademacher, Max Neunhöffer, Ákos Seress.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
##
##  Constructive recognition of classical groups in their natural
##  representation.
##
#############################################################################


RECOG.ResetSLstd := function(r)
  r.left := One(r.a);
  r.right := One(r.a);
  if not IsBound(r.cache) then
      r.cache := [EmptyPlist(100),EmptyPlist(100),
                  List([1..r.ext],i->[]),     # rowopcache
                  List([1..r.ext],i->[])];    # colopcache
  fi;
  return r;
end;

# TODO: document the parameters
RECOG.InitSLstd := function(f,d,s,t,a,b)
  local r;
  r := rec( f := f, p := Characteristic(f), ext := DegreeOverPrimeField(f),
            q := Size(f), d := d, all := Concatenation(s,t,[a],[b]),
            one := One(f), One := One(s[1]), s := s, t := t, a := a, b := b );
  return RECOG.ResetSLstd(r);
end;

RECOG.FindFFCoeffs := function(r,lambda)
  return IntVecFFE(Coefficients(CanonicalBasis(r.f),lambda));
end;

# TODO: document this; what does "fake" mean????
# Theory: the fake gens are only used for their memory. Since we are only
# interested in the memory (to produce slps), we use trivial permutations for
# the underlying group elements, so that the multiplication is cheap.
# Verify and then document this.
RECOG.InitSLfake := function(f,d)
  local ext,l;
  ext := DegreeOverPrimeField(f);
  l := ListWithIdenticalEntries(2*ext+2,());
  l := GeneratorsWithMemory(l);
  return RECOG.InitSLstd(f,d,l{[1..ext]},l{[ext+1..2*ext]},
                         l[2*ext+1],l[2*ext+2]);
end;

RECOG.DoRowOp_SL := function(m,i,j,lambda,std)
  # add lambda times j-th row to i-th row, i<>j
  # by left-multiplying with an expression in the standard generators:
  #   a : e_n -> e_{n-1} -> ... -> e_1 -> (-1)^(n+1) e_n
  #   b : e_n -> e_{n-1} -> ... -> e_2 -> (-1)^n e_n and e_1 -> e_1
  #   s : e_1 -> e_1+ * e_2, e_i -> e_i   for i > 1
  #   t : e_2 -> e_1+ * e_2, e_i -> e_i   for i <> 2
  # s and t are lists of length ext to span over GF(p) all the scalars
  # in *.
  # Note that V_i = <e_1,...,e_i>.
  # So <s,t> is an SL_2 in the upper left corner, a is an n-cycle
  # b is an n-1 cycle with garbage fixing the first vector
  # This only modifies the record std collecting a straight line program.
  local Getai,Getbj,coeffs,k,new,newnew;

  Getai := function(l)
      local pos;
      if l < 0 then pos := std.d - l;
               else pos := l;
      fi;
      if not IsBound(std.cache[1][pos]) then
          std.cache[1][pos] := std.a^l;
      fi;
      return std.cache[1][pos];
  end;
  Getbj := function(l)
      local pos;
      if l < 0 then pos := std.d - l;
               else pos := l;
      fi;
      if not IsBound(std.cache[2][pos]) then
          std.cache[2][pos] := std.b^l;
      fi;
      return std.cache[2][pos];
  end;

  newnew := std.One;
  coeffs := RECOG.FindFFCoeffs(std,lambda);
  for k in [1..std.ext] do
      if not IsZero(coeffs[k]) then
          if IsBound(std.cache[3][k][i]) and
             IsBound(std.cache[3][k][i][j]) then
              new := std.cache[3][k][i][j];
          else;
              new := std.One;
              if i < j then
                  # We need to multiply from the left with the element
                  #    a^(i-1) * b^(j-i-1) * s_k * b^-(j-i-1) * a^-(i-1)
                  # from the left.
                  if i > 1 then new := Getai(-(i-1)) * new; fi;
                  if j > i+1 then new := Getbj(-(j-i-1)) * new; fi;
                  new := std.s[k] * new;
                  if j > i+1 then new := Getbj(j-i-1) * new; fi;
                  if i > 1 then new := Getai(i-1) * new; fi;
              elif i > j then
                  # We need to multiply from the left with the element
                  #    a^(j-1) * b^(i-j-1) * t_k * b^-(i-j-1) * a^-(j-1)
                  # from the left.
                  if j > 1 then new := Getai(-(j-1)) * new; fi;
                  if i > j+1 then new := Getbj(-(i-j-1)) * new; fi;
                  new := std.t[k] * new;
                  if i > j+1 then new := Getbj(i-j-1) * new; fi;
                  if j > 1 then new := Getai(j-1) * new; fi;
              fi;
              if not IsBound(std.cache[3][k][i]) then
                  std.cache[3][k][i] := [];
              fi;
              std.cache[3][k][i][j] := new;
          fi;
          std.left := new^coeffs[k] * std.left;
          newnew := new^coeffs[k] * newnew;
      fi;
  od;
  if m <> false and not IsZero(lambda) then m[i] := m[i] + m[j] * lambda; fi;
  return newnew;
end;

RECOG.DoColOp_SL := function(m,i,j,lambda,std)
  # add lambda times i-th column to j-th column, i<>j
  # by left-multiplying with an expression in the standard generators:
  #   a : e_n -> e_{n-1} -> ... -> e_1 -> (-1)^(n+1) e_n
  #   b : e_n -> e_{n-1} -> ... -> e_2 -> (-1)^n e_n and e_1 -> e_1
  #   s : e_1 -> e_1+ * e_2, e_i -> e_i   for i > 1
  #   t : e_2 -> e_1+ * e_2, e_i -> e_i   for i <> 2
  # s and t are lists of length ext to span over GF(p) all the scalars
  # in *.
  # Note that V_i = <e_1,...,e_i>.
  # So <s,t> is an SL_2 in the upper left corner, a is an n-cycle
  # b is an n-1 cycle with garbage fixing the first vector
  # This only modifies the record std collecting a straight line program.
  local Getai,Getbj,coeffs,k,new,newnew;

  Getai := function(l)
      local pos;
      if l < 0 then pos := std.d - l;
               else pos := l;
      fi;
      if not IsBound(std.cache[1][pos]) then
          std.cache[1][pos] := std.a^l;
      fi;
      return std.cache[1][pos];
  end;
  Getbj := function(l)
      local pos;
      if l < 0 then pos := std.d - l;
               else pos := l;
      fi;
      if not IsBound(std.cache[2][pos]) then
          std.cache[2][pos] := std.b^l;
      fi;
      return std.cache[2][pos];
  end;

  newnew := std.One;
  coeffs := RECOG.FindFFCoeffs(std,lambda);
  for k in [1..std.ext] do
      if not IsZero(coeffs[k]) then
          if IsBound(std.cache[4][k][i]) and
             IsBound(std.cache[4][k][i][j]) then
              new := std.cache[4][k][i][j];
          else;
              new := std.One;
              if i < j then
                  # We need to multiply from the right with the element
                  #    a^(i-1) * b^(j-i-1) * s_k * b^-(j-i-1) * a^-(i-1)
                  # from the right.
                  if i > 1 then new := Getai(-(i-1)) * new; fi;
                  if j > i+1 then new := Getbj(-(j-i-1)) * new; fi;
                  new := std.s[k] * new;
                  if j > i+1 then new := Getbj(j-i-1) * new; fi;
                  if i > 1 then new := Getai(i-1) * new; fi;
              elif i > j then
                  # We need to multiply from the right with the element
                  #    a^(j-1) * b^(i-j-1) * t_k * b^-(i-j-1) * a^-(j-1)
                  # from the left.
                  if j > 1 then new := Getai(-(j-1)) * new; fi;
                  if i > j+1 then new := Getbj(-(i-j-1)) * new; fi;
                  new := std.t[k] * new;
                  if i > j+1 then new := Getbj(i-j-1) * new; fi;
                  if j > 1 then new := Getai(j-1) * new; fi;
              fi;
              if not IsBound(std.cache[4][k][i]) then
                  std.cache[4][k][i] := [];
              fi;
              std.cache[4][k][i][j] := new;
          fi;
          std.right := std.right * new^coeffs[k];
          newnew := newnew * new^coeffs[k];
      fi;
  od;
  if m <> false and not IsZero(lambda) then
      for k in [1..Length(m)] do
          m[k][j] := m[k][j] + m[k][i] * lambda;
      od;
  fi;

  return newnew;
end;

RECOG.MakeSL_StdGens := function(p,ext,n,d)
  local a,b,f,i,q,s,t,x,res;
  f := GF(p,ext);
  q := Size(f);
  a := IdentityMat(d,f);
  a := a{Concatenation([n],[1..n-1],[n+1..d])};
  ConvertToMatrixRep(a,q);
  b := IdentityMat(d,f);
  b := b{Concatenation([1,n],[2..n-1],[n+1..d])};
  ConvertToMatrixRep(b,q);
  if IsEvenInt(n) then
      a[1] := -a[1];
  else
      b[2] := -b[2];
  fi;
  s := [];
  t := [];
  for i in [0..ext-1] do
      x := IdentityMat(d,f);
      x[1,2] := Z(p,ext)^i;
      Add(s,x);
      x := IdentityMat(d,f);
      x[2,1] := Z(p,ext)^i;
      Add(t,x);
  od;
  res := rec( s := s, t := t, a := a, b := b, f := f, q := q, p := p,
              ext := ext, One := IdentityMat(d,f), one := One(f),
              d := d );
  res.all := Concatenation( res.s, res.t, [res.a], [res.b] );
  return res;
end;

RECOG.ExpressInStd_SL2 := function(m,std)
  local mi;

  if IsObjWithMemory(m) then
      mi := InverseMutable(StripMemory(m));
  else
      mi := InverseMutable(m);
  fi;
  std.left := std.One;
  if not IsOne(mi[1,1]) then
      if IsZero(mi[2,1]) then
          RECOG.DoRowOp_SL(mi,2,1,std.one,std);
          # Now mi[2,1] is non-zero
      fi;
      RECOG.DoRowOp_SL(mi,1,2,(std.one-mi[1,1])/mi[2,1],std);
  fi;
  # Now mi[1,1] is equal to one
  if not IsZero(mi[2,1]) then
      RECOG.DoRowOp_SL(mi,2,1,-mi[2,1],std);
  fi;
  # Now mi[2,1] is equal to zero and thus mi[2,2] equal to one
  if not IsZero(mi[1,2]) then
      RECOG.DoRowOp_SL(mi,1,2,-mi[1,2],std);
  fi;
  # Now mi is the identity matrix, the element collected in std
  # is the one to multiply on the left hand side to transform mi to the
  # identity. Thus it is equal to m.
  return SLPOfElm(std.left);
end;

RECOG.ExpressInStd_SL := function(m,std)
  # m a matrix, std a fake standard generator record with trivial
  # generators with memory
  local d,i,j,mi,pos;

  if IsObjWithMemory(m) then
      mi := InverseMutable(StripMemory(m));
  else
      mi := InverseMutable(m);
  fi;
  std.left := std.One;
  d := Length(m);
  for i in [1..d] do
      if not IsOne(mi[i,i]) then
          pos := First([i+1..d],k->not IsZero(mi[k,i]));
          if pos = fail then
              pos := i+1;
              RECOG.DoRowOp_SL(mi,pos,i,std.one,std);
          fi;
          RECOG.DoRowOp_SL(mi,i,pos,(std.one-mi[i,i])/mi[pos,i],std);
      fi;
      # Now mi[i,i] is equal to one
      for j in Concatenation([1..i-1],[i+1..d]) do
          if not IsZero(mi[j,i]) then
              RECOG.DoRowOp_SL(mi,j,i,-mi[j,i],std);
          fi;
      od;
      # Now mi[i,i] is the only non-zero entry in the column
  od;
  # Now mi is the identity matrix, the element collected in std
  # is the one to multiply on the left hand side to transform mi to the
  # identity. Thus it is equal to m.
  return SLPOfElm(std.left);
end;



RECOG.RecogniseSL2NaturalEvenChar := function(g,f,torig)
  # f a finite field, g equal to SL(2,Size(f)), t either an involution
  # or false.
  # Returns a set of standard generators for SL_2 and the base change
  # to expose it. Works with memory. Uses PseudoRandom.
  local a,actpos,am,b,bas,bm,c,can,ch,cm,co,co2,el,ev,eva,evb,evbi,ext,gens,
        i,j,k,kk,mas,masi,mat,mati,mb,o,one,os,pos,q,res,s,ss,ssm,t,tb,tm,
        tt,ttm,u,v,x,xb,xm;

  q := Size(f);
  gens := GeneratorsOfGroup(g);
  if torig = false then
      for a in gens do
          if not IsOne(a) and IsOne(a^2) then
              torig := a;
              break;
          fi;
      od;
  fi;
  if torig = false then
    # if no involution t has been given, compute one, using Proposition 4 from
    # "Black box groups isomorphic to PGL(2,2^e)" by Kantor & Kassabov,
    # Journal of Algebra, 421 (2015) 16–26.
    repeat
        am:=PseudoRandom(g);
    until not IsOneProjective(am);
    k := Order(am);
    if IsEvenInt(k) then
        tm := am^(k/2);
    else
        # find a conjugate of a which does not commute with a.
        repeat
            bm := am^PseudoRandom(g);
            cm := am*bm;
            tm := bm*am;
        until cm<>tm;
        tm := tm^-1 * cm;
        if not IsOneProjective(StripMemory(tm)^2) then
            tm := cm^((q^2-2)/2) * am;
        fi;
    fi;
  else
      tm := torig;
  fi;
  t := StripMemory(tm);

  Assert(1, IsOne(t^2));

  ch := Factors(CharacteristicPolynomial(f,f,t,1));
  if Length(ch) <> 2 or ch[1] <> ch[2] then
      ErrorNoReturn("matrix is not triagonalizable - this should never happen!");
  fi;

  one := OneMutable(t);
  bas := MutableCopyMat(NullspaceMat(Value(ch[1],t)));
  Add(bas,one[1]);
  if RankMat(bas) < 2 then
      bas[2] := one[2];
  fi;
  tb := bas*t*bas^-1;
  can := CanonicalBasis(f);
  tt := [t];
  ttm := [tm];
  mat := [Coefficients(can,tb[2,1])];
  mb := MutableBasis(GF(2),mat);
  o := [gens[1]];
  os := [gens[1]];
  actpos := 1;
  j := 1;
  ext := DegreeOverPrimeField(f);
  while Length(tt) < ext do
      repeat
          repeat
              while j > Length(o) do
                  for k in gens do
                      kk := o[actpos]*k;
                      pos := PositionSorted(os,kk);
                      if pos > Length(os) or os[pos] <> kk then
                          Add(o,kk);
                          Add(os,kk,pos);
                      fi;
                  od;
                  actpos := actpos + 1;
              od;
              xm := o[j];
              j := j + 1;
              c := Comm(tm,xm);
          until not IsOne(c^2);
          xm := xm * c^(((q-1)*(q+1)-1)/2);
          x := StripMemory(xm);
          xb := bas*x*bas^-1;
          co := Coefficients(can,xb[2,1]);
      until not IsContainedInSpan(mb,co);
      CloseMutableBasis(mb,co);
      Add(tt,x);
      Add(ttm,xm);
      Add(mat,co);
  od;
  ConvertToMatrixRep(mat,2);
  mati := mat^-1;

  # Now we can add an arbitrary multiple of the first row to the
  # second and an arbitrary multiple of the second column to the first.
  # Therefore we quickly find other complimentary transvections:
  ss := [];
  ssm := [];
  mas := [];
  mb := MutableBasis(GF(2),mas,ZeroMutable(mat[1]));
  j := 1;
  while Length(ss) < ext do
      while true do   # will be left by break
          repeat
              while j > Length(o) do
                  for k in gens do
                      kk := o[actpos]*k;
                      pos := PositionSorted(os,kk);
                      if pos > Length(os) or os[pos] <> kk then
                          Add(o,kk);
                          Add(os,kk,pos);
                      fi;
                  od;
                  actpos := actpos + 1;
              od;
              xm := o[j];
              j := j + 1;
              x := MutableCopyMat(bas*StripMemory(xm)*bas^-1);
          until not IsZero(x[1,2]);

          if not IsOne(x[2,2]) then
              el := (One(f)-x[2,2])/x[1,2];
              co := Coefficients(can,el) * mati;
              for i in [1..Length(co)] do
                  if not IsZero(co[i]) then
                      xm := ttm[i] * xm;
                  fi;
              od;
              x[2] := x[2] + x[1] * el;
              if x <> bas*StripMemory(xm)*bas^-1 then
                # FIXME: sometimes triggered by RecognizeGroup(GL(2,16));
                ErrorNoReturn("!!!");
              fi;
          fi;
          # now x[2,2] is equal to One(f)
          # we postpone the actual computation of the final x until we
          # know it is needed:
          co := Coefficients(can,x[1,2]);
          if IsContainedInSpan(mb,co) then continue; fi;
          # OK, we need it, so let's make it:
          el := x[2,1];
          co2 := Coefficients(can,el) * mati;
          for i in [1..Length(co2)] do
              if not IsZero(co2[i]) then
                  xm := xm * ttm[i];
              fi;
          od;
# TODO: add sanity check here, too???
          x := StripMemory(xm);
          # now x[2,1] is equal to Zero(f) and thus x[1,1] is One(f) as well
          break;
      od;
      CloseMutableBasis(mb,co);
      Add(ss,x);
      Add(ssm,xm);
      Add(mas,co);
  od;
  ConvertToMatrixRep(mas,2);
  masi := mas^-1;

  # Now we replace all the s and the t by some products to get rid
  # of the base changes:
  s := EmptyPlist(ext);
  t := EmptyPlist(ext);
  for i in [1..ext] do
      co := Positions(masi[i],Z(2));
      Add(s,Product(ssm{co}));
      co := Positions(mati[i],Z(2));
      Add(t,Product(ttm{co}));
  od;

  res :=  rec( g := g, t := t, s := s, bas := bas, basi := bas^-1,
              one := One(f), a := s[1]*t[1]*s[1], b := One(s[1]),
              One := One(s[1]), f := f, q := q, p := 2, ext := ext,
              d := 2 );
  res.all := Concatenation(res.s,res.t,[res.a],[res.b]);
  return res;
end;

RECOG.GuessProjSL2ElmOrder := function(x,f)
  local facts,i,j,o,p,q,r,s,y,z;
  p := Characteristic(f);
  q := Size(f);
  if IsOneProjective(x) then return 1;
  elif IsEvenInt(p) and IsOneProjective(x^2) then return 2;
  fi;
  if p > 2 then
      y := x^p;
      if IsOneProjective(y) then
          return p;
      fi;
  fi;
  if IsOneProjective(x^(q-1)) then
      facts := Collected(FactInt(q-1:cheap)[1]);
      s := Product(facts,x->x[1]^x[2]);
      r := (q-1)/s;
  else
      facts := Collected(FactInt(q+1:cheap)[1]);
      s := Product(facts,x->x[1]^x[2]);
      r := (q+1)/s;
  fi;
  y := x^r;
  o := r;
  for i in [1..Length(facts)] do
      p := facts[i];
      j := p[2]-1;
      while j >= 0 do
          z := y^(s/p[1]^(p[2]-j));
          if not IsOneProjective(z) then break; fi;
          j := j - 1;
      od;
      o := o * p[1]^(j+1);
  od;
  return o;
end;

RECOG.IsThisSL2Natural := function(gens,f)
  # Checks quickly whether or not this is SL(2,f).
  # The answer is not guaranteed to be correct, this is Las Vegas.
  local CheckElm,a,b,clos,coms,i,isabelian,j,l,notA5,p,q,S,seenqm1,seenqp1,x;

  # The following method does not work for q <= 11, as then
  # the projective orders are either q+1, or else less than 5.
  # Hence seenqm1 never gets set.
  CheckElm := function(x)
      local o;
      o := RECOG.GuessProjSL2ElmOrder(x,f);
      if o in [1,2] then
          return false;
      fi;
      if o > 5 then
          if notA5 = false then Info(InfoRecog,4,"SL2: Group is not A5"); fi;
          notA5 := true;
          if seenqp1 and seenqm1 then
              return true;
          fi;
      fi;
      if o = p or o <= 5 then
          return false;
      fi;
      if (q+1) mod o = 0 then
          if not seenqp1 then
              Info(InfoRecog,4,"SL2: Found element of order dividing q+1.");
              seenqp1 := true;
              if seenqm1 and notA5 then
                  return true;
              fi;
          fi;
      else
          if not seenqm1 then
              Info(InfoRecog,4,"SL2: Found element of order dividing q-1.");
              seenqm1 := true;
              if seenqp1 and notA5 then
                  return true;
              fi;
          fi;
      fi;
      return false;
  end;

  if Length(gens) <= 1 then
      Info(InfoRecog,4,"SL2: Group cyclic");
      return false;
  fi;

  q := Size(f);
  p := Characteristic(f);
  # For small q, compute the order of the group via a stabilizer chain.
  # Note that at this point we are usually working projective, and thus
  # scalars are factored out "implicitly". Thus the generators we are
  # looking at may generate a group which only contains SL2 as a subgroup.
  if q <= 11 then    # this could be increased if needed
      Info(InfoRecog,4,"SL2: Computing stabiliser chain.");
      S := StabilizerChain(Group(gens));
      Info(InfoRecog,4,"SL2: size is ",Size(S));
      # return Size(S) mod (q*(q-1)*(q+1)) = 0;
      return Size(S) = (q*(q-1)*(q+1));
  fi;

  seenqp1 := false;
  seenqm1 := false;
  notA5 := false;

  for i in [1..Length(gens)] do
      if CheckElm(gens[i]) then
          return true;
      fi;
  od;
  CheckElm(gens[1]*gens[2]);
  if Length(gens) >= 3 then
      CheckElm(gens[1]*gens[3]);
      CheckElm(gens[2]*gens[3]);
  fi;

  # First we check the derived group:
  coms := EmptyPlist(20);
  l := Length(gens);
  if l <= 4 then
      Info(InfoRecog,4,"SL2: Computing commutators of gens...");
      for i in [1..l-1] do
          for j in [i+1..l] do
              x := Comm(gens[i],gens[j]);
              if CheckElm(x) then
                  return true;
              fi;
              Add(coms,x);
          od;
      od;
  else
      Info(InfoRecog,4,"SL2: Computing 6 random commutators...");
      for i in [1..6] do
          a := RECOG.RandomSubproduct(gens,rec());
          b := RECOG.RandomSubproduct(gens,rec());
          x := Comm(a,b);
          if CheckElm(x) then
              return true;
          fi;
          Add(coms,x);
      od;
  fi;
  if ForAll(coms,c->RECOG.IsScalarMat(c) <> false) then
      Info(InfoRecog,4,"SL2: Group is soluble, commutators are central");
      return false;
  fi;
  Info(InfoRecog,4,"SL2: Computing normal closure...");
  clos := FastNormalClosure(gens,coms,5);
  for i in [Length(coms)+1..Length(clos)] do
      if CheckElm(clos[i]) then
          return true;
      fi;
  od;
  if ForAll(clos{[Length(coms)+1..Length(clos)]},
            c->RECOG.IsScalarMat(c) <> false) then
      Info(InfoRecog,4,"SL2: Group is soluble, derived subgroup central");
      return false;
  fi;
  Info(InfoRecog,4,"SL2: Computing 6 random commutators...");
  isabelian := true;
  for i in [1..6] do
      a := RECOG.RandomSubproduct(clos,rec());
      b := RECOG.RandomSubproduct(clos,rec());
      x := Comm(a,b);
      if RECOG.IsScalarMat(x) = false then isabelian := false; break; fi;
  od;
  if isabelian then
      Info(InfoRecog,4,
           "SL2: Group is soluble, derived subgroup abelian mod scalars");
      return false;
  fi;

  # Now we know that the group is not dihedral!
  return false;
end;



# Now the code for writing SLPs:

SLPforElementFuncsProjective.PSL2 := function(ri,x)
  local det,log,slp,y,z,pos,s;
  ri!.fakegens.count := ri!.fakegens.count + 1;
  if ri!.fakegens.count > 1000 then
      ri!.fakegens := RECOG.InitSLfake(ri!.field,2);
      ri!.fakegens.count := 0;
  fi;
  y := ri!.nicebas * x * ri!.nicebasi;
  det := DeterminantMat(y);
  if not IsOne(det) then
      z := PrimitiveRoot(ri!.field);
      log := LogFFE(det,z);
      y := y * z^(-log*ri!.gcd.coeff1/ri!.gcd.gcd);
  fi;
  # At this point, y has determinant 1; but we consider it modulo scalars.
  # To make sure that different coset reps behave the same, we scale it
  # with a suitable primitive d-th root of unity.
  if not IsBound(ri!.normlist) then
      ri!.normlist := RECOG.SetupNormalisationListForPSLd(ri!.field,
                                                          ri!.gcd.gcd);
  fi;
  pos := PositionNonZero(y[1]);
  s := RECOG.NormaliseScalarForPSLd(y[1,pos],ri!.normlist);
  slp := RECOG.ExpressInStd_SL2(s * y,ri!.fakegens);
  return slp;
end;

# s: a non-zero scalar
# list: a list of certain primitive roots of unity, as
#       computed by SetupNormalisationListForPSLd
#
# This function considers s and all its multiples by the elements in
# list, and picks the smallest of them. It returns the multiplicator
# used to obtain that element from s.
RECOG.NormaliseScalarForPSLd := function(s,list)
  local min,minmul,t,u;
  min := s;
  minmul := s^0;
  for t in list do
      u := s*t;
      if u < min then
          min := u;
          minmul := t;
      fi;
  od;
  return minmul;
end;

# f: a finite field
# d: a positive integer
#
# Returns a list of primitive d-th roots of unity.
RECOG.SetupNormalisationListForPSLd := function(f,d)
  local e,i,list,z;
  list := EmptyPlist(d);
  z := PrimitiveRoot(f)^((Size(f)-1)/d);
  e := z;
  for i in [1..d-1] do
      Add(list,e);
      e := e * z;
  od;
  return list;
end;

# el: a field element
# d: a positive integer (typically ri!.gcd.gcd)
# f: a galois field (typically ri!.field)
#
# Compute a primitive d-th root of el in the field f.
# TODO: This function copies the code from RootFFE, which will
# appear in GAP 4.9. Once GAP 4.9 is out, we can switch
# to using RootFFE directly.
RECOG.ComputeRootInFiniteField := function(el, d, f)
    local z, e, m, p, a;
    if IsZero(el) or IsOne(el)  then
        return el;
    fi;
    z := PrimitiveRoot(f);
    m := Size(f) - 1;
    e := LogFFE(el, z);
    p := GcdInt(m, e);
    d := d mod m;
    a := GcdInt(m, d);
    if p mod a <> 0  then
        return fail;
    fi;
    a := e * (a / d mod (m / p)) / a mod m;
    return z ^ a;
end;

# Express an element of PSL_d as an slp in terms of standard generators.
SLPforElementFuncsProjective.PSLd := function(ri,x)
  local det,pos,root,s,slp,y;
  ri!.fakegens.count := ri!.fakegens.count + 1;
  if ri!.fakegens.count > 1000 then
      ri!.fakegens := RECOG.InitSLfake(ri!.field,ri!.dimension);
      ri!.fakegens.count := 0;
  fi;
  y := ri!.nicebas * x * ri!.nicebasi;
  det := DeterminantMat(y);
  if not IsOne(det) then
      # At this point, y is in the kernel of the determinant map *mod scalars*.
      # That means that det may not be 1 -- it can be any d-th power.
      # We thus can compute a d-th root of 1/det, and scale y with it,
      # in order to obtain a matrix with determinant 1 in the same
      # projective class.
      root := RECOG.ComputeRootInFiniteField(1/det,Length(y),ri!.field);
      if root = fail then
          return fail;
      fi;
      y := y * root;
  fi;
  # At this point, y has determinant 1; but we consider it modulo scalars.
  # To make sure that different coset reps behave the same, we scale it
  # with a suitable primitive d-th root of unity.
  if not IsBound(ri!.normlist) then
      ri!.normlist := RECOG.SetupNormalisationListForPSLd(ri!.field,
                                                          ri!.gcd.gcd);
  fi;
  pos := PositionNonZero(y[1]);
  s := RECOG.NormaliseScalarForPSLd(y[1,pos],ri!.normlist);
  slp := RECOG.ExpressInStd_SL(s * y,ri!.fakegens);
  return slp;
end;

#! @BeginChunk ClassicalNatural
#! TODO
#! @EndChunk
BindRecogMethod(FindHomMethodsProjective, "ClassicalNatural",
"check whether it is a classical group in its natural representation",
function(ri, g)
  local changed,classical,d,det,ext,f,gcd,gens,gm,i,p,pr,q,root,std,stdg,z;
  d := ri!.dimension;
  f := ri!.field;
  q := Size(f);
  p := Characteristic(f);
  RECOG.SetPseudoRandomStamp(g,"ClassicalNatural");

  # First check whether we are applicable:
  if d = 2 then
      if not RECOG.IsThisSL2Natural(GeneratorsOfGroup(g),f) then
          Info(InfoRecog,2,"ClassicalNatural: Is not PSL_2.");
          return fail; # FIXME: fail = TemporaryFailure here really correct?
      fi;
  else
      classical := RecogniseClassical(g);
      if classical.isSLContained <> true then
          Info(InfoRecog,2,"ClassicalNatural: Is not PSL.");
          return fail; # FIXME: fail = TemporaryFailure here really correct?
      fi;
  fi;

  # Now get rid of nasty determinants:
  gens := ShallowCopy(GeneratorsOfGroup(g));
  changed := false;
  z := Z(q);
  gcd := Gcdex(d,q-1);
  for i in [1..Length(gens)] do
      det := DeterminantMat(gens[i]);
      if not IsOne(det) then
          root := RECOG.ComputeRootInFiniteField(det,gcd.gcd,f);
          if root = fail then
              ErrorNoReturn("Should not have happened, 15634, tell Max!");
          fi;
          gens[i] := gens[i] * root;
          changed := true;
      fi;
  od;
  if changed then
      gm := GroupWithMemory(gens);
      pr := ProductReplacer(GeneratorsOfGroup(gm),rec(maxdepth := 500));
      gm!.pseudorandomfunc := [rec( func := Next, args := [pr] )];
  else
      gm := Group(ri!.gensHmem);
      gm!.pseudorandomfunc := [rec(func := function(ri,name,bool)
                                      return RandomElm(ri,name,bool).el;
                                    end,
                            args := [ri,"ClassicalNatural",true])];
  fi;

  if d = 2 then
      # We only have to check for (P)SL_2 since otherwise the subfield
      # method will detect it. Note that this is a projective method,
      # but a projective group contains PSL_2 if and only if the matrix
      # group generated by the same matrices (possibly scaled to make
      # the determinant to be 1) contains SL_2.

      # This is (P)SL2, lets set up the recognition:
      Info(InfoRecog,2,"ClassicalNatural: this is PSL_2!");
      if IsEvenInt(q) then
          std := RECOG.RecogniseSL2NaturalEvenChar(gm,f,false);
          ri!.comment := "PSL2Even";
      else
          std := RECOG.RecogniseSL2NaturalOddCharUsingBSGS(gm,f);
          ri!.comment := "PSL2Odd";
      fi;
      Setslptonice(ri,SLPOfElms(std.all));
      ri!.nicebas := std.bas;
      ri!.nicebasi := std.basi;
      SetNiceGens(ri,List(StripMemory(std.all),x->std.basi*x*std.bas));
      ri!.fakegens := RECOG.InitSLfake(f,2);
      ri!.fakegens.count := 0;
      ri!.gcd := gcd;
      SetFilterObj(ri,IsLeaf);
      SetSize(ri,(q+1)*(q-1)*q/GcdInt(2,q-1));
      SetIsRecogInfoForSimpleGroup(ri, q>3);
      Setslpforelement(ri,SLPforElementFuncsProjective.PSL2);
      return Success;
  else   # bigger than 2:
      if classical.isSLContained = true then
          # Do not run the generic code in small cases:
          if (q^d-1)/(q-1) <= 1000 or d = 3 then
              # FIXME: Note d=3 currently has a problem in the SL2-finder.
              Info(InfoRecog,2,"Classical natural: SL(",d,",",q,"): small ",
                   "case, handing over to Schreier-Sims.");
              ri!.comment := Concatenation("SL(",String(d),",",String(q),")",
                                           "_StabilizerChain");
              return FindHomMethodsProjective.StabilizerChainProj(ri,g);
          fi;
          Info(InfoRecog,2,"ClassicalNatural: this is PSL_n!");
          std := RECOG.FindStdGens_SL(gm);
          Setslptonice(ri,std.slpstd);
          ri!.nicebas := std.bas;
          ri!.nicebasi := std.basi;
          ext := DegreeOverPrimeField(f);
          stdg := RECOG.MakeSL_StdGens(p,ext,d,d);
          SetNiceGens(ri,List(StripMemory(stdg.all),
                      x->std.basi*x*std.bas));
          ri!.fakegens := RECOG.InitSLfake(f,d);
          ri!.fakegens.count := 0;
          ri!.comment := "PSLd";
          ri!.gcd := gcd;
          SetFilterObj(ri,IsLeaf);
          SetSize(ri,Product([0..d-1],i->(q^d-q^i))/((q-1)*gcd.gcd));
          SetIsRecogInfoForSimpleGroup(ri,true);
          Setslpforelement(ri,SLPforElementFuncsProjective.PSLd);
          return Success;
      fi;
  fi;

  return fail; # FIXME: fail = TemporaryFailure here really correct?

end);
