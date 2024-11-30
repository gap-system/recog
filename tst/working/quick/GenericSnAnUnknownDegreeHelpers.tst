# RECOG.IsFixedPoint
gap> ri := RecogNode(SymmetricGroup(10));;
gap> g := (1,2,3,4,5,6,7,8);;
gap> c := (1,2,3);;
gap> r := (1,2)(4,5,6);;
gap> RECOG.IsFixedPoint(ri, g,c,r);
true
gap> r := (2,3,4);;
gap> RECOG.IsFixedPoint(ri, g,c,r);
false

# RECOG.AdjustCycle
gap> ri := RecogNode(SymmetricGroup(10));;
gap> g := (1,2,3,4,5,6,7,8);;
gap> c := (1,2,3);;
gap> r := (4,5);;
gap> RECOG.AdjustCycle(ri, g, c, r, 8);
(3,5)
gap> r := (3,4,5);;
gap> RECOG.AdjustCycle(ri, g, c, r, 8);
(3,4,5)
gap> r := (2,5);;
gap> RECOG.AdjustCycle(ri, g, c, r, 8);
(3,5)
gap> r := (2,4,5);;
gap> RECOG.AdjustCycle(ri, g, c, r, 8);
(3,5,4)
gap> r := (2,3,5);;
gap> RECOG.AdjustCycle(ri, g, c, r, 8);
(3,4,5)
gap> r := (1,5);;
gap> RECOG.AdjustCycle(ri, g, c, r, 8);
(3,5)
gap> r := (1,4,5);;
gap> RECOG.AdjustCycle(ri, g, c, r, 8);
(3,5,4)
gap> r := (1,3,4,5);;
gap> RECOG.AdjustCycle(ri, g, c, r, 8);
(3,6,4,5)
gap> r := (1,2,5);;
gap> RECOG.AdjustCycle(ri, g, c, r, 8);
(3,5,4)
gap> r := (1,2,3,5);;
gap> RECOG.AdjustCycle(ri, g, c, r, 8);
(3,5,4,6)

# RECOG.BuildCycle
gap> ri := RecogNode(SymmetricGroup(10));;

# c = (u,v,w)
gap> c := (1,2,3);;

# Form 1: x = (v,a_1,...,a_alpha) * (w,b_1,....,b_beta) * (...)
# alpha - beta = 0
gap> x := (2,4,5,6)* (3,7,8,9);;
gap> RECOG.BuildCycle(ri, c, x, 10);
[ (1,2,3,4,7,5,8,6,9), 9 ]

# alpha - beta = -1
gap> x := (2,4,5,6)* (3,7,8,9,10);;
gap> RECOG.BuildCycle(ri, c, x, 10);
[ (1,2,3,4,7,5,8,6,9), 9 ]

# alpha - beta = 1
gap> x := (2,4,5,6,10)* (3,7,8,9);;
gap> RECOG.BuildCycle(ri, c, x, 10);
[ (1,2,3,4,7,5,8,6,9), 9 ]

# alpha - beta = -2
gap> x := (2,4,5) * (3,7,8,9,10);;
gap> RECOG.BuildCycle(ri, c, x, 10);
[ (1,2,3,4,7,5,8,10,9), 9 ]

# alpha - beta = 2
gap> x := (2,4,5,6,10) * (3,7,8);;
gap> RECOG.BuildCycle(ri, c, x, 10);
[ (1,2,3,4,7,5,8,6,10), 9 ]

# Form 2: x = (v,a_1,...,a_alpha,w,b_1,....,b_beta) * (...)
# alpha - beta = 0
gap> x := (2,4,5,6,3,7,8,9);;
gap> RECOG.BuildCycle(ri, c, x, 10);
[ (1,2,3,4,7,5,8,6,9), 9 ]

# alpha - beta = -1
gap> x := (2,4,5,6,3,7,8,9,10);;
gap> RECOG.BuildCycle(ri, c, x, 10);
[ (1,2,3,4,7,5,8,6,9), 9 ]

# alpha - beta = 1
gap> x := (2,4,5,6,10,3,7,8,9);;
gap> RECOG.BuildCycle(ri, c, x, 10);
[ (1,2,3,4,7,5,8,6,9), 9 ]

# alpha - beta = -2
gap> x := (2,4,5,3,7,8,9,10);;
gap> RECOG.BuildCycle(ri, c, x, 10);
[ (1,2,3,4,7,5,8,10,9), 9 ]

# alpha - beta = 2
gap> x := (2,4,5,6,10,3,7,8);;
gap> RECOG.BuildCycle(ri, c, x, 10);
[ (1,2,3,4,7,5,8,6,10), 9 ]
