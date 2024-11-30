#############################################################################
# BruhatDecompositionSU.gd
#############################################################################
#############################################################################
##
##  BruhatDecomposition package
##
##    Daniel Rademacher, RWTH Aachen University
##    Alice Niemeyer, RWTH Aachen University
##
## Licensed under the GPL 3 or later.
##
#############################################################################

#! @Chapter Special Unitary Group
#! @ChapterLabel SpecialUnitaryGroup
#!
#! This chapter deals with the special unitary group

#! @Section Introduction and Quick Start of functions for SU
#! @SectionLabel LabelIntroductionAndQuickStartSU
#!
#! TODO






#! @Section Functions for SU
#! @SectionLabel LabelFunctionsSU

####################
# PART I - a)
#    Originally implemented subfunctions
####################

InfoBruhat := NewInfoClass("InfoBruhat");;
SetInfoLevel( InfoBruhat, 2 );

#####
# MakePermutationMat()
#####

#! @Arguments perm dim fld
#! @Returns The permutation matrix of perm over <M>M_{d x d}(fld)</M> (ie <M>res_{i,j} = One(fld)</M> if <M>i^{perm} = j</M>)
#! @Description
#! perm: A permutation, <M>\newline</M>
#! dim: A natural number, <M>\newline</M>
#! fld: A field <M>\newline</M>
#! This is the same function as MyPermutationMat.
DeclareGlobalFunction( "MakePermutationMat" );



#####
# LGOStandardGensSU
#####

#! @Arguments d q
#! @Returns stdgens (the LGO standard-generators of SU<M>(d,q)</M>)
#! @Description
#! <M>d</M>: The dimension of our matrix. <M>\newline</M>
#! <M>q</M>: A prime power <M>q = p^f</M>, where <M>F_q</M> ist the field whereover the matrices are defined <M>\newline</M>
#! This function computes the standard generators of SU
#! as given by C. R. Leedham-Green and E. A. O'Brien in
#! "Constructive Recognition of Classical Groups in odd characteristic". If q is even, <C>LGOStandardGensSUEvenChar(d,q)</C> is called automatically.
DeclareGlobalFunction( "LGOStandardGensSU" );



#####
# LGOStandardGensSUEvenChar
#####

#! @Arguments d q
#! @Returns stdgens (the LGO standard-generators of SU<M>(d,q)</M>) for q even
#! @Description
#! <M>d</M>: The dimension of our matrix. <M>\newline</M>
#! <M>q</M>: A 2 power <M>q = 2^f</M>, where <M>F_q</M> ist the field whereover the matrices are defined <M>\newline</M>
#! This function computes the standard generators of Sp
#! as given by C. R. Leedham-Green and E. A. O'Brien in
#! "Constructive Recognition of Classical Groups in even characteristic"
DeclareGlobalFunction( "LGOStandardGensSUEvenChar" );



#####
#   CoefficientsPrimitiveElementS
#####

#! @Arguments fld, alpha, basis
#! @Returns Coefficients (A vector c sth alpha = sum c[i] b[i])
#! @Description
#! fld: A field, <M>\newline</M>
#! alpha: An element of fld <M>\newline</M>
#! basis: A <M>F_p</M> basis of fld <M>\newline</M>
#! It expresses an element alpha in a field fld as
#! a linear combination of the basis elements.
DeclareGlobalFunction( "CoefficientsPrimitiveElementS" );



####################
# PART II - a)
#    UnipotentDecomposition and Transvections
####################

#####
# UnitriangularDecompositionSUEven
#####

#! @Arguments stdgens g
#! @Returns slp (A list of instructions yielding <M>u_1,u_2</M> if evaluated as SLP), <M>[u_1,g,u_2]</M> (The matrices of the Bruhat-Decomposition)
#! @Description
#! stdgens: The LGO standard-generators <M>\newline</M>
#! g: A matrix in SU(<M>d,q</M>) where d is even and q is odd <M>\newline</M>
#! Computes the Unitriangular decomposition of the matrix <M>g</M>.
DeclareGlobalFunction( "UnitriangularDecompositionSUEven" );



#####
# UnitriangularDecompositionSUEvenAndEvenChar
#####

#! @Arguments stdgens g
#! @Returns slp (A list of instructions yielding <M>u_1,u_2</M> if evaluated as SLP), <M>[u_1,g,u_2]</M> (The matrices of the Bruhat-Decomposition)
#! @Description
#! stdgens: The LGO standard-generators <M>\newline</M>
#! g: A matrix in SU(<M>d,q</M>) where d is even and q is even <M>\newline</M>
#! Computes the Unitriangular decomposition of the matrix <M>g</M>.
DeclareGlobalFunction( "UnitriangularDecompositionSUEvenAndEvenChar" );



#####
# UnitriangularDecompositionSUOdd
#####

#! @Arguments stdgens g
#! @Returns slp (A list of instructions yielding <M>u_1,u_2</M> if evaluated as SLP), <M>[u_1,g,u_2]</M> (The matrices of the Bruhat-Decomposition)
#! @Description
#! stdgens: The LGO standard-generators <M>\newline</M>
#! g: A matrix in SU(<M>d,q</M>) where d is odd and q is odd <M>\newline</M>
#! Computes the Unitriangular decomposition of the matrix <M>g</M>.
DeclareGlobalFunction( "UnitriangularDecompositionSUOdd" );



#####
# UnitriangularDecompositionSUOddAndEvenChar
#####

#! @Arguments stdgens g
#! @Returns slp (A list of instructions yielding <M>u_1,u_2</M> if evaluated as SLP), <M>[u_1,g,u_2]</M> (The matrices of the Bruhat-Decomposition)
#! @Description
#! stdgens: The LGO standard-generators <M>\newline</M>
#! g: A matrix in SU(<M>d,q</M>) where d is odd and q is even <M>\newline</M>
#! Computes the Unitriangular decomposition of the matrix <M>g</M>.
DeclareGlobalFunction( "UnitriangularDecompositionSUOddAndEvenChar" );



#####
# UnitriangularDecompositionSU
#####

#! @Arguments stdgens g
#! @Returns slp (A list of instructions yielding <M>u_1,u_2</M> if evaluated as SLP), <M>[u_1,g,u_2]</M> (The matrices of the Bruhat-Decomposition)
#! @Description
#! stdgens: The LGO standard-generators <M>\newline</M>
#! g: A matrix in SU(<M>d,q</M>) <M>\newline</M>
#! Computes the Unitriangular decomposition of the matrix <M>g</M>. Depending on q and d the correct function of <C>UnitriangularDecompositionSUEven</C>, <C>UnitriangularDecompositionSUOdd</C> and <C>UnitriangularDecompositionSUOdd</C> is choosen.
DeclareGlobalFunction( "UnitriangularDecompositionSU" );



#####################
# PART III
#    Decomposition of Permutation and Diagonal-Matrix
####################

#####
#   MonomialSLPSUOdd
#####

#! @Arguments stdgens mat slp
#! @Returns slp (A list of instructions to evaluate tmpvalue. If slp is also given as input then this instructions are added to slp), [tmpvalue,diag] (tmpvalue is a monomial matix such that tmpvalue*mat = diag where diag is a diagonal matrix)
#! @Description
#! stdgens: The LGO standard-generators <M>\newline</M>
#! mat: A monomial matrix (ie <M>w</M>) in SU<M>(d,q)</M> with <M>d</M> odd and <M>q</M> odd <M>\newline</M>
#! slp: An already existing list of instructions *optional <M>\newline</M>
#! In this function we will transform a monomial matrix <M>mat \in</M> SU<M>(d,q)</M> with <M>d</M> even and <M>q</M> odd into
#! a diagonal matrix diag. Using only the standard-generators <M>s,u,v</M> this
#! will lead to a monomial matrix tmpvalue
#! and <M>tmpvalue^{-1} \cdot diag = mat</M> (i.e. diag = tmpvalue*mat ).
#! Furthermore we will return list slp of instructions which will
#! (when evaluated at the LGO standard-generators) yields diag.
DeclareGlobalFunction( "MonomialSLPSUOdd" );



#####
#   MonomialSLPSUOddAndEvenChar
#####

#! @Arguments stdgens mat slp
#! @Returns slp (A list of instructions to evaluate tmpvalue. If slp is also given as input then this instructions are added to slp), [tmpvalue,diag] (tmpvalue is a monomial matix such that tmpvalue*mat = diag where diag is a diagonal matrix)
#! @Description
#! stdgens: The LGO standard-generators <M>\newline</M>
#! mat: A monomial matrix (ie <M>w</M>) in SU<M>(d,q)</M> with <M>d</M> odd and <M>q</M> even <M>\newline</M>
#! slp: An already existing list of instructions *optional <M>\newline</M>
#! In this function we will transform a monomial matrix <M>mat \in</M> SU<M>(d,q)</M> with <M>d</M> even and <M>q</M> odd into
#! a diagonal matrix diag. Using only the standard-generators <M>s,u,v</M> this
#! will lead to a monomial matrix tmpvalue
#! and <M>tmpvalue^{-1} \cdot diag = mat</M> (i.e. diag = tmpvalue*mat ).
#! Furthermore we will return list slp of instructions which will
#! (when evaluated at the LGO standard-generators) yields diag.
DeclareGlobalFunction( "MonomialSLPSUOddAndEvenChar" );



#####
#   MonomialSLPSUEvenAndEvenChar
#####

#! @Arguments stdgens mat slp
#! @Returns slp (A list of instructions to evaluate tmpvalue. If slp is also given as input then this instructions are added to slp), [tmpvalue,diag] (tmpvalue is a monomial matix such that tmpvalue*mat = diag where diag is a diagonal matrix)
#! @Description
#! stdgens: The LGO standard-generators <M>\newline</M>
#! mat: A monomial matrix (ie <M>w</M>) in SU<M>(d,q)</M> with <M>d</M> even and <M>q</M> even <M>\newline</M>
#! slp: An already existing list of instructions *optional <M>\newline</M>
#! In this function we will transform a monomial matrix <M>mat \in</M> SU<M>(d,q)</M> with <M>d</M> even and <M>q</M> even into
#! a diagonal matrix diag. Using only the standard-generators <M>s,u,v</M> this
#! will lead to a monomial matrix tmpvalue
#! and <M>tmpvalue^{-1} \cdot diag = mat</M> (i.e. diag = tmpvalue*mat ).
#! Furthermore we will return list slp of instructions which will
#! (when evaluated at the LGO standard-generators) yields diag.
DeclareGlobalFunction( "MonomialSLPSUEvenAndEvenChar" );



#####
#   MonomialSLPSUEven
#####

#! @Arguments stdgens mat slp
#! @Returns slp (A list of instructions to evaluate tmpvalue. If slp is also given as input then this instructions are added to slp), [tmpvalue,diag] (tmpvalue is a monomial matix such that tmpvalue*mat = diag where diag is a diagonal matrix)
#! @Description
#! stdgens: The LGO standard-generators <M>\newline</M>
#! mat: A monomial matrix (ie <M>w</M>) in SU<M>(d,q)</M> with <M>d</M> even and <M>q</M> odd <M>\newline</M>
#! slp: An already existing list of instructions *optional <M>\newline</M>
#! In this function we will transform a monomial matrix <M>mat \in</M> SU<M>(d,q)</M> with <M>d</M> odd and <M>q</M> odd into
#! a diagonal matrix diag. Using only the standard-generators <M>s,u,v</M> this
#! will lead to a monomial matrix tmpvalue
#! and <M>tmpvalue^{-1} \cdot diag = mat</M> (i.e. diag = tmpvalue*mat ).
#! Furthermore we will return list slp of instructions which will
#! (when evaluated at the LGO standard-generators) yields diag.
DeclareGlobalFunction( "MonomialSLPSUEven" );



#####
#   CheckContinue
#####

#! @Arguments perm m
#! @Returns True or false
#! @Description
#! perm: A permutation <M>\newline</M>
#! m: A natural number. If this function is called by <C>MonomialSLPSU</C> then <M>m = \frac{d}{2}</M> or <M>m = \frac{(d-1)}{2}</M> <M>\newline</M>
#! This is a help function for <C>MonomialSLPSU</C>. This function checks whether for all cycle c of perm holds: LargestMovedPoint(c) <M>\leq</M> m or SmallestMovedPoint(c) &gt; m.
#! Notice that this is the condition for the main loop of <C>MonomialSLPSU</C>.
DeclareGlobalFunction( "CheckContinue" );



#####
#   CycleFromPermutation
#####

#! @Arguments g
#! @Returns List of permutations
#! @Description
#! g: A permutation <M>\newline</M>
#! This is a help function for <C>MonomialSLPSUOdd</C>. This function computes the cycles of g and stores them in the output list.
DeclareGlobalFunction( "CycleFromPermutation" );



#####
#   CycleFromListMine
#####

#! @Arguments nc h
#! @Returns TODO
#! @Description
#! nc: A subset of [1,...,h] <M>\newline</M>
#! h: A natural number (the largest moved point of a permutation) <M>\newline</M>
#! This is a help function for <C>CycleFromPermutation</C>. This function computes a cycle in Sym_h which corresponds to nc.
DeclareGlobalFunction( "CycleFromListMine" );



#####
#   DiagSLPSUOdd
#####

#! @Arguments stdgens diag slp
#! @Returns slp (A list of instructions to evaluate diag if slp was Input then this instructions are added to slp)
#! @Description
#! stdgens: The LGO standard-generators <M>\newline</M>
#! diag: A diagonal matrix (eg diag) in SU<M>(d,q)</M> with <M>d</M> odd and <M>q</M> odd <M>\newline</M>
#! slp: An already existing list of instructions *optional <M>\newline</M>
#! Writes a list of instructions which evaluated with LGO standard-generators
#! yield the diagonal matrix of the input.
DeclareGlobalFunction( "DiagSLPSUOdd" );



#####
#   DiagSLPSUOddAndEvenChar
#####

#! @Arguments stdgens diag slp
#! @Returns slp (A list of instructions to evaluate diag if slp was Input then this instructions are added to slp)
#! @Description
#! stdgens: The LGO standard-generators <M>\newline</M>
#! diag: A diagonal matrix (eg diag) in SU<M>(d,q)</M> with <M>d</M> odd and <M>q</M> even <M>\newline</M>
#! slp: An already existing list of instructions *optional <M>\newline</M>
#! Writes a list of instructions which evaluated with LGO standard-generators
#! yield the diagonal matrix of the input.
DeclareGlobalFunction( "DiagSLPSUOddAndEvenChar" );




#####
#   DiagSLPSU
#####

#! @Arguments stdgens diag slp
#! @Returns slp (A list of instructions to evaluate diag if slp was Input then this instructions are added to slp)
#! @Description
#! stdgens: The LGO standard-generators <M>\newline</M>
#! diag: A diagonal matrix (eg diag) in SU<M>(d,q)</M> <M>\newline</M>
#! slp: An already existing list of instructions *optional <M>\newline</M>
#! Writes a list of instructions which evaluated with LGO standard-generators
#! yield the diagonal matrix of the input. Depending on q and d the correct function of <C>DiagSLPSUEven</C>, <C>DiagSLPSUEvenAndEvenChar</C> and <C>DiagSLPSUOdd</C> is choosen.
DeclareGlobalFunction( "DiagSLPSU" );




#####
#   DiagSLPSUEven
#####

#! @Arguments stdgens diag slp
#! @Returns slp (A list of instructions to evaluate diag if slp was Input then this instructions are added to slp)
#! @Description
#! stdgens: The LGO standard-generators <M>\newline</M>
#! diag: A diagonal matrix (eg diag) in SU<M>(d,q)</M> with <M>d</M> even and <M>q</M> odd <M>\newline</M>
#! slp: An already existing list of instructions *optional <M>\newline</M>
#! Writes a list of instructions which evaluated with LGO standard-generators
#! yield the diagonal matrix of the input.
DeclareGlobalFunction( "DiagSLPSUEven" );



#####
#   DiagSLPSUEvenAndEvenChar
#####

#! @Arguments stdgens diag slp
#! @Returns slp (A list of instructions to evaluate diag if slp was Input then this instructions are added to slp)
#! @Description
#! stdgens: The LGO standard-generators <M>\newline</M>
#! diag: A diagonal matrix (eg diag) in SU<M>(d,q)</M> with <M>d</M> even and <M>q</M> even <M>\newline</M>
#! slp: An already existing list of instructions *optional <M>\newline</M>
#! Writes a list of instructions which evaluated with LGO standard-generators
#! yield the diagonal matrix of the input.
DeclareGlobalFunction( "DiagSLPSUEvenAndEvenChar" );



####################
# PART IV
#    Main Functions. Constructs slp for the StraightLineProgram
#####################

#####
#   BruhatDecompositionSU
#####

#! @Arguments stdgens g
#! @Returns pgr (A SLP to compute <M>u_1,u_2,p_{sign}</M> and <M>diag</M> and the matrices <M>u_1, u_2, p_{sign}</M> and <M>diag</M> itself.)
#! @Description
#! stdgens: The LGO standard-generators <M> \newline </M>
#! g: A matrix in SU<M>(d,q)</M> <M> \newline </M>
#! Uses <C>UnitriangularDecompositionSU()</C>, <C>MonomialSLPSU()</C> and <C>DiagSLPSU()</C>
#! to write a matrix <M>g \in</M> SU<M>(d,q)</M> as <M>g = u_1^{-1} \cdot p_{sign} \cdot diag \cdot u_2^{-1}</M>
#! where <M>u_1,u_2</M> are lower unitriangular matrices, <M>p_{sign}</M> is a monomial matrix and <M>diag</M> a diagonal matrix.
#! It furthermore yields an SLP that returns the above matrices if evaluated
#! with the LGO standard-generators.
DeclareGlobalFunction( "BruhatDecompositionSU" );
