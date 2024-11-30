#############################################################################
# BruhatDecompositionSp.gd
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

#! @Chapter Symplectic Group
#! @ChapterLabel SymplecticGroup
#!
#! This chapter deals with the symplectic group

#! @Section Introduction and Quick Start of functions for Sp
#! @SectionLabel LabelIntroductionAndQuickStartSp
#!
#! TODO






#! @Section Functions for Sp
#! @SectionLabel LabelFunctionsSp

####################
# PART I - a)
#    Originally implemented subfunctions
####################

InfoBruhat := NewInfoClass("InfoBruhat");;
SetInfoLevel( InfoBruhat, 2 );

#####
#   LGOStandardGensSp
#####

#! @Arguments d q
#! @Returns stdgens (the LGO standard-generators of Sp<M>(d,q)</M>)
#! @Description
#! <M>d</M>: The dimension of our matrix. Notice that <M>d</M> needs to be even for symplectic groups. <M>\newline</M>
#! <M>q</M>: A prime power <M>q = p^f</M>, where <M>F_q</M> ist the field whereover the matrices are defined <M>\newline</M>
#! This function computes the standard generators of Sp
#! as given by C. R. Leedham-Green and E. A. O'Brien in
#! "Constructive Recognition of Classical Groups in odd characteristic"
DeclareGlobalFunction( "LGOStandardGensSp" );



#####
#   LGOStandardGensSpEvenChar
#####

#! @Arguments d q
#! @Returns stdgens (the LGO standard-generators of Sp<M>(d,q)</M>) for q even
#! @Description
#! <M>d</M>: The dimension of our matrix. Notice that <M>d</M> needs to be even for symplectic groups. <M>\newline</M>
#! <M>q</M>: A 2 power <M>q = 2^f</M>, where <M>F_q</M> ist the field whereover the matrices are defined <M>\newline</M>
#! This function computes the standard generators of Sp
#! as given by C. R. Leedham-Green and E. A. O'Brien in
#! "Constructive Recognition of Classical Groups in even characteristic"
DeclareGlobalFunction( "LGOStandardGensSpEvenChar" );



####################
# PART II - a)
#    UnipotentDecomposition and Transvections
####################

#####
#   UnitriangularDecompositionSp
#####

#! @Arguments stdgens g
#! @Returns slp (A list of instructions yielding <M>u_1,u_2</M> if evaluated as SLP), <M>[u_1,g,u_2]</M> (The matrices of the Bruhat-Decomposition)
#! @Description
#! stdgens: The LGO standard-generators <M>\newline</M>
#! g: A matrix in Sp(<M>d,q</M>) and q odd <M>\newline</M>
#! Computes the Unitriangular decomposition of the matrix <M>g</M>.
DeclareGlobalFunction( "UnitriangularDecompositionSp" );



#####
#   UnitriangularDecompositionSpEvenChar
#####

#! @Arguments stdgens g
#! @Returns slp (A list of instructions yielding <M>u_1,u_2</M> if evaluated as SLP), <M>[u_1,g,u_2]</M> (The matrices of the Bruhat-Decomposition)
#! @Description
#! stdgens: The LGO standard-generators <M>\newline</M>
#! g: A matrix in Sp(<M>d,q</M>) and q even <M>\newline</M>
#! Computes the Unitriangular decomposition of the matrix <M>g</M>.
DeclareGlobalFunction( "UnitriangularDecompositionSpEvenChar" );



#####################
# PART III
#    Decomposition of Permutation and Diagonal-Matrix
####################

#####
#   MonomialSLPSp
#####

#! @Arguments stdgens mat slp
#! @Returns slp (A list of instructions to evaluate tmpvalue. If slp is also given as input then this instructions are added to slp), [tmpvalue,diag] (tmpvalue is a monomial matix such that tmpvalue*mat = diag where diag is a diagonal matrix)
#! @Description
#! stdgens: The LGO standard-generators <M>\newline</M>
#! mat: A monomial matrix (ie <M>w</M>) <M>\newline</M>
#! slp: An already existing list of instructions *optional <M>\newline</M>
#! In this function we will transform a monomial matrix <M>mat \in</M> Sp<M>(d,q)</M> into
#! a diagonal matrix diag. Using only the standard-generators <M>s,u,v</M> this
#! will lead to a monomial matrix tmpvalue
#! and <M>tmpvalue^{-1} \cdot diag = mat</M> (i.e. diag = tmpvalue*mat ).
#! Furthermore we will return list slp of instructions which will
#! (when evaluated at the LGO standard-generators) yields diag.
DeclareGlobalFunction( "MonomialSLPSp" );



#####
#   DiagSLPSp
#####

#! @Arguments stdgens diag slp
#! @Returns slp (A list of instructions to evaluate diag if slp was Input then this instructions are added to slp)
#! @Description
#! stdgens: The LGO standard-generators <M>\newline</M>
#! diag: A diagonal matrix (eg diag) <M>\newline</M>
#! slp: An already existing list of instructions *optional <M>\newline</M>
#! Writes a list of instructions which evaluated with LGO standard-generators
#! yield the diagonal matrix of the input.
DeclareGlobalFunction( "DiagSLPSp" );



####################
# PART IV
#    Main Functions. Constructs slp for the StraightLineProgram
#####################

#####
#   BruhatDecompositionSp
#####

#! @Arguments stdgens g
#! @Returns pgr (A SLP to compute <M>u_1,u_2,p_{sign}</M> and <M>diag</M> and the matrices <M>u_1, u_2, p_{sign}</M> and <M>diag</M> itself.)
#! @Description
#! stdgens: The LGO standard-generators <M> \newline </M>
#! g: A matrix in Sp<M>(d,q)</M> <M> \newline </M>
#! Uses <C>UnitriangularDecompositionSp()</C>, <C>MonomialSLPSp()</C> and <C>DiagSLPSp()</C>
#! to write a matrix <M>g \in</M> Sp<M>(d,q)</M> as <M>g = u_1^{-1} \cdot p_{sign} \cdot diag \cdot u_2^{-1}</M>
#! where <M>u_1,u_2</M> are lower unitriangular matrices, <M>p_{sign}</M> is a monomial matrix and <M>diag</M> a diagonal matrix.
#! It furthermore yields an SLP that returns the above matrices if evaluated
#! with the LGO standard-generators.
DeclareGlobalFunction( "BruhatDecompositionSp" );
