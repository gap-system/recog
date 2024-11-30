#############################################################################
# BruhatDecompositionSO.gd
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

#! @Chapter Special Orthogonal Group
#! @ChapterLabel SpecialOrthogonalGroup
#!
#! This chapter deals with the special orthogonal group

#! @Section Introduction and Quick Start of functions for SO
#! @SectionLabel LabelIntroductionAndQuickStartSO
#!
#! TODO






#! @Section Functions for SO
#! @SectionLabel LabelFunctionsSO

####################
# PART I - a)
#    Originally implemented subfunctions
####################

InfoBruhat := NewInfoClass("InfoBruhat");;
SetInfoLevel( InfoBruhat, 2 );

#####
# FindPrimePowerDecomposition
#####

#! @Arguments n
#! @Returns <M>[a,b]</M> (<M>a</M> and <M>b</M> are natural numbers such that <M>n-1= 2^a \cdot b</M>)
#! @Description
#! <M>n</M>: Natural number
#! Computes two natural numbers <M>a</M> and <M>b</M> such that <M>n-1= 2^a \cdot b</M>.
DeclareGlobalFunction( "FindPrimePowerDecomposition" );



#####
# LGOStandardGensSO
#####

#! @BeginGroup LGOStandardGensSOGroup
#! @Arguments d q e
#! @Returns stdgens (the LGO standard-generators of SO<M>(e,d,q)</M>)
#! @Description
#! <M>d</M>: the dimension of our matrices, <M>\newline</M>
#! <M>q</M>: A prime power <M>q = p^f</M>, where <M>\mathbb{F}_q</M> ist the field whereover the matrices are defined. <M>q</M> has to be odd <M>\newline</M>
#! <M>e</M>: 1 for plus type, 0 for zero type, -1 for minus type
#! This function computes the standard generators of SO
#! as given by C. R. Leedham-Green and E. A. O'Brien in
#! "Constructive Recognition of Classical Groups in odd characteristic"
#! Depending on <M>e</M> and <M>p</M> (notice <M>q = p^f</M> with p prime), the functions &#95;&#95;<C>LGOStandardGensSOPlus(d,q)</C>, &#95;&#95;<C>LGOStandardGensSOCircle(d,q)</C> or &#95;&#95;<C>LGOStandardGensSOMinus(d,q)</C> are called.
DeclareGlobalFunction( "LGOStandardGensSO" );
DeclareGlobalFunction( "__LGOStandardGensSOPlus" );
DeclareGlobalFunction( "__LGOStandardGensSOCircle" );
DeclareGlobalFunction( "__LGOStandardGensSOMinus" );
#! @EndGroup



#####
# LGOStandardGensOmega
#####

#! @BeginGroup LGOStandardGensOmegaGroup
#! @Arguments d q e
#! @Returns stdgens (the LGO standard-generators of <M>\Omega(e,d,q)</M>)
#! @Description
#! <M>d</M>: the dimension of our matrices, <M>\newline</M>
#! <M>q</M>: A prime power <M>q = p^f</M>, where <M>\mathbb{F}_q</M> ist the field whereover the matrices are defined. <M>\newline</M>
#! <M>e</M>: 1 for plus type, 0 for zero type, -1 for minus type
#! This function computes the standard generators of <M>\Omega</M>
#! as given by C. R. Leedham-Green and E. A. O'Brien in
#! "Constructive Recognition of Classical Groups in odd characteristic" and
#! "Constructive Recognition of Classical Groups in even characteristic"
#! Depending on <M>e</M>, the functions &#95;&#95;<C>LGOStandardGensOmegaPlus(d,q)</C>, &#95;&#95;<C>LGOStandardGensOmegaPlusEvenChar(d,q)</C>, &#95;&#95;<C>LGOStandardGensOmegaCircle(d,q)</C>, &#95;&#95;<C>LGOStandardGensOmegaCircleEvenChar(d,q)</C> &#95;&#95;<C>LGOStandardGensOmegaMinus(d,q)</C> or &#95;&#95;<C>LGOStandardGensOmegaMinusEvenChar(d,q)</C> are called.
DeclareGlobalFunction( "LGOStandardGensOmega" );
DeclareGlobalFunction( "__LGOStandardGensOmegaPlus" );
DeclareGlobalFunction( "__LGOStandardGensOmegaPlusEvenChar" );
DeclareGlobalFunction( "__LGOStandardGensOmegaCircle" );
DeclareGlobalFunction( "__LGOStandardGensOmegaCircleEvenChar" );
DeclareGlobalFunction( "__LGOStandardGensOmegaMinus" );
DeclareGlobalFunction( "__LGOStandardGensOmegaMinusEvenChar" );
#! @EndGroup



#####
# MSO
#####

#! @Arguments d q e
#! @Returns <M>G</M> (where <M>G =</M> SO<M>(e,d,q)</M>)
#! @Description
#! <M>d</M>: the dimension of our matrices, <M>\newline</M>
#! <M>q</M>: A prime power <M>q = p^f</M>, where <M>\mathbb{F}_q</M> ist the field whereover the matrices are defined. <M>q</M> has to be odd <M>\newline</M>
#! <M>e</M>: 1 for plus type, 0 for zero type, -1 for minus type <M>\newline</M>
#! This function returns the special orthogonal group of type e. The generators of the group are the LGO standard generators and the size of the group is already stored as an attribute.
DeclareGlobalFunction( "MSO" );



####################
# PART II - a)
#    UnipotentDecomposition and Transvections
####################

#####
# UnitriangularDecompositionSOPlus
#####

#! @Arguments stdgens g
#! @Returns slp (A list of instructions yielding <M>u_1,u_2</M> if evaluated as SLP), <M>[u_1,g,u_2]</M> (The matrices of the Bruhat-Decomposition)
#! @Description
#! stdgens: The LGO standard-generators of SO<M>^+(d,q</M>) <M>\newline</M>
#! g: A matrix in SO<M>^+(d,q</M>) <M>\newline</M>
#! Computes the Unitriangular decomposition of the matrix <M>g</M>.
DeclareGlobalFunction( "UnitriangularDecompositionSOPlus" );



#####
# UnitriangularDecompositionSOCircle
#####

#! @Arguments stdgens g
#! @Returns slp (A list of instructions yielding <M>u_1,u_2</M> if evaluated as SLP), <M>[u_1,g,u_2]</M> (The matrices of the Bruhat-Decomposition)
#! @Description
#! stdgens: The LGO standard-generators of SO<M>^\circ(d,q</M>) <M>\newline</M>
#! g: A matrix in SO<M>^\circ(d,q</M>) <M>\newline</M>
#! Computes the Unitriangular decomposition of the matrix <M>g</M>.
DeclareGlobalFunction( "UnitriangularDecompositionSOCircle" );



#####
# UnitriangularDecompositionSOMinus
#####

#! @Arguments stdgens g
#! @Returns slp (A list of instructions yielding <M>u_1,u_2</M> if evaluated as SLP), <M>[u_1,g,u_2]</M> (The matrices of the Bruhat-Decomposition)
#! @Description
#! stdgens: The LGO standard-generators of SO<M>^-(d,q</M>) <M>\newline</M>
#! g: A matrix in SO<M>^-(d,q</M>) <M>\newline</M>
#! Computes the Unitriangular decomposition of the matrix <M>g</M>.
DeclareGlobalFunction( "UnitriangularDecompositionSOMinus" );



#####################
# PART III
#    Decomposition of Permutation and Diagonal-Matrix
####################

#####
#   MonomialSLPSOPlus
#####

#! @Arguments stdgens mat slp
#! @Returns slp (A list of instructions to evaluate tmpvalue. If slp is also given as input then this instructions are added to slp), [tmpvalue,diag] (tmpvalue is a monomial matix such that tmpvalue*mat = diag where diag is a diagonal matrix)
#! @Description
#! stdgens: The LGO standard-generators of SO<M>^+(d,q)</M> <M>\newline</M>
#! mat: A monomial matrix (ie <M>w</M>) in SO<M>^+(d,q)</M> <M>\newline</M>
#! slp: An already existing list of instructions *optional <M>\newline</M>
#! In this function we will transform a monomial matrix <M>mat \in</M> SO<M>^+(d,q)</M> into
#! a diagonal matrix diag. Using only the standard-generators <M>s,u,v</M> this
#! will lead to a monomial matrix tmpvalue
#! and <M>tmpvalue^{-1} \cdot diag = mat</M> (i.e. diag = tmpvalue*mat ).
#! Furthermore we will return list slp of instructions which will
#! (when evaluated at the LGO standard-generators) yields diag.
DeclareGlobalFunction( "MonomialSLPSOPlus" );



#####
#   MonomialSLPSOCircle
#####

#! @Arguments stdgens mat slp
#! @Returns slp (A list of instructions to evaluate tmpvalue. If slp is also given as input then this instructions are added to slp), [tmpvalue,diag] (tmpvalue is a monomial matix such that tmpvalue*mat = diag where diag is a diagonal matrix)
#! @Description
#! stdgens: The LGO standard-generators of SO<M>^\circ(d,q)</M> <M>\newline</M>
#! mat: A monomial matrix (ie <M>w</M>) in SO<M>^\circ(d,q)</M> <M>\newline</M>
#! slp: An already existing list of instructions *optional <M>\newline</M>
#! In this function we will transform a monomial matrix <M>mat \in</M> SO<M>^\circ(d,q)</M> into
#! a diagonal matrix diag. Using only the standard-generators <M>s,u,v</M> this
#! will lead to a monomial matrix tmpvalue
#! and <M>tmpvalue^{-1} \cdot diag = mat</M> (i.e. diag = tmpvalue*mat ).
#! Furthermore we will return list slp of instructions which will
#! (when evaluated at the LGO standard-generators) yields diag.
DeclareGlobalFunction( "MonomialSLPSOCircle" );



#####
#   MonomialSLPSOMinus
#####

#! @Arguments stdgens mat slp
#! @Returns slp (A list of instructions to evaluate tmpvalue. If slp is also given as input then this instructions are added to slp), [tmpvalue,diag] (tmpvalue is a monomial matix such that tmpvalue*mat = diag where diag is a diagonal matrix)
#! @Description
#! stdgens: The LGO standard-generators of SO<M>^-(d,q)</M> <M>\newline</M>
#! mat: A monomial matrix (ie <M>w</M>) in SO<M>^-(d,q)</M> <M>\newline</M>
#! slp: An already existing list of instructions *optional <M>\newline</M>
#! In this function we will transform a monomial matrix <M>mat \in</M> SO<M>^-(d,q)</M> into
#! a diagonal matrix diag. Using only the standard-generators <M>s,u,v</M> this
#! will lead to a monomial matrix tmpvalue
#! and <M>tmpvalue^{-1} \cdot diag = mat</M> (i.e. diag = tmpvalue*mat ).
#! Furthermore we will return list slp of instructions which will
#! (when evaluated at the LGO standard-generators) yields diag.
DeclareGlobalFunction( "MonomialSLPSOMinus" );



#####
#   FindCorrectCycel
#####

#! @Arguments perm j
#! @Returns A permutation
#! @Description
#! perm: A list of cycles <M>\newline</M>
#! j: A natural number <M>\newline</M>
#! This is a help function for <C>MonomialSLPSOPlus</C>.
#! Checks whether there is a cycle <M>c</M> in perm such that <M>j^c \neq j</M>. If there is such an cycle, the cycle is returned. Otherwise the identity permutation is returned.
DeclareGlobalFunction( "FindCorrectCycel" );




#####
#   TestPermutationProd
#####

#! @Arguments op np l n
#! @Returns true or false
#! @Description
#! <M>op</M>: A list of cycle <M>\newline</M>
#! <M>np</M>: A list of cycle <M>\newline</M>
#! <M>l</M>: A list of natural numbers <M>\newline</M>
#! <M>n</M>: A natural number <M>\newline</M>
#! This is a help function for <C>MonomialSLPSOPlus</C>. This function checks whether the new permutation <M>np</M> destorys an already considered element of <M>op</M>. The already considered elements are stored in <M>l</M>.
DeclareGlobalFunction( "TestPermutationProd" );




#####
#   TestPermutationProd2
#####

#! @Arguments op np tn l n
#! @Returns true or false
#! @Description
#! <M>op</M>: A list of cycle <M>\newline</M>
#! <M>np</M>: A list of cycle <M>\newline</M>
#! <M>tn</M>: A natural number <M>\newline</M>
#! <M>l</M>: A list of natural numbers <M>\newline</M>
#! <M>n</M>: A natural number <M>\newline</M>
#! This is a help function for <C>MonomialSLPSOPlus</C>. This function checks whether the probability to continue with <M>np</M> is higher than with <M>op</M> depending on the element <M>tn</M>.
DeclareGlobalFunction( "TestPermutationProd2" );




#####
#   MonomialMatrixToEasyForm
#####

#! @Arguments M
#! @Returns [list,perm] (list is a list of the non-zero elements of each column of <M>M</M>, perm is the permutation corresponding to <M>M</M>)
#! @Description
#! <M>M</M>: A monomial matrix <M>\newline</M>
#! This is a help function for <C>MonomialSLPSOPlus</C> and <C>MonomialSLPSOCircle</C>. This function calcultes a list of size 2. The first entry is a list of the non-zero elements of each column of <M>M</M>. The second entry is a permutation which corresponds to <M>M</M> as a permutation matrix.
DeclareGlobalFunction( "MonomialMatrixToEasyForm" );




#####
#   EasyFormToMonomialMatrix
#####

#! @Arguments tupel n fld
#! @Returns <M>M</M> (A monomial matrix)
#! @Description
#! <M>tupel</M>: A 2-tupel as in <C>MonomialMatrixToEasyForm</C> <M>\newline</M>
#! <M>n</M>: A natural number <M>\newline</M>
#! <M>fld</M>: A finite field <M>\newline</M>
#! This is a help function for <C>MonomialSLPSOPlus</C> and <C>MonomialSLPSOCircle</C>. This function computes a monomial matrix <M>M</M> of size <M>n</M> over <M>fld</M> such that <C>MonomialMatrixToEasyForm</C><M>(M) = tupel </M>.
DeclareGlobalFunction( "EasyFormToMonomialMatrix" );




#####
#   MultiplicationOfEasyForm
#####

#! @Arguments tupel1 tupel2
#! @Returns [list,perm] (list is a list of the non-zero elements of each column of <M>M</M>, perm is the permutation corresponding to <M>M</M>)
#! @Description
#! <M>tupel1</M>: A 2-tupel as in <C>MonomialMatrixToEasyForm</C> <M>\newline</M>
#! <M>tupel2</M>: A 2-tupel as in <C>MonomialMatrixToEasyForm</C> <M>\newline</M>
#! This is a help function for <C>MonomialSLPSOPlus</C> and <C>MonomialSLPSOCircle</C>. Let <M>M_1</M> be a monomial matrix which corresponds to <M>tupel1</M> and <M>M_2</M> be a monomial matrix which corresponds to <M>tupel2</M>. This function computes a tupel [list,perm] such that for the corresponding monomial matrix <M>M</M> holds <M>M = M_1 \cdot M_2</M>.
DeclareGlobalFunction( "MultiplicationOfEasyForm" );



#####
#   DiagSLPSOPlus
#####

#! @Arguments stdgens diag slp
#! @Returns slp (A list of instructions to evaluate diag if slp was Input then this instructions are added to slp)
#! @Description
#! stdgens: The LGO standard-generators of SO<M>^+(d,q)</M> <M>\newline</M>
#! diag: A diagonal matrix (eg diag) in SO<M>^+(d,q)</M> <M>\newline</M>
#! slp: An already existing list of instructions *optional <M>\newline</M>
#! Writes a list of instructions which evaluated with LGO standard-generators
#! yield the diagonal matrix of the input.
DeclareGlobalFunction( "DiagSLPSOPlus" );




#####
#   DiagSLPSOCircle
#####

#! @Arguments stdgens diag slp
#! @Returns slp (A list of instructions to evaluate diag if slp was Input then this instructions are added to slp)
#! @Description
#! stdgens: The LGO standard-generators of SO<M>^\circ(d,q)</M> <M>\newline</M>
#! diag: A diagonal matrix (eg diag) in SO<M>^\circ(d,q)</M> <M>\newline</M>
#! slp: An already existing list of instructions *optional <M>\newline</M>
#! Writes a list of instructions which evaluated with LGO standard-generators
#! yield the diagonal matrix of the input.
DeclareGlobalFunction( "DiagSLPSOCircle" );




#####
#   DiagSLPSOMinus
#####

#! @Arguments stdgens diag slp
#! @Returns slp (A list of instructions to evaluate diag if slp was Input then this instructions are added to slp)
#! @Description
#! stdgens: The LGO standard-generators of SO<M>^-(d,q)</M> <M>\newline</M>
#! diag: A diagonal matrix (eg diag) in SO<M>^-(d,q)</M> <M>\newline</M>
#! slp: An already existing list of instructions *optional <M>\newline</M>
#! Writes a list of instructions which evaluated with LGO standard-generators
#! yield the diagonal matrix of the input.
DeclareGlobalFunction( "DiagSLPSOMinus" );



####################
# PART IV
#    Main Functions. Constructs slp for the StraightLineProgram
#####################

#####
#   BruhatDecompositionSO
#####

#! @Arguments stdgens g
#! @Returns pgr (A SLP to compute <M>u_1,u_2,p_{sign}</M> and <M>diag</M> and the matrices <M>u_1, u_2, p_{sign}</M> and <M>diag</M> itself.)
#! @Description
#! stdgens: The LGO standard-generators <M> \newline </M>
#! g: A matrix in SO<M>(e,d,q)</M> <M> \newline </M>
#! Uses <C>UnitriangularDecompositionSOPlus()</C>, <C>MonomialSLPSOPlus()</C> and <C>DiagSLPSOPlus()</C>
#! for the plus type, <C>UnitriangularDecompositionSOCircle()</C>, <C>MonomialSLPSOCircle()</C> and <C>DiagSLPSOCircle()</C>
#! for the circle type or <C>UnitriangularDecompositionSOMinus()</C>, <C>MonomialSLPSOMinus()</C> and <C>DiagSLPSOMinus()</C>
#! for the minus type to write a matrix <M>g \in</M> SO<M>(e,d,q)</M> as <M>g = u_1^{-1} \cdot p_{sign} \cdot diag \cdot u_2^{-1}</M>
#! where <M>u_1,u_2</M> are lower unitriangular matrices, <M>p_{sign}</M> is a monomial matrix and <M>diag</M> a diagonal matrix.
#! It furthermore yields an SLP that returns the above matrices if evaluated
#! with the LGO standard-generators.
DeclareGlobalFunction( "BruhatDecompositionSO" );
DeclareGlobalFunction( "BruhatDecompositionSOMinus" );
