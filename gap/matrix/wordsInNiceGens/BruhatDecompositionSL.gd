#############################################################################
# BruhatDecompositionSL.gd
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

#! @Chapter Special Linear Group
#! @ChapterLabel SpecialLinearGroup
#!
#! This chapter deals with the special linear group

#! @Section Introduction and Quick Start of functions for SL
#! @SectionLabel LabelIntroductionAndQuickStartSL

######################################
#! Concept:
#!    This implementation follows the ideas of
#!    "Straight-line programs with memory and matrix Bruhat decomposition"
#!    by Alice Niemeyer, Tomasz Popiel and Cheryl Praeger.
#!    In the following all references will mean this paper
#!    and in case we differ from this paper (due to readability or bug-fixing)
#!    this will also be remarked. <M>\smallskip</M>
#!
#!    Let <M>g \in</M> SL<M>(d,p^f)</M>
#!    Bruhat Decomposition computes <M>g = u_1 \cdot w \cdot u_2</M>, where
#!         - <M>u_1,u_2</M> are lower triangular matrices
#!         - <M>w</M> is monomial matrix <M>\smallskip</M>
#!
#!    In this algorithm we want to compute the Bruhat-Decomposition of <M>g</M>
#!    and give <M>g</M> (respectively <M>u_1,w</M> and <M>u_2</M>) as word in the so called
#!    "LGO standard generators" (REF TODO). <M>\smallskip</M>
#!
#!    1) While computing <M>u_1</M> (resp <M>u_2</M>) with some kind of Gauß-Algorithm,
#!    we express the matrices as product of so called transvections
#!    - For <M>1 \leq j &lt; i \leq d</M>: <M>t_{i,j}(\alpha)</M> is the matrix T with
#!        1-entries on diagonal, <M>T_{i,j} = \alpha</M>, 0 elsewhere <M>\newline</M>
#!    Each <M>t_{i,j}(\alpha)</M> can be computed from <M>t_{2,1}(\alpha)</M> via recursion,
#!    where we have to distinguish the odd and even dimensons (p12 Lemma 4.2).
#!    This again can be expressed as a product of <M>t_{2,1}(\omega^\ell)</M>
#!    (where omega is a primitive element and <M>0 \leq \ell &lt; f</M>).
#!    The transvections as words in the standard generators are described in
#!    (p12 Lemma 4.2). <M>\newline</M>
#!    This yields a decomposition of <M>u_1</M> and <M>u_2</M> in standard generators. <M>\smallskip</M>
#!
#!    2) In a further step we will decompose the monomial Matrix <M>w</M> in
#!    a signed permutation matrix p_sign and a diagonal Matrix diag.
#!    ( How to associate p_sign with a product of generators is
#!    further described in (PART I b) and (PART III) ) <M>\smallskip</M>
#!
#!    3) The last step is the decomposition of the diagonal Matrix in 2)
#!    as word in the standard generators. <M>\smallskip</M>
#!
#!    We won't do this matrix multiplications directly, but write them
#!    in a list to evaluate in a StraightLineProgram. (Section 2)
#!    Although described differently in the paper, we sometimes will allow
#!    instructions to multiply more than two elements (eg during conjugating).
#!    This doesn't affect the optimality of an slp much, but higly increases
#!    the readability of our implementation. <M>\smallskip</M>
######################################
#! @Section Implemented Subfunctions (Part I)
#! @SectionLabel LabelSubfunctionsPart1
#!
#!    Later we will need some additional functions. Why they are needed and where they are needed is described here. <P/>
#!
#!    <List>
#!    <Item> <C>MakeSLP()</C>: After the <C>BruhatDecompositionSL()</C> we get a list of instructions to calculate the matrices we want using the LGO standard generators. <C>MakeSLP()</C> is used to get a SLP out of these instructions.</Item>
#!    <Item> <C>CoefficientsPrimitiveElement()</C>: It expresses an element w in a field fld as a linear combination of a Primitive Element. This is important for the transvections. (TODO Add Reference!) </Item>
#!    <Item> <C>MyPermutationMat()</C>: Turns a permutation into a permutation matrix. We need it to calculate the LGO standard generator. </Item>
#!    <Item> <C>LGOStandardGensSL()</C>: This function computes the standard generators of SL
#!                    as given by C. R. Leedham-Green and E. A. O'Brien in
#!                    "Constructive Recognition of Classical Groups  in odd characteristic".
#!                    (TODO Add Reference!) <P/>
#!                    </Item>
#!    <Item> <C>HighestSlotOfSLP()</C>: The following function determines the highest slot of a  SLP constructed from the list slp will write in. This is important to glue SLPs together. </Item>
#!
#!    <Item> <C>MatToWreathProd()</C> and <C>WreathProdToMat()</C>:
#!        In <C>PermSLP()</C> [<Ref Sect="PermSLP"/>] we want to transform the monomial matrix <M>w</M> given by
#!        <C>UnipotentDecomposition()</C> into a diagonal matrix.
#!        (The exact procedure is described in <C>PermSLP()</C> [<Ref Sect="PermSLP"/>])<P/>
#!        Since multiplying the LGO standard-generators <M>s,v</M> and <M>x</M> not only involves
#!        permutations but we also have to consider which non-zero entries are <M>+1</M> and
#!        which <M>-1</M>, we want to associate this matrices with permutations on <M>2d</M> points. (cf. Wreath-Product)<P/>
#!
#!        <M>[s,v,x] \to Sym(2d), M \to </M> <C>Mwr</C> where
#!        <M>i^{Mwr} =  j</M>  and <M>(i+d)^{Mwr}= j+d</M> if <M> M_{i,j} = 1</M> and
#!        <M>i^{Mwr} = j+d</M> and <M>(i+d)^{Mwr}=  j</M>  if <M>M_{i,j} = -1</M>
#!        for <M>1 \leq i \leq d</M>.<P/>
#!
#!        Due to their relation to wreath-products, we will call denote the image
#!        of a matrix <C>M</C><M> \in [s,v,x] </M> by <C>Mwr</C>. <P/>
#!
#!        In fact the association from <C>MatToWreathProd()</C> [<Ref Sect="MatToWreathProd"/>] is an isomorphism and we can associate to each
#!        permutation we compute during <C>PermSLP()</C> [<Ref Sect="PermSLP"/>] a signed permutation matrix (a monomial matrix with only <M>+1</M> and <M>-1</M> as non-zero entries). <P/>

#!        <M>M_{i,j} = 1</M>  if <M>i^{Mwr} =  j \leq d</M> and
#!        <M>M_{i,j} = -1</M> if <M>i^{Mwr} = j+d</M>
#!    </Item>
#!
#!    <Item> <C>AEM()</C>: Write instructions for Ancient Egyptian Multiplication in slp. At several occasions we will need to compute a high power of some value saved in a memory slot.</Item>
#!
#!    <Item> <C>TestIfMonomial()</C>: Tests if a given matrix M is monomial matrix. We use it to decide whether we are already finished in <C>UnipotentDecomposition()</C>.</Item>
#!
#!    </List>
#!
#!    For some functions also exist a NC version. See [<Ref Sect="Section_LabelNCVersionSL"/>].
#!
#!
#! @Section UnipotentDecomposition (Part II - a)
#! @SectionLabel LabelUnipotentDecomposition2a
#!
#!    In this section is the <C>UnipotentDecomposition()</C> described. This method is used to compute the
#!    Unitriangular decomposition of the matrix <M>g</M>. [<Ref Sect="UnipotentDecomposition"/>] <P/>
#!
#!    For this we use five local functions in the <C>UnipotentDecomposition()</C>. They are
#!    <C>TransvecAtAlpha()</C>,
#!    <C>ShiftTransvections()</C>, <C>FastShiftTransvections()</C>, <C>BackShiftTransvections()</C> and
#!    <C>FastBackShiftTransvections()</C>. <P/>
    
#!    The difference to <C>UnipotentDecompositionWithTi()</C> [<Ref Sect="Section_LabelUnipotentDecomposition2b"/>] is that this
#!    version won't store all the transvections <M>t_{i,i-1}(\omega^l)</M>.
#!    This will increase the runtime but reduce the memory usage by <M>(d-3) \cdot f</M> compared to
#!    the <C>UnipotentDecompositionWithTi()</C>.<P/>
#!
#!    The function can be called for example by
#!<Log>
#!gap> d := 3;;
#!gap> q := 5;;
#!gap> L := SL(d, q);;
#!gap> m := PseudoRandom(L);;
#!gap> stdgens := LGOStandardGensSL(d, q);;
#!gap> UnipotentDecomposition( stdgens, g);;
#!</Log>
#!
#! @Section UnipotentDecomposition saving Transvections (Part II - b)
#! @SectionLabel LabelUnipotentDecomposition2b
#!
#!    In this section is the <C>UnipotentDecompositionWithTi()</C> described.
#!    This method is used to compute the
#!    Unitriangular decomposition of the matrix <M>g</M>. [<Ref Sect="UnipotentDecompositionWithTi"/>] <P/>
#!
#!    In this version we will store all the transvections <M>t_{i,i-1}(\omega^l)</M>.
#!    This will increase the memory usage by <M>(d-3) \cdot f</M> but reduce runtime.<P/>
#!
#!    In <C>UnipotentDecompositionWithTi()</C> we use two local functions. They are
#!    <C>TransvectionAtAlpha()</C> and
#!    <C>ComputeAllTransvections()</C>. <P/>
#!
#!    The function can be called for example by
#!<Log>
#!gap> d := 3;;
#!gap> q := 5;;
#!gap> L := SL(d, q);;
#!gap> m := PseudoRandom(L);;
#!gap> stdgens := LGOStandardGensSL(d, q);;
#!gap> UnipotentDecompositionWithTi( stdgens, g);;
#!</Log>
#!
#!
#! @Section Decomposing the Monomial Matrix (Part III)
#! @SectionLabel LabelDecomposingMonomialMatrices
#!
#!    We use three functions to decompose the monomial matrix <M>w</M> we get from
#!    <C>UnipotentDecomposition()</C>. They are:
#!    <List>
#!        <Item> <C>PermutationMonomialMatrix()</C>: Find the permutation (in Sym(d) corresponding to the monomial matrix <M>w</M>) and <M>diag</M> a diagonal matrix, where <M>diag[i]</M> is the non-zero entry of row <M>i</M>. [<Ref Sect="PermutationMonomialMatrix"/>] </Item>
#!        <Item> <C>PermSLP()</C>:
#!        In this function we will transform a monomial matrix <M>w \in </M>SL<M>(d,q)</M> into a diagonal matrix <M>diag</M>. Using only the standard-generators <M>s,v,x</M>. This will lead to a monomial matrix <M>p_{sign}</M> with only <M>\pm 1</M> in non-zero entries and <M>p_{sign} \cdot diag = w</M> (i.e. <M>diag = (p_{sign})^{-1} \cdot w</M> ).<P/>
#!                Furthermore we will return list <C>slp</C> of instructions which will (when evaluated at the LGO standard-generators) yield <M>diag</M>.
#!
#!            It is sufficient for <M>diag</M> to be diagonal, if the permutation associated with <M>w</M> (i.e. <M>i^{\pi_w} = j</M> if <M>M_{i,j} \neq 0</M>) is the inverse of the permutation associated to <M>p_{sign}</M> (again only to Sym(<M>d</M>) ).<P/>
#!
#!            In <C>PermSLP()</C> we thus transform <M>\pi_w</M> to <M>()</M> using only <M>\{ \pi_s, \pi_v, \pi_x \}</M>.
#!            In order to know <M>diag</M> without computing all matrix multiplications, (we don't know the signs of <M>p_{sign}</M>), we compute a second permutation simultaneously (here using their identification with permutations in Sym<M>(2d)</M> and identifying <M>\{ \pi_s, \pi_v, \pi_x \}</M> with <M>\{s,v,x\}</M> ). [<Ref Sect="PermSLP"/>] </Item>
#!        <Item> <C>DiagonalDecomposition()</C>: Writes a list of instructions which evaluated on LGO standard-generators yield the diagonal matrix of the input. [<Ref Sect="DiagonalDecomposition"/>]</Item>
#!    </List>
#!
#!    To these three functions is also a NC version implemented. See [<Ref Sect="Section_LabelNCVersionSL"/>].
#!
#!
#! @Section Main Function (Part IV)
#! @SectionLabel LabelMainFunctionSL
#!
#!    In <C>BruhatDecompositionSL()</C> [<Ref Sect="BruhatDecompositionSL"/>] we put everything together. We use the three functions <C>UnipotentDecomposition()</C> [<Ref Sect="UnipotentDecomposition"/>], <C>PermSLP()</C> [<Ref Sect="PermSLP"/>] and <C>DiagonalDecomposition()</C> [<Ref Sect="DiagonalDecomposition"/>] to compute matrices with <M>u_1^{-1} \cdot p_{sign} \cdot diag \cdot u_2^{-1} = g</M> and a SLP <C>pgr</C> that computes these matrices with the LGO standard generators.<P/>
#!
#!    Here is an exampel:
#!<Log>
#!gap> mat := [ [ Z(5)^2, Z(5)^0, Z(5)^2 ],
#!>             [ Z(5)^3, 0*Z(5), 0*Z(5) ],
#!>             [ 0*Z(5), Z(5)^2, Z(5)^2 ] ];;#!
#!gap> L := BruhatDecompositionSL(LGOStandardGensSL(3,5), mat);
#!gap> result := ResultOfStraightLineProgram(L[1], LGOStandardGensSL(3,5));
#!</Log>
#!
#!    <C>BruhatDecompositionSLWithTi()</C> [<Ref Sect="BruhatDecompositionSLWithTi"/>] works like <C>BruhatDecompositionSL()</C> [<Ref Sect="BruhatDecompositionSL"/>] but uses <C>UnipotentDecompositionWithTi()</C> [<Ref Sect="UnipotentDecompositionWithTi"/>] instead of <C>UnipotentDecomposition()</C> [<Ref Sect="UnipotentDecomposition"/>]. <P/>
#!
#!    You can use it in the same way like <C>BruhatDecompositionSL()</C>:
#!<Log>
#!gap> mat := [ [ Z(5)^2, Z(5)^0, Z(5)^2 ],
#!>             [ Z(5)^3, 0*Z(5), 0*Z(5) ],
#!>             [ 0*Z(5), Z(5)^2, Z(5)^2 ] ];;
#!gap> L := BruhatDecompositionSLWithTi(LGOStandardGensSL(3,5), mat);
#!gap> result := ResultOfStraightLineProgram(L[1], LGOStandardGensSL(3,5));
#!</Log>
#!
#!    To both functions is also a NC version implemented. See [<Ref Sect="Section_LabelNCVersionSL"/>].
#!
#!
#! @Section NC Version
#! @SectionLabel LabelNCVersionSL
#!
#!    Here is the NC version of the Bruhat Decomposition described.
#!    In all implemented functions are all used functions replaced through their NC version (if one exists).
#!    Moreover are all checks from functions of MyBruhatDecomposition removed.<P/>
#!
#!    These functions has been modified by this actions and got a NC Version:
#! <List>
#!            <Item><C>MakeSLP()</C>[<Ref Sect="MakeSLP"/>] <M>\to</M> <C>MakeSLPNC()</C>[<Ref Sect="MakeSLPNC"/>] (uses the NC version of <C>StraightLineProgram</C>)</Item>
#!            <Item><C>MyPermutationMat()</C> [<Ref Sect="MyPermutationMat"/>] <M>\to</M> <C>MyPermutationMatNC()</C> [<Ref Sect="MyPermutationMatNC"/>] (uses the NC version of <C>ConvertToMatrixRep</C>)</Item>
#!            <Item><C>LGOStandardGensSL()</C> [<Ref Sect="LGOStandardGensSL"/>] <M>\to</M> <C>LGOStandardGensSLNC()</C> [<Ref Sect="LGOStandardGensSLNC"/>] (uses the NC version of <C>MyPermutationMat()</C>)</Item>
#!            <Item><C>MatToWreathProd()</C> [<Ref Sect="MatToWreathProd"/>] <M>\to</M> <C>MatToWreathProdNC()</C> [<Ref Sect="MatToWreathProdNC"/>] (no checks for user input)</Item>
#!            <Item><C>TestIfMonomial()</C> [<Ref Sect="TestIfMonomial"/>] <M>\to</M> <C>TestIfMonomialNC()</C> [<Ref Sect="TestIfMonomialNC"/>] (no checks for user input)</Item>
#!            <Item><C>UnipotentDecomposition()</C> [<Ref Sect="UnipotentDecomposition"/>] <M>\to</M> <C>UnipotentDecompositionNC()</C> [<Ref Sect="UnipotentDecompositionNC"/>] (no checks for user input)</Item>
#!            <Item><C>UnipotentDecompositionWithTi()</C> [<Ref Sect="UnipotentDecompositionWithTi"/>] <M>\to</M> <C>UnipotentDecompositionWithTiNC()</C> [<Ref Sect="UnipotentDecompositionWithTiNC"/>] (no checks for user input)</Item>
#!            <Item><C>PermutationMonomialMatrix()</C> [<Ref Sect="PermutationMonomialMatrix"/>] <M>\to</M> <C>PermutationMonomialMatrixNC()</C> [<Ref Sect="PermutationMonomialMatrixNC"/>] (no checks for user input)</Item>
#!            <Item><C>PermSLP()</C> [<Ref Sect="PermSLP"/>] <M>\to</M> <C>PermSLPNC()</C> [<Ref Sect="PermSLPNC"/>] (no checks for unser input and uses <C>PermutationMonomialMatrixNC()</C>)</Item>
#!            <Item><C>DiagonalDecomposition()</C> [<Ref Sect="DiagonalDecomposition"/>] <M>\to</M> <C>DiagonalDecompositionNC()</C> [<Ref Sect="DiagonalDecompositionNC"/>] (no checks for user input)</Item>
#!            <Item><C>BruhatDecompositionSL()</C> [<Ref Sect="BruhatDecompositionSL"/>] <M>\to</M> <C>BruhatDecompositionSLNC()</C> [<Ref Sect="BruhatDecompositionSLNC"/>] (uses <C>UnipotentDecompositionNC()</C>, <C>PermSLPNC()</C> and <C>DiagonalDecompositionNC</C>)</Item>
#!            <Item><C>BruhatDecompositionSLWithTi()</C> [<Ref Sect="BruhatDecompositionSLWithTi"/>] <M>\to</M> <C>BruhatDecompositionSLWithTiNC()</C> [<Ref Sect="BruhatDecompositionSLWithTiNC"/>] (uses <C>UnipotentDecompositionWithTiNC()</C>, <C>PermSLPNC()</C> and <C>DiagonalDecompositionNC()</C>)</Item>
#! </List>


#! @Section Functions for SL
#! @SectionLabel LabelFunctionsSL

######################################
#
#    NC Version:
#    In all implemented functions are all used functions replaced through
#    their NC version (if one exists). Moreover are all checks from functions
#    of BruhatDecomposition have been removed
#
#    This functions has been modified by this actions and got a NC Version:
#        MakeSLP -> MakeSLPNC (uses the NC version of StraightLineProgram)
#        MyPermutationMat -> MyPermutationMatNC (uses ConvertToMatrixRepNC)
#        LGOStandardGensSL -> LGOStandardGensSLNC (uses MyPermutationMatNC)
#    The NC versions of the following functions do not check for user input
#        MatToWreathProd -> MatToWreathProdNC
#        TestIfMonomial -> TestIfMonomialNC
#        UnipotentDecomposition -> UnipotentDecompositionNC
#        UnipotentDecompositionWithTi -> UnipotentDecompositionWithTiNC
#        PermutationMonomialMatrix -> PermutationMonomialMatrixNC
#        PermSLP -> PermSLPNC (also uses other NC versions of other functions)
#        DiagonalDecomposition -> DiagonalDecompositionNC
#    BruhatDecompositionSLNC and BruhatDecompositionSLWithTiNC now use the NC
#    versions of UnipotentDecomposition, PermSLP and DiagonalDecomposition
#        BruhatDecompositionSL -> BruhatDecompositionSLNC
#        BruhatDecompositionSLWithTi -> BruhatDecompositionSLWithTiNC
#
######################################


####################
# PART I - a)
#    Originally implemented subfunctions
####################

InfoBruhat := NewInfoClass("InfoBruhat");;
SetInfoLevel( InfoBruhat, 2 );

#####
# MakeSLP()
#####

#! @BeginGroup MakeSLPGroup
#! @Arguments slp genlen
#! @Returns An SLP using the instructions of slp and genlen inputs
#! @Description
#! slp: A list of instructions for a straight-line program, <M>\newline</M>
#! genlen: The number of inputs for our SLP (ie the number of generators ) <M>\newline</M>
#! To increase readability, the lists slp as defined later
#! (see Unipotent-, Diagonal-, BruhatDecompositionSL and PermSLP)
#! start with [1,1],[2,1],.. [5,1]. However this represents the LGO standard-
#! generators and is the input of our straight-line program.
#! Defining and SLP we thus have to exclude this instructions from our list.
DeclareGlobalFunction( "MakeSLP" );
DeclareGlobalFunction( "MakeSLPNC" );
#! @EndGroup


#####
# CoefficientsPrimitiveElement()
#####

#! @Arguments fld alpha
#! @Returns Coefficients (A vector c sth for omega primitive element alpha = sum c[i] omega^(i-1))
#! @Description
#! fld: A field, <M>\newline</M>
#! alpha: An element of fld <M>\newline</M>
#! The following function has been written by Thomas Breuer.
#! It expresses an element alpha in a field fld as
#! a linear combination of a Primitive Element.
DeclareGlobalFunction( "CoefficientsPrimitiveElement" );



#####
# MyPermutationMat()
#####

#! @BeginGroup MyPermutationMatGroup
#! @Arguments perm dim fld
#! @Returns The permutation matrix of perm over <M>M_{d x d}(fld)</M> (ie <M>res_{i,j} = One(fld)</M> if <M>i^{perm} = j</M>)
#! @Description
#! perm: A permutation, <M>\newline</M>
#! dim: A natural number, <M>\newline</M>
#! fld: A field <M>\newline</M>
#! Given a permutation an integer <M>d > 0</M> and a field fld, this function computes
#! the permutation matrix <M>P</M> in <M>M_{d x d}(fld)</M>.
DeclareGlobalFunction( "MyPermutationMat" );
DeclareGlobalFunction( "MyPermutationMatNC" );
#! @EndGroup


#####
# LGOStandardGensSL
#####

#! @BeginGroup LGOStandardGensSLGroup
#! @Arguments d q
#! @Returns stdgens (the LGO standard-generators of SL<M>(d,q)</M>)
#! @Description
#! <M>d</M>: the dimension of our matrix, <M>\newline</M>
#! <M>q</M>: A prime power <M>q = p^f</M>, where <M>F_q</M> ist the field whereover the matrices are defined <M>\newline</M>
#! This function computes the standard generators of SL
#! as given by C. R. Leedham-Green and E. A. O'Brien in
#! "Constructive Recognition of Classical Groups in odd characteristic"
#! (This matrices can also be found in the paper ch 3.1 ps 6-7)
DeclareGlobalFunction( "LGOStandardGensSL" );
DeclareGlobalFunction( "LGOStandardGensSLNC" );
#! @EndGroup


####################
# PART I - b)
#    Additionally implemented subfunctions
####################

#####
# HighestSlotOfSLP()
#####

# We can't use Length(slp) as done in the original code to determine which
# slots are already used, because not every entry of slp creates a new slot
# while others may increase the highest slot used by more than one.
# (After explicitly writing in a slot j>N, the SLP continues creating slots
#    j+1,j+2,.. if no slot is explicitly given.)

#! @Arguments slp
#! @Returns highestslot (The number of slots this SLP will need if evaluated)
#! @Description
#! slp: A list of instructions satisfying the properties for an SLP <M>\newline</M>
#! The following function determines the highest slot a SLP
#! constructed from the list slp will write in.
DeclareGlobalFunction( "HighestSlotOfSLP" );



#####
# MatToWreathProd() and WreathProdToMat()
#####

#! @BeginGroup MatToWreathProdGroup
#! @Arguments M
#! @Returns perm (the permutation Mwr)
#! @Description
#! M: A monomial matrix with only +1 and -1 entries <M>\newline</M>
#! In PermSLP we want to transform the monomial matrix w given by
#! UnipotentDecomposition() into a diagonal matrix.
#!    (The exact procedure is described in PermSLP)
#! Since multiplying the LGO standard-generators <M>s,v</M> and <M>x</M> not only involves
#! permutations but we also have to consider which non-zero entries are +1 and
#! which -1, we want to associate this matrices with permutations on <M>2d</M> points.
#! (cf Wreath-Product)
#! <M> \langle s,v,x \rangle \rightarrow</M> Sym<M>(2d), M \rightarrow Mwr</M> where
#! <M>i^{Mwr} =  j </M> and <M>(i+d)^{Mwr}= j+d</M> if <M>M_{i,j} = 1</M>        and
#! <M>i^{Mwr} = j+d</M> and <M>(i+d)^{Mwr}=  j</M>  if <M>M_{i,j} = -1</M>
#! for <M>1\leq i\leq d</M>
#! Due to their relation to wreath-products, we will call denote the image
#! of a matrix <M>M \in \langle s,v,x \rangle </M> by Mwr
DeclareGlobalFunction( "MatToWreathProd" );
DeclareGlobalFunction( "MatToWreathProdNC" );
#! @EndGroup


#! @Arguments perm dim fld
#! @Returns res (The Matrix M satisfying the below properties)
#! @Description
#! perm: A permutation in Sym(<M>2d</M>) sth. <M>{{i,i+d}}_1: 1 \leq i \leq d </M> are blocks, <M>\newline</M>
#! dim: The dimension of the matrix we want perm send to, <M>\newline</M>
#! fld: The field whereover the matrix is defined. <M>\newline</M>
#! In fact the association above is an isomorphism and we can associate to each
#! permutation we compute during PermSLP a unique monomial matrix whose non-zero
#! entries are +1 or -1.
#! <M>M_{i,j} = 1</M>  if <M>i^{Mwr} =  j \leq d  </M>      and
#! <M>M_{i,j} = -1</M> if <M>i^{Mwr} = j+d</M>
DeclareGlobalFunction( "WreathProdToMat" );



#####
# AEM (Ancient Egytian Multiplication)
#####

#! @Arguments spos respos tmppos k
#! @Returns instr (Lines of an SLP that will (when evaluated) take the value b saved in spos and write b^k in respos)
#! @Description
#! AEM (Ancient Egytian Multiplication) <M>\newline</M>
#! spos: The memory slot, where a value b is saved in, <M>\newline</M>
#! respos: The memory slot we want the exponentation to be written in, <M>\newline</M>
#! tmppos: A memory slot for temporary results, <M>\newline</M>
#! k: An integer <M>\newline</M>
#! At several occasions we will need to compute a high power of some value
#! saved in a memory slot. For this purpose there is a variaton of AEM
#! implemented below.
#! Remarks:     tmpos and respos must differ.
#! If spos = respos or spos =  tmpos it will be overwritten.
DeclareGlobalFunction( "AEM" );



#####
# TestIfMonomial()
#####

#! @BeginGroup TestIfMonomialGroup
#! @Arguments M
#! @Returns True if <M>M</M> is a monomial matrix, otherwise false.
#! @Description
#! <M>M</M>: A Matrix <M>\newline</M>
#! Tests if a given matrix <M>M</M> is a monomial matrix.
#! There is function in GAP, however it does not seem to work for SL<M>(d,q)</M>.
DeclareGlobalFunction( "TestIfMonomial" );
DeclareGlobalFunction( "TestIfMonomialNC" );
#! @EndGroup


####################
# PART II - a)
#    UnipotentDecomposition and Transvections
####################

#####
# Transvections2()
#####

#! @Arguments stdgens omega slp pos
#! @Returns slp: The list of instruction with additional instructions writing <M>t_{2,1}(\omega^\ell)</M> in Slot pos[l+1] <M>0 \leq \ell \leq f-1</M>.
#! @Description
#! stdgens: The LGO standard-generators of SL<M>(d,q)</M> <M>\newline</M>
#! omega: A primitive element of GF(<M>q</M>) <M>\newline</M>
#! slp: A list of instructions <M>\newline</M>
#! pos: A list of numbers, denoting where to save the transvections
#! <M>t_{2,1}(\omega^\ell)</M> for <M>0 \leq \ell \leq f-1</M> <M>\newline</M>
#! Let stdgens be the list of standard generators for SL<M>(d,p^f)</M>
#! and let omega be a primitive element of G(<M>p^f</M>).
#! This function computes <M>T_2 := \{ t_{2,1}(\omega^\ell) \mid 0 \leq \ell \leq f-1 \}</M>
#! Record what we do in slp
#! This function coincides with eq (6) p12.
DeclareGlobalFunction( "Transvections2" );



#####
# UnipotentDecomposition()
#####

#! @BeginGroup UnipotentDecompositionGroup
#! @Arguments stdgens g
#! @Returns slp (A list of instructions yielding <M>u_1,u_2</M> if evaluated as SLP), <M>[u_1,g,u_2]</M> (The matrices of the Bruhat-Decomposition)
#! @Description
#! stdgens: The LGO standard-generators <M>\newline</M>
#! g: A matrix in SL(<M>d,q</M>) <M>\newline</M>
#! Computes the Unitriangular decomposition of the matrix <M>g</M>.
DeclareGlobalFunction( "UnipotentDecomposition" );
DeclareGlobalFunction( "UnipotentDecompositionNC" );
#! @EndGroup


####################
# PART II - b)
#    Basically the same as in II - a)
#    But now we save all Transvections
####################

#! @BeginGroup UnipotentDecompositionWithTiGroup
#! @Arguments stdgens g
#! @Returns slp (A list of instructions yielding <M>u_1,u_2</M> if evaluated as SLP), <M>[u_1,g,u_2]</M> (The matrices of the Bruhat-Decomposition)
#! @Description
#! stdgens: The LGO standard-generators <M>\newline</M>
#! g: A matrix in SL(<M>d,q</M>) <M>\newline</M>
#! Computes the Bruhat decomposition of the matrix <M>g</M>, given
#! the standard generators for the group.
#! In this version we will store all the transvections <M>t_{i,i-1}(\omega^\ell)</M>.
#! this will increase the memory usage by <M>(d-3) \cdot f</M> but reduce the runtime.
DeclareGlobalFunction( "UnipotentDecompositionWithTi" );
DeclareGlobalFunction( "UnipotentDecompositionWithTiNC" );
#! @EndGroup


#####################
# PART III
#    Decomposition of Permutation and Diagonal-Matrix
####################

#####
# PermutationMonomialMatrix()
#####

#! @BeginGroup PermutationMonomialMatrixGroup
#! @Arguments M
#! @Returns diag (The vector of non-zero entries, where diag<M>[i]</M> is the non-zero entry of row <M>i</M>.), perm (The  permutation associated to <M>M</M>, i.e. <M>i^{perm} = j</M> if <M>M_{i,j}</M> is not 0)
#! @Description
#! M: A monomial matrix. <M>\newline</M>
#! Find the permutation (in Sym(<M>d</M>)) corresponding to the input monomial matrix.
DeclareGlobalFunction( "PermutationMonomialMatrix" );
DeclareGlobalFunction( "PermutationMonomialMatrixNC" );
#! @EndGroup



#####
# PermSLP()
#####

#! @BeginGroup PermSLPGroup
#! @Arguments stdgens mat slp
#! @Returns slp (A list of instructions to evaluate p_sign if slp was Input then this instructions are added to slp), p_sign (The signed permutation matrix), mat (The diagonal matrix diag)
#! @Description
#! stdgens: The LGO standard-generators <M>\newline</M>
#! mat: A monomial matrix (ie <M>w</M>) <M>\newline</M>
#! slp: An already existing list of instructions *optional <M>\newline</M>
#! In this function we will transform a monomial matrix <M>w \in</M> SL<M>(d,q)</M> into
#! a diagonal matrix diag. Using only the standard-generators <M>s,v,x</M> this
#! will lead to a monomial matrix p_sign with only +-1 in non-zero entries
#! and p_sign*diag = <M>w</M> (i.e. diag = p_sign^-1*w ).
#! Furthermore we will return list slp of instructions which will
#! (when evaluated at the LGO standard-generators) yield diag. <M>\newline</M>
#! It is sufficient for diag to be diagonal, if the permutation associated
#! with <M>w</M> (i.e. <M> i^\pi_w = j </M> if <M> M_{i,j} </M> not 0) is the inverse of the permutation
#! associated to p_sign (again only to Sym(<M> d </M>) ) <M>\newline</M>
#! In PermSLP we thus transform <M>\pi_w</M> to () using only <M>\{ \pi_s, \pi_v, \pi_x \}</M>
#! In order to know diag without computing all matrix multiplications,
#! (we don't know the signs of p_sign), we compute a second permutation
#! simultaneously (here using their identification with permutations in Sym(<M>2d</M>)
#! and identifying <M>\{ \pi_s, \pi_v, \pi_x \}</M> with <M>\{ s,v,x \}</M> )
DeclareGlobalFunction( "PermSLP" );
DeclareGlobalFunction( "PermSLPNC" );
#! @EndGroup



#####
# DiagonalDecomposition()
#####

#! @BeginGroup DiagonalDecompositionGroup
#! @Arguments stdgens diag slp
#! @Returns slp (A list of instructions to evaluate diag if slp was Input then this instructions are added to slp), hres (The the identity matrix)
#! @Description
#! stdgens: The LGO standard-generators <M>\newline</M>
#! diag: A diagonal matrix (eg diag) <M>\newline</M>
#! slp: An already existing list of instructions *optional <M>\newline</M>
#! Writes a list of instructions which evaluated on LGO standard-generators
#! yield the diagonal matrix of the input.
DeclareGlobalFunction( "DiagonalDecomposition" );
DeclareGlobalFunction( "DiagonalDecompositionNC" );
#! @EndGroup



####################
# PART IV
#    Main Functions. Constructs slp for the StraightLineProgram
#####################

#####
# BruhatDecompositionSL()
#####

#! @BeginGroup BruhatDecompositionSLGroup
#! @Arguments stdgens g
#! @Returns pgr (A SLP to compute <M>u_1,u_2,p_{sign}</M> and <M>diag</M> and the matrices <M>u_1, u_2, p_{sign}</M> and <M>diag</M> itself.)
#! @Description
#! stdgens: The LGO standard-generators <M>\newline</M>
#! g: A matrix in SL<M>(d,q)</M> <M>\newline</M>
#! Uses <C>UnipotentDecomposition()</C>, <C>PermSLP()</C> and <C>DiagonalDecomposition()</C>
#! to write a matrix <M>g \in</M> SL<M>(d,q)</M> as <M>g = u_1^{-1} \cdot p_{sign} \cdot diag \cdot u_2^{-1}</M>
#! where <M>u_1,u_2</M> are lower unitriangular matrices, <M>p_{sign}</M> is a monomial matrix
#! with only +1 and -1 as non-zero entries and <M>diag</M> a diagonal matrix.
#! It furthermore yields an SLP that returns the above matrices if evaluated
#! with the LGO standard-generators.
DeclareGlobalFunction( "BruhatDecompositionSL" );
DeclareGlobalFunction( "BruhatDecompositionSLNC" );
#! @EndGroup



#####
# BruhatDecompositionSLWithTi()
#####

#! @BeginGroup BruhatDecompositionSLWithTiGroup
#! @Arguments stdgens g
#! @Returns pgr (A SLP to compute <M>u_1,u_2,p_{sign}</M> and <M>diag</M> and the matrices <M>u_1, u_2, p_{sign}</M> and <M>diag</M> itself.)
#! @Description
#! stdgens: The LGO standard-generators <M>\newline</M>
#! g: A matrix in SL<M>(d,q)</M> <M>\newline</M>
#! As <C>BruhatDecompositionSL()</C> but replaces <C>UnipotentDecomposition()</C>
#! by <C>UnipotentDecompositionWithTi()</C>.
DeclareGlobalFunction( "BruhatDecompositionSLWithTi" );
DeclareGlobalFunction( "BruhatDecompositionSLWithTiNC" );
#! @EndGroup
