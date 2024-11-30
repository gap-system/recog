#############################################################################
# BruhatDecomposition.gd
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
#
#! @Chapter Foreword
#!
#! Let <M>G</M> be one of the classical groups SL, Sp, SU or SO over a finite field of size <M>q</M> and dimension <M>d</M>. Let g be an element in G.
#! We want to write <M>g = u_1 \cdot w \cdot u_2</M> with <M>u_1</M> and <M>u_2</M> lower unitriangular matrices and <M>w</M> a monomial matrix. <P/>
#! This is already implemented for:
#! <List>
#!     <Item>
#!     Special linear group (SL) (see Chapter <Ref Sect="Chapter_SpecialLinearGroup"/>)
#!     </Item>
#!     <Item>
#!     Symplectic group (Sp) (see Chapter <Ref Sect="Chapter_SymplecticGroup"/>)
#!     </Item>
#!     <Item>
#!     Special unitary group (SU) (see Chapter <Ref Sect="Chapter_SpecialUnitaryGroup"/>)
#!     </Item>
#!     <Item>
#!     Special orthogonal group (SO) (see Chapter <Ref Sect="Chapter_SpecialOrthogonalGroup"/>)
#!     </Item>
#! </List>



#! @Section Main Function
#! @SectionLabel MainFunction

#####
# BruhatDecomposition()
#####

#! @Arguments g
#! @Returns pgr (A SLP to compute <M>u_1,u_2,p_{sign}</M> and <M>diag</M> and the matrices <M>u_1, u_2, p_{sign}</M> and <M>diag</M> itself.)
#! @Description
#! Checks whether <M>g</M> is an element of one of the classical groups in their natural representation. If yes, the corresponding Bruhat decomposition of the group and the element <M>g</M> is calculated. Otherwise the function prints a warning.
DeclareGlobalFunction( "BruhatDecomposition" );
