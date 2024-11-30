#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
##
##  Reading the implementation part of the recog package.
##
#############################################################################

# Generic:
ReadPackage("recog","gap/base/methods.gi");
ReadPackage("recog","gap/base/methsel.gi");
ReadPackage("recog","gap/base/recognition.gi");
ReadPackage("recog","gap/base/kernel.gi");

# The following contain generic functionality for different types of groups:

# Projective:
ReadPackage("recog","gap/base/projective.gi");


# Some tools:
ReadPackage("recog","gap/utils.gi");

# generic
ReadPackage("recog","gap/generic/TrivialGroup.gi");
ReadPackage("recog","gap/generic/FewGensAbelian.gi");
ReadPackage("recog","gap/generic/KnownNilpotent.gi");

# Permutations:
ReadPackage("recog","gap/perm/giant.gi");
ReadPackage("recog","gap/perm/largebase.gi");
ReadPackage("recog","gap/SnAnBB.gi");
ReadPackage("recog","gap/generic/SnAnUnknownDegree.gi");

# Matrices/Projective:
ReadPackage("recog","gap/projective/findnormal.gi");
ReadPackage("recog","gap/matrix/matimpr.gi");
ReadPackage("recog","gap/projective/c6.gi");
ReadPackage("recog","gap/projective/tensor.gi");
ReadPackage("recog","gap/matrix/ppd.gi");
ReadPackage("recog","gap/matrix/classical.gi");
ReadPackage("recog","gap/matrix/slconstr.gi");
ReadPackage("recog","gap/matrix/wordsInNiceGens/BruhatDecomposition.gi");
ReadPackage("recog","gap/matrix/wordsInNiceGens/BruhatDecompositionSL.gi");
ReadPackage("recog","gap/matrix/wordsInNiceGens/BruhatDecompositionSU.gi");
ReadPackage("recog","gap/matrix/wordsInNiceGens/BruhatDecompositionSp.gi");
ReadPackage("recog","gap/matrix/wordsInNiceGens/BruhatDecompositionO.gi");
ReadPackage("recog","gap/projective/c3c5.gi");
ReadPackage("recog","gap/projective/d247.gi");
ReadPackage("recog","gap/projective/almostsimple/threeelorders.gi");
ReadPackage("recog","gap/projective/almostsimple.gi");
ReadPackage("recog","gap/projective/almostsimple/lietype.gi");
ReadPackage("recog","gap/projective/almostsimple/hints.gi");
ReadPackage("recog","gap/projective/classicalnatural.gi");
ReadPackage("recog","gap/projective/AnSnOnFDPM.gi");

# All the method installations are now here:
ReadPackage("recog","gap/perm.gi");
ReadPackage("recog","gap/matrix.gi");
ReadPackage("recog","gap/projective.gi");
