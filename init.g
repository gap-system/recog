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
##  Reading the declaration part of the recog package.
##
#############################################################################

ReadPackage("recog","gap/base/hack.g");
ReadPackage("recog","gap/base/methods.gd");
ReadPackage("recog","gap/base/methsel.gd");
ReadPackage("recog","gap/base/recognition.gd");
ReadPackage("recog","gap/base/kernel.gd");

# The following contain generic declarations for different types of groups:
ReadPackage("recog","gap/base/projective.gd");

ReadPackage("recog","gap/matrix.gd");

ReadPackage("recog","gap/matrix/ppd.gd");
ReadPackage("recog","gap/matrix/classical.gd");
ReadPackage("recog","gap/matrix/wordsInNiceGens/BruhatDecomposition.gd");
ReadPackage("recog","gap/matrix/wordsInNiceGens/BruhatDecompositionSL.gd");
ReadPackage("recog","gap/matrix/wordsInNiceGens/BruhatDecompositionSU.gd");
ReadPackage("recog","gap/matrix/wordsInNiceGens/BruhatDecompositionSp.gd");
ReadPackage("recog","gap/matrix/wordsInNiceGens/BruhatDecompositionO.gd");
ReadPackage("recog","gap/projective/almostsimple.gd");
ReadPackage("recog","gap/projective/findnormal.gd");
ReadPackage("recog","gap/projective/AnSnOnFDPM.gd");
