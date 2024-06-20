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
##  This files builds the documentation of the recog package. Running it
##  requires the GAPDoc and AutoDoc GAP packages, as well as pdflatex.
##
##  Run it with GAP from within the package directory.
##
#############################################################################

if fail = LoadPackage("AutoDoc", ">= 2019.07.03") then
    ErrorNoReturn("AutoDoc 2019.07.03 or newer is required");
fi;

Read(Filename(DirectoryCurrent(), "regen_doc.g"));

scan_dirs := [
    "doc",
    "gap",
    "gap/base",
    "gap/generic",
    "gap/matrix",
    "gap/perm",
    "gap/projective",
    "gap/projective/almostsimple",
    "gap/projective/constructive_recognition",
    "gap/projective/constructive_recognition/SL",
    "gap/projective/constructive_recognition/utils",
    ];

AutoDoc(rec(
    autodoc := rec( scan_dirs := scan_dirs ),
    gapdoc := rec( scan_dirs := scan_dirs ),
    scaffold := rec(
        bib := "recog",
        includes := [
            "intro.xml",
            "install.xml",
            "recognition.xml",
            "methsel.xml",
            "afterrecog.xml",
            "methods.xml",
            "examples.xml",
            "renaming.xml",
            ],
        ),
));
