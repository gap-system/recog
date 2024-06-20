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
##  PackageInfo.g for the package `recog'
##
#############################################################################

SetPackageInfo( rec(

PackageName := "recog",
Subtitle := "A package for constructive recognition of permutation and matrix groups",
Version := "1.4.3",
Date := "27/09/2022", # dd/mm/yyyy format
License := "GPL-3.0-or-later",

##  Information about authors and maintainers.
Persons := [
  rec(
    LastName      := "Neunhöffer",
    FirstNames    := "Max",
    IsAuthor      := true,
    IsMaintainer  := false,
    Email         := "max@9hoeffer.de",
  ),
  rec(
    LastName      := "Seress",
    FirstNames    := "Ákos",
    IsAuthor      := true,
    IsMaintainer  := false,
  ),
  rec(
    LastName      := "Bernhardt",
    FirstNames    := "Dominik",
    IsAuthor      := false,
    IsMaintainer  := false, 
    Email         := "bernhardt@mathb.rwth-aachen.de",
    Place         := "Aachen",
    Institution   := "RWTH Aachen University",
    #WWWHome       := "https://www.mathb.rwth-aachen.de/cms/MATHB/Der-Lehrstuhl/Team/Wissenschaftliche-Beschaeftigte/~rnsg/Dominik-Bernhardt/lidx/1/"
  ),
  rec(
    LastName      := "Ankaralioglu",
    FirstNames    := "Nurullah",
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "ankarali@atauni.edu.tr",
  ),
  rec(
    LastName      := "Brooksbank",
    FirstNames    := "Peter",
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "pbrooksb@bucknell.edu",
    Place         := "Lewisburg",
    Institution   := "Bucknell University"
  ),
  rec(
    LastName      := "Celler",
    FirstNames    := "Frank",
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "frank@celler.de",
    Place         := "Aachen",
    Institution   := "Lehrstuhl D für Mathematik, RWTH Aachen",
  ),
rec(
    LastName      := "Hähndel",
    FirstNames    := "Paula",
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "paula.haehndel@mathematik.uni-halle.de",
    WWWHome       := "https://algebra.mathematik.uni-halle.de/haehndel/",
    Place         := "Halle (Saale)",
    Institution   := "Martin-Luther-Universität Halle-Wittenberg"
  ),
  rec(
    LastName      := "Hulpke",
    FirstNames    := "Alexander",
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "hulpke@colostate.edu",
    WWWHome       := "https://www.math.colostate.edu/~hulpke/",
    Place         := "Fort Collins",
    Institution   := "Colorado State University"
  ),
  rec(
    LastName      := "Howe",
    FirstNames    := "Stephen",
    IsAuthor      := false,
    IsMaintainer  := false,
  ),
  rec(
    LastName      := "Jefferson",
    FirstNames    := "Christopher",
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "caj21@st-andrews.ac.uk",
    WWWHome       := "https://caj.host.cs.st-andrews.ac.uk",
    Place         := "St Andrews",
    Institution   := "University of St Andrews"
  ),
  rec(
    LastName      := "Law",
    FirstNames    := "Maska",
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "maska@maths.uwa.edu.au",
    Place         := "Perth",
    Institution   := "University of Western Australia"
  ),
  rec(
    LastName      := "Linton",
    FirstNames    := "Steve",
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "sal@cs.st-andrews.ac.uk",
    WWWHome       := "http://www-groups.mcs.st-and.ac.uk/~sal",
    Place         := "St Andrews",
    Institution   := "University of St Andrews"
  ),
  rec(
    LastName      := "Malle",
    FirstNames    := "Gunter",
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "malle@mathematik.uni-kl.de",
    WWWHome       := "https://www.mathematik.uni-kl.de/~malle/",
    Place         := "Kaiserslautern",
    Institution   := "Universität Kaiserslautern",
  ),
  rec(
    LastName      := "Niemeyer",
    FirstNames    := "Alice",
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "alice.niemeyer@mathb.rwth-aachen.de",
    WWWHome       := "http://www.math.rwth-aachen.de/~Alice.Niemeyer/",
    Place         := "Aachen",
    Institution   := "RWTH Aachen University"
  ),
  rec(
    LastName      := "O'Brien",
    FirstNames    := "Eamonn",
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "e.obrien@auckland.ac.nz",
    WWWHome       := "https://www.math.auckland.ac.nz/~obrien/",
    Place         := "Auckland",
    Institution   := "University of Auckland",
  ),
  rec(
    LastName      := "Roney-Dougal",
    FirstNames    := "Colva M.",
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "colva@mcs.st-and.ac.uk",
    WWWHome       := "http://www-groups.mcs.st-and.ac.uk/~colva",
    Place         := "St Andrews",
    Institution   := "University of St Andrews"
  ),
  rec(
    LastName      := "Horn",
    FirstNames    := "Max",
    IsAuthor      := false,
    IsMaintainer  := true,
    Email         := "mhorn@rptu.de",
    WWWHome       := "https://www.quendi.de/math",
    Place         := "Kaiserslautern",
    Institution   := "RPTU Kaiserslautern-Landau"
  ),
 rec(
    LastName      := "Siccha",
    FirstNames    := "Sergio",
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "sergio@mathb.rwth-aachen.de",
    #WWWHome       := "https://www.mathematik.rwth-aachen.de/go/id/bkbg/gguid/0x28CF75713F0B7744BEF1377FB3F6748E/ikz/11/allou/1/lidx/1/",
    Place         := "Aachen",
    Institution   := "RWTH Aachen University"
  ), 
  rec(
    LastName      := "Wilson",
    FirstNames    := "Wilf",
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "gap@wilf-wilson.net",
    WWWHome       := "https://wilf.me"
  ),
rec(
    LastName      := "Whybrow",
    FirstNames    := "Madeleine",
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "madeleine.whybrow@famnit.upr.si",
    WWWHome       := "https://madeleinewhybrow.wordpress.com/contact/",
    Place         := "Primorska",
    Institution   := "University of Primorska"
  ),
],

##  Status information. Currently the following cases are recognized:
##    "accepted"      for successfully refereed packages
##    "deposited"     for packages for which the GAP developers agreed
##                    to distribute them with the core GAP system
##    "dev"           for development versions of packages
##    "other"         for all other packages
##
# Status := "accepted",
Status := "deposited",

##  You must provide the next two entries if and only if the status is
##  "accepted" because is was successfully refereed:
# format: 'name (place)'
# CommunicatedBy := "Mike Atkinson (St. Andrews)",
#CommunicatedBy := "",
# format: mm/yyyy
# AcceptDate := "08/1999",
#AcceptDate := "",

SourceRepository := rec(
    Type := "git",
    URL := Concatenation( "https://github.com/gap-packages/", ~.PackageName ),
),
IssueTrackerURL := Concatenation( ~.SourceRepository.URL, "/issues" ),
PackageWWWHome  := Concatenation( "https://gap-packages.github.io/", ~.PackageName ),
README_URL      := Concatenation( ~.PackageWWWHome, "/README.md" ),
PackageInfoURL  := Concatenation( ~.PackageWWWHome, "/PackageInfo.g" ),
ArchiveURL      := Concatenation( ~.SourceRepository.URL,
                                 "/releases/download/v", ~.Version,
                                 "/", ~.PackageName, "-", ~.Version ),
ArchiveFormats := ".tar.gz .tar.bz2",

##  Here you  must provide a short abstract explaining the package content
##  in HTML format (used on the package overview Web page) and an URL
##  for a Webpage with more detailed information about the package
##  (not more than a few lines, less is ok):
##  Please, use '<span class="pkgname">GAP</span>' and
##  '<span class="pkgname">MyPKG</span>' for specifing package names.
##
AbstractHTML := """
    <p><b>Warning:</b> This package is still under development and
    this version is to be considered a working, but preliminary one.</p>

    <p>This package contains a collection of methods for the
    constructive recognition of groups. It is mostly intended for
    permutation groups, matrix groups and projective groups.</p>
    """,

PackageDoc := rec(
  BookName  := "recog",
  ArchiveURLSubset := ["doc"],
  HTMLStart := "doc/chap0_mj.html",
  PDFFile   := "doc/manual.pdf",
  SixFile   := "doc/manual.six",
  LongTitle := "A collection of group recognition methods",
),

Dependencies := rec(
  GAP := ">=4.11",
  NeededOtherPackages := [
    ["AtlasRep", ">= 1.4.0"],
    ["Alnuth", ">= 3.2.1"],
    ["FactInt", ">= 1.5.2"],
    ["Forms", ">= 1.2"],
    ["genss", ">= 1.3"],
    ["Orb", ">= 3.4"],
  ],
  SuggestedOtherPackages := [],
  ExternalConditions := []
),

AvailabilityTest := ReturnTrue,
TestFile := "tst/testquick.g",

Keywords := ["group recognition", "matrix group recognition",
"permutation group", "black box group", "composition tree",
"Aschbacher classes", "method selection"],

AutoDoc := rec(
    TitlePage := rec(
        Copyright := Concatenation(
                    "&copyright; 2005-2014 by Max Neunhöffer and Ákos Seress<P/>\n",
                    "&copyright; 2005-2022 by its authors, see file <F>COPYRIGHT</F> for details.<P/>\n",
                    "\n",
                    "This package may be distributed under the terms and conditions of the\n",
                    "GNU Public License Version 3 or (at your option) any later version.\n"
                ),
    )
),

));
