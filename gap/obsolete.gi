#############################################################################
##
##  This file is part of recog, a package for the GAP computer algebra system
##  which provides a collection of methods for the constructive recognition
##  of groups.
##
##  This files's authors include Sergio Siccha.
##
##  Copyright of recog belongs to its developers whose names are too numerous
##  to list here. Please refer to the COPYRIGHT file for details.
##
##  SPDX-License-Identifier: GPL-3.0-or-later
##
##
##  Code to stay backwards-compatible.
##
#############################################################################

RECOG_DidPrintObsoleteWarningForEmptyRecognitionInfoRecord := false;
BindGlobal("EmptyRecognitionInfoRecord",
function(r, H, projective)
    if not RECOG_DidPrintObsoleteWarningForEmptyRecognitionInfoRecord then
        Info(InfoObsolete, 1,
             "'EmptyRecognitionInfoRecord' is obsolete.",
             "\n#I  It may be removed in a future release of GAP.",
             "\n#I  Use RecogNode instead.");
        RECOG_DidPrintObsoleteWarningForEmptyRecognitionInfoRecord := true;
    fi;
    return RecogNode(H, projective, r);
end);
