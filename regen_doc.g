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
##  Regenerate parts of the recog documentation from its source code
##
#############################################################################

# We need the precise version of recog contained in the current directory; if
# recog is not yet loaded, that's no problem; otherwise, we need to work a bit
# to verify that this is the case, and otherwise exit with an error Reading
# the implementation part of the recog package.
if not IsBound(GAPInfo.PackagesLoaded.recog) then
    SetPackagePath("recog", "./");
    LoadPackage("recog");
else
    loadedPath := GAPInfo.PackagesLoaded.recog[1];
    # ask bash whether that path corresponds to the current directory
    testPath := DirectoriesSystemPrograms();
    testPath := Filename(testPath, "test");
    res := Process( DirectoryCurrent(), testPath,
                    InputTextNone(), OutputTextNone(),
                    [ GAPInfo.PackagesLoaded.recog[1], "-ef", "." ] );
    if res <> 0 then
        ErrorNoReturn("a different version of recog was already loaded or you ",
                      "started GAP in the wrong directory; try ",
                      "`gap -A regen_doc.g` or `gap -A makedoc.g`");
    fi;
fi;

DbsWhichUseMethod := function(methodsRecord, methodName)
    local result, method, methodDbs, types, db, i;
    result := [];
    method := methodsRecord.(methodName);
    methodDbs := [FindHomDbPerm, FindHomDbMatrix, FindHomDbProjective];
    types := ["permutation", "matrix", "projective"];
    for i in [1..Length(methodDbs)] do
        db := methodDbs[i];
        if ForAny(db, x -> Stamp(x.method) = Stamp(method)) then
            Add(result, types[i]);
        fi;
    od;
    return result;
end;

ListOfUnusedMethods := function()
    local unusedMethods, methodRecords, methodRecordsNames, collection,
        collectionName, i, methodName;
    unusedMethods := [];
    methodRecordsNames := ["FindHomMethodsGeneric", "FindHomMethodsPerm",
                           "FindHomMethodsMatrix", "FindHomMethodsProjective"];
    for collectionName in methodRecordsNames do
        collection := ValueGlobal(collectionName);
        for methodName in RecNames(collection) do
            if IsEmpty(DbsWhichUseMethod(collection, methodName)) then
                Add(unusedMethods, [methodName, collectionName]);
            fi;
        od;
    od;
    return unusedMethods;
end;

GenerateMethodsTableXML := function(shortname, desc, db)
local dir, xmlfile, meth;

    dir := Filename(DirectoryCurrent(), "");
    xmlfile := Concatenation(dir, "doc/_methods_", shortname, "_table.xml");
    xmlfile := OutputTextFile(xmlfile, false);
    SetPrintFormattingStatus(xmlfile, false);

    PrintTo(xmlfile, "<Table Align=\"|l|l|l|l|\">\n");
    AppendTo(xmlfile, "<Caption>", desc, " group find homomorphism methods</Caption>\n");
    AppendTo(xmlfile, "<HorLine/>\n");

    SortBy(db, x -> -x.rank);
    for meth in db do
        AppendTo(xmlfile, "<Row>\n");
        AppendTo(xmlfile, "<Item>", meth.rank, "</Item>\n");
        AppendTo(xmlfile, "<Item><C>", Stamp(meth.method), "</C></Item>\n");
        AppendTo(xmlfile, "<Item>", Comment(meth.method), "</Item>\n");
        AppendTo(xmlfile, "<Item><Ref Subsect=\"", Stamp(meth.method), "\"/></Item>\n");
        AppendTo(xmlfile, "</Row>\n");
        AppendTo(xmlfile, "<HorLine/>\n");
    od;

    AppendTo(xmlfile, "</Table>\n");

    CloseStream(xmlfile);

end;

GenerateUnusedMethodsTableXML := function()
    local xmlfile, meth;

    xmlfile := Filename(DirectoryCurrent(), "doc/_methods_unused_table.xml");
    xmlfile := OutputTextFile(xmlfile, false);
    SetPrintFormattingStatus(xmlfile, false);

    PrintTo(xmlfile, "<Table Align=\"|l|l|l|\">\n");
    AppendTo(xmlfile, "<Caption>Unused group find homomorphism methods</Caption>\n");
    AppendTo(xmlfile, "<HorLine/>\n");

    for meth in ListOfUnusedMethods() do
        AppendTo(xmlfile, "<Row>\n");
        AppendTo(xmlfile, "<Item><C>", meth[1], "</C></Item>\n");
        AppendTo(xmlfile, "<Item><C>", meth[2], "</C></Item>\n");
        AppendTo(xmlfile, "<Item><Ref Subsect=\"", meth[1], "\"/></Item>\n");
        AppendTo(xmlfile, "</Row>\n");
        AppendTo(xmlfile, "<HorLine/>\n");
    od;

    AppendTo(xmlfile, "</Table>\n");

    CloseStream(xmlfile);

end;

GenerateMethodsListXML := function(shortname, db)
    local dir, xmlfile, dbsWhichUseMethod, nrDbsWhichUseMethod, s, meth;

    dir := Filename(DirectoryCurrent(), "");
    xmlfile := Concatenation(dir, "doc/_methods_", shortname, "_list.xml");
    xmlfile := OutputTextFile(xmlfile, false);
    SetPrintFormattingStatus(xmlfile, false);

    for meth in Set(RecNames(db)) do
        AppendTo(xmlfile, "<Subsection Label=\"", meth, "\">\n");
        AppendTo(xmlfile, "<Heading><C>", meth, "</C></Heading>\n");
        # Where is this method used?
        AppendTo(xmlfile, "This method is ");
        dbsWhichUseMethod := DbsWhichUseMethod(db, meth);
        nrDbsWhichUseMethod := Length(dbsWhichUseMethod);
        if nrDbsWhichUseMethod = 0 then
            AppendTo(xmlfile, "unused!");
        else
            s := "used for recognizing ";
            Append(s, JoinStringsWithSeparator(dbsWhichUseMethod{[1 .. nrDbsWhichUseMethod - 1]},
                                               ", "));
            if nrDbsWhichUseMethod = 2 then
                Append(s, " and ");
            elif nrDbsWhichUseMethod = 3 then
                Append(s, ", and ");
            fi;
            Append(s, dbsWhichUseMethod[nrDbsWhichUseMethod]);
            Append(s, " groups.");
            AppendTo(xmlfile, s);
        fi;
        AppendTo(xmlfile, "<P/>\n");
        AppendTo(xmlfile, "<#Include Label=\"", meth, "\">\n");
        AppendTo(xmlfile, "</Subsection>\n");
   od;

    CloseStream(xmlfile);

end;

GenerateMethodsTableXML("matrix", "Matrix", FindHomDbMatrix);
GenerateMethodsTableXML("perm", "Permutation", FindHomDbPerm);
GenerateMethodsTableXML("proj", "Projective", FindHomDbProjective);

GenerateUnusedMethodsTableXML();

GenerateMethodsListXML("generic", FindHomMethodsGeneric);
GenerateMethodsListXML("matrix", FindHomMethodsMatrix);
GenerateMethodsListXML("perm", FindHomMethodsPerm);
GenerateMethodsListXML("proj", FindHomMethodsProjective);
