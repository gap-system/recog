######################################
# BruhatDecomposition.gi
######################################

#####
# BruhatDecomposition()
#####

InstallGlobalFunction(  BruhatDecomposition,
function(g)
    
    local d, fld, q;
    
    d := Length( g );
    fld := FieldOfMatrixList( [g] );
    q := Size(fld);
   
    if g in Sp(d,q) then
        return BruhatDecompositionSp(LGOStandardGensSp(d,q),g);
    elif g in SU(d,q) then
        return BruhatDecompositionSU(LGOStandardGensSU(d,q),g);
    elif g in SO(1,d,q) then
        return BruhatDecompositionSO(LGOStandardGensSO(1,d,q),g);
    elif g in SO(0,d,q) then
        return BruhatDecompositionSO(LGOStandardGensSO(0,d,q),g);
    elif g in SO(-1,d,q) then
        return BruhatDecompositionSO(LGOStandardGensSO(-1,d,q),g);
    elif g in SL(d,q) then
        return BruhatDecompositionSL(LGOStandardGensSL(d,q),g);
    else
        Print("The element g is not an element of one of the classical groups in their natural representation. \n");
        Print("Abort.");
    fi;

end
);
