#
# BruhatDecomposition: Computes the Bruhat Decomposition of matrices of the classical groups.
#

gap> TestBruhatDecompositionSLPSL := function()
>    local counter, g, G, res, d, GG, stdgens, diag, slp, tmpvalue, c, P, u1, u2, mon;
>    P := [2,4,8,16,32,3,9,27,5,5^2,7,7^2];
>    
>    for d in [6..13] do
>        for c in P do
>            stdgens := LGOStandardGensSL(d,c);
>            G := GroupByGenerators(stdgens);
>            Print("Dimension: ");
>            Print(d);
>            Print(",Ordnung: ");
>            Print(c);
>            Print("\n");
>            counter := 1;
>            while counter < 100 do
>                g := PseudoRandom(G);
>                res := BruhatDecompositionSL(stdgens,g);
>                slp := res[1];
>                slp := ResultOfStraightLineProgram(slp,stdgens);
>                res := res[2];
>                u1 := res[1];
>                u2 := res[2];
>                mon := res[3];
>                diag := res[4];
>                if (slp[1]^(-1)*slp[3]*slp[4]*slp[2]^(-1) <> g) then
>                    Error("Wrong matrix.");
>                fi;
>                Display(counter);
>                counter := counter +1;
>            od;
>        od;
>    od;
>
> end;;


gap> TestBruhatDecompositionSLPSLNC := function()
>    local counter, g, G, res, d, GG, stdgens, diag, slp, tmpvalue, c, P, u1, u2, mon;
>    P := [2,4,8,16,32,3,9,27,5,5^2,7,7^2];
>    
>    for d in [6..13] do
>        for c in P do
>            stdgens := LGOStandardGensSL(d,c);
>            G := GroupByGenerators(stdgens);
>            Print("Dimension: ");
>            Print(d);
>            Print(",Ordnung: ");
>            Print(c);
>            Print("\n");
>            counter := 1;
>            while counter < 100 do
>                g := PseudoRandom(G);
>                res := BruhatDecompositionSLNC(stdgens,g);
>                slp := res[1];
>                slp := ResultOfStraightLineProgram(slp,stdgens);
>                res := res[2];
>                u1 := res[1];
>                u2 := res[2];
>                mon := res[3];
>                diag := res[4];
>                if (slp[1]^(-1)*slp[3]*slp[4]*slp[2]^(-1) <> g) then
>                    Error("Wrong matrix.");
>                fi;
>                Display(counter);
>                counter := counter +1;
>            od;
>        od;
>    od;
>
> end;;


gap> TestBruhatDecompositionSLPSp := function()
>    local counter, g, G, res, d, GG, stdgens, diag, slp, tmpvalue, c, P, u1, u2, mon;
>    P := [2,4,8,16,32,3,9,27,5,5^2,7,7^2];
>    
>    for d in Filtered([6..13], x-> x mod 2 = 0) do
>        for c in P do
>            if c mod 2 = 0 then
>                 stdgens := LGOStandardGensSpEvenChar(d,c);
>            else
>                 stdgens := LGOStandardGensSp(d,c);
>            fi;
>            G := GroupByGenerators(stdgens);
>            Print("Dimension: ");
>            Print(d);
>            Print(",Ordnung: ");
>            Print(c);
>            Print("\n");
>            counter := 1;
>            while counter < 100 do
>                g := PseudoRandom(G);
>                res := BruhatDecompositionSp(stdgens,g);
>                slp := res[1];
>                slp := ResultOfStraightLineProgram(slp,stdgens);
>                res := res[2];
>                u1 := res[1];
>                u2 := res[2];
>                mon := res[3];
>                diag := res[4];
>                if (slp[1]^(-1)*slp[3]*slp[4]*slp[2]^(-1) <> g) then
>                    Error("Wrong matrix.");
>                fi;
>                Display(counter);
>                counter := counter +1;
>            od;
>        od;
>    od;
>
> end;;



gap> TestBruhatDecompositionSLPSU := function()
>    local counter, g, G, res, d, GG, stdgens, diag, slp, tmpvalue, c, P, u1, u2, mon;
>    P := [2,4,8,16,32,3,9,27,5,5^2,7,7^2];
>    
>    for d in [6..13] do
>        for c in P do
>            if c mod 2 = 0 then
>                  stdgens := LGOStandardGensSUEvenChar(d,c);
>            else
>                  stdgens := LGOStandardGensSU(d,c);
>            fi;
>            G := GroupByGenerators(stdgens);
>            Print("Dimension: ");
>            Print(d);
>            Print(",Ordnung: ");
>            Print(c);
>            Print("\n");
>            counter := 1;
>            while counter < 100 do
>                g := PseudoRandom(G);
>                res := BruhatDecompositionSU(stdgens,g);
>                slp := res[1];
>                slp := ResultOfStraightLineProgram(slp,stdgens);
>                res := res[2];
>                u1 := res[1];
>                u2 := res[2];
>                mon := res[3];
>                diag := res[4];
>                if (slp[1]^(-1)*slp[3]*slp[4]*slp[2]^(-1) <> g) then
>                    Error("Wrong matrix.");
>                fi;
>                Display(counter);
>                counter := counter +1;
>            od;
>        od;
>    od;
>
> end;



gap> TestBruhatDecompositionSLPSO := function()
>    local counter, g, G, res, d, GG, stdgens, diag, slp, tmpvalue, c, P, u1, u2, mon;
>    P := [3,9,27,5,5^2,7,7^2,11,13,11^2,17];
>    
>    Display("Plus case.");
>    for d in Filtered([6..13], x-> x mod 2 = 0) do
>       for c in P do
>            if c mod 2 = 0 then
>                  stdgens := LGOStandardGensOmega(1,d,c);
>            else
>                  stdgens := LGOStandardGensSO(1,d,c);
>            fi;
>            G := GroupByGenerators(stdgens);
>            Print("Dimension: ");
>            Print(d);
>            Print(",Ordnung: ");
>            Print(c);
>            Print("\n");
>            counter := 1;
>            while counter < 100 do
>                g := PseudoRandom(G);
>                res := BruhatDecompositionSO(stdgens,g);
>                slp := res[1];
>                slp := ResultOfStraightLineProgram(slp,stdgens);
>                res := res[2];
>                u1 := res[1];
>                u2 := res[2];
>                mon := res[3];
>                diag := res[4];
>                if (slp[1]^(-1)*slp[3]*slp[4]*slp[2]^(-1) <> g) then
>                    Error("Wrong matrix.");
>                fi;
>                Display(counter);
>                counter := counter +1;
>            od;
>        od;
>    od;
>
>    Display("Circle case.");
>    for d in Filtered([6..13], x-> x mod 2 = 1) do
>        for c in P do
>            if c mod 2 = 0 then
>                  stdgens := LGOStandardGensOmega(0,d,c);
>            else
>                  stdgens := LGOStandardGensSO(0,d,c);
>            fi;
>            G := GroupByGenerators(stdgens);
>            Print("Dimension: ");
>            Print(d);
>            Print(",Ordnung: ");
>            Print(c);
>            Print("\n");
>            counter := 1;
>            while counter < 100 do
>                g := PseudoRandom(G);
>                res := BruhatDecompositionSO(stdgens,g);
>                slp := res[1];
>                slp := ResultOfStraightLineProgram(slp,stdgens);
>                res := res[2];
>                u1 := res[1];
>                u2 := res[2];
>                mon := res[3];
>                diag := res[4];
>                if (slp[1]^(-1)*slp[3]*slp[4]*slp[2]^(-1) <> g) then
>                    Error("Wrong matrix.");
>                fi;
>                Display(counter);
>                counter := counter +1;
>            od;
>        od;
>    od;
>
>    Display("Minus case.");
>    for d in Filtered([8..15], x-> x mod 2 = 0) do
>        for c in P do
>           if c mod 2 = 0 then
>                  stdgens := LGOStandardGensOmega(-1,d,c);
>           else
>                  stdgens := LGOStandardGensSO(-1,d,c);
>            fi;
>            G := GroupByGenerators(stdgens);
>            Print("Dimension: ");
>            Print(d);
>            Print(",Ordnung: ");
>            Print(c);
>            Print("\n");
>            counter := 1;
>            while counter < 100 do
>                g := PseudoRandom(G);
>                res := BruhatDecompositionSOMinus(stdgens,g);
>                slp := res[1];
>                slp := ResultOfStraightLineProgram(slp,stdgens);
>                res := res[2];
>                u1 := res[1];
>                u2 := res[2];
>                mon := res[3];
>                diag := res[4];
>                if (slp[1]^(-1)*slp[3]*slp[4]*slp[2]^(-1) <> g) then
>                    Error("Wrong matrix.");
>                fi;
>                Display(counter);
>                counter := counter +1;
>            od;
>        od;
>    od;
>
> end;;



gap> TestBruhatDecompositionSLPOmega := function()
>    local counter, g, G, res, d, GG, stdgens, diag, slp, tmpvalue, c, P, u1, u2, mon;
>    P := [2,4,8,16,32,3,9,27,5,5^2,7,7^2];
>    
>    for d in Filtered([6..20], x-> x mod 2 = 0) do
>        for c in P do
>            stdgens := LGOStandardGensOmega(1,d,c);
>            G := GroupByGenerators(stdgens);
>            Print("Dimension: ");
>            Print(d);
>            Print(",Ordnung: ");
>            Print(c);
>            Print("\n");
>            counter := 1;
>            while counter < 100 do
>                g := PseudoRandom(G);
>                # BruhatDecompositionOmega
>                res := BruhatDecompositionSO(stdgens,g);
>                slp := res[1];
>                slp := ResultOfStraightLineProgram(slp,stdgens);
>                res := res[2];
>                u1 := res[1];
>                u2 := res[2];
>                mon := res[3];
>                diag := res[4];
>                if (slp[1]^(-1)*slp[3]*slp[4]*slp[2]^(-1) <> g) then
>                    Error("Wrong matrix.");
>                fi;
>                Display(counter);
>                counter := counter +1;
>            od;
>        od;
>    od;
>
>    for d in Filtered([6..20], x-> x mod 2 = 1) do
>        for c in P do
>           stdgens := LGOStandardGensOmega(0,d,c);
>            G := GroupByGenerators(stdgens);
>            Print("Dimension: ");
>            Print(d);
>            Print(",Ordnung: ");
>            Print(c);
>            Print("\n");
>            counter := 1;
>            while counter < 100 do
>                g := PseudoRandom(G);
>                # BruhatDecompositionOmega
>                res := BruhatDecompositionSO(stdgens,g);
>                slp := res[1];
>                slp := ResultOfStraightLineProgram(slp,stdgens);
>                res := res[2];
>                u1 := res[1];
>                u2 := res[2];
>                mon := res[3];
>                diag := res[4];
>                if (slp[1]^(-1)*slp[3]*slp[4]*slp[2]^(-1) <> g) then
>                    Error("Wrong matrix.");
>                fi;
>                Display(counter);
>                counter := counter +1;
>            od;
>        od;
>    od;
>
>    for d in Filtered([6..20], x-> x mod 2 = 0) do
>        for c in P do
>           stdgens := LGOStandardGensOmega(-1,d,c);
>            G := GroupByGenerators(stdgens);
>            Print("Dimension: ");
>            Print(d);
>            Print(",Ordnung: ");
>            Print(c);
>            Print("\n");
>            counter := 1;
>            while counter < 100 do
>                g := PseudoRandom(G);
>                # BruhatDecompositionOmega
>                res := BruhatDecompositionSO(stdgens,g);
>                slp := res[1];
>                slp := ResultOfStraightLineProgram(slp,stdgens);
>                res := res[2];
>                u1 := res[1];
>                u2 := res[2];
>                mon := res[3];
>                diag := res[4];
>                if (slp[1]^(-1)*slp[3]*slp[4]*slp[2]^(-1) <> g) then
>                    Error("Wrong matrix.");
>                fi;
>                counter := counter +1;
>            od;
>        od;
>    od;
>
> end;;

gap> Display("Test SL\n");;
gap> TestBruhatDecompositionSLPSL();;
gap> Display("Test SLNC\n");;
gap> TestBruhatDecompositionSLPSLNC();;
gap> Display("Test Sp\n");;
gap> TestBruhatDecompositionSLPSp();;
gap> Display("Test SU\n");;
gap> TestBruhatDecompositionSLPSU();;
gap> Display("Test SO\n");;
gap> TestBruhatDecompositionSLPSO();;
# TestBruhatDecompositionSLPOmega();;
gap> Print("Everything worked! Congrats!\n");;

