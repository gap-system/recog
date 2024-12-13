```
Conformal := ConformalUnitaryGroup(3, 3);
maximalInConformal := [g`subgroup : g in MaximalSubgroups(Conformal)];
groupsWithOrders := [ g : g in maximalInConformal | #g mod (7) eq 0 ];

maximalInOmega := ClassicalMaximals("O+", d, q);
groupsWithOrders := [ g : g in maximalInOmega | #g mod (3*7*13*31) eq 0 ];
```
