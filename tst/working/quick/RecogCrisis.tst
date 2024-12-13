# TODO KernelGeneratorsAlreadyEnlargedByCrisis
# Build the following tree:
# gap> root;
# <failed recognition node
#  F:has no image
#  K:<failed recognition node
#     F:<failed recognition node
#        F:has no image
#        K:<failed recognition node
#           F:has no image
#           K:<failed recognition node
#              F:has no image
#              K:<failed recognition node >>>>
#     K:<trivial kernel>>
gap> G := Group((1,2,3));;
gap> newNode := RecogNode(G);; SetFilterObj(newNode, IsSafeForMandarins);
gap> root := newNode;;
gap> # We mostly add lots of kernels.
gap> r := newNode;; newNode := RecogNode(G);;
gap> SetKernelRecogNode(r, newNode); SetParentRecogNode(newNode, r);
gap> r := newNode;; newNode := RecogNode(G);;
gap> # Here we add an image node and a trivial kernel
gap> SetImageRecogNode(r, newNode); SetParentRecogNode(newNode, r);
gap> SetKernelRecogNode(r, fail);
gap> nodeWithTrivialKernel := r;;
gap> r := newNode;; newNode := RecogNode(G);;
gap> SetKernelRecogNode(r, newNode); SetParentRecogNode(newNode, r);
gap> r := newNode;; newNode := RecogNode(G);;
gap> SetKernelRecogNode(r, newNode); SetParentRecogNode(newNode, r);
gap> r := newNode;; newNode := RecogNode(G);;
gap> SetKernelRecogNode(r, newNode); SetParentRecogNode(newNode, r);
gap> leaf := newNode;; SetFilterObj(leaf, IsLeaf);

# Level 1
gap> crisis := RecogCrisis(leaf);;
gap> crisis!.level;
1
gap> IsIdenticalObj(crisis!.kernelToChop, ParentRecogNode(leaf));
true

# Level 1 with trivial kernel
gap> crisis := RecogCrisis(fail, nodeWithTrivialKernel);;
gap> crisis!.level;
1
gap> crisis!.kernelToChop = fail;
true

# Level 2
gap> SetFilterObj(ParentRecogNode(leaf), KernelGeneratorsAlreadyEnlargedByCrisis);
gap> crisis := RecogCrisis(leaf);;
gap> crisis!.level;
2
gap> IsIdenticalObj(crisis!.kernelToChop, KernelRecogNode(root));
true

# Now make the top most kernel safe
gap> SetFilterObj(KernelRecogNode(root), IsSafeForMandarins);
gap> crisis := RecogCrisis(leaf);;
gap> crisis!.level;
2
gap> IsIdenticalObj(crisis!.kernelToChop,
>                   KernelRecogNode(ImageRecogNode(KernelRecogNode(root))));
true

# Crisis at depth 1
gap> newNode := RecogNode(G);; SetFilterObj(newNode, IsSafeForMandarins);
gap> root := newNode;;
gap> r := newNode;; newNode := RecogNode(G);;
gap> SetKernelRecogNode(r, newNode); SetParentRecogNode(newNode, r);
gap> leaf := newNode;; SetFilterObj(leaf, IsLeaf);
gap> crisis := RecogCrisis(leaf);;
gap> crisis!.level;
1
gap> IsIdenticalObj(crisis!.kernelToChop, leaf);
true
