- IsReady: only is not set when no recognition method was able to recognise a
  node in the tree.
- make in the package RecognizeGeneric only be called with RecogNodes
  this would enable us to get rid of `depthstring`
- IsSafeForMandarins: recog method should know whether there is a deterministic
  function to compute its kernel. Name isFindGensNMethDeterministic?
  => operation with two methods
  - IsRecogNode: go check on successmethod
  - IsRecogMethod: take its component
  => findGensNmeth: is it ever set by anything but recognition methods? If not,
  we can store it in the recog method.
- ValidateHomomInput: everybody must set hasvalidatehomominput! Can we make
  this a required component of the recognition method? 
- Enforce that every recog method provides a way to SetNiceGens?
