var $Alloc: [ref]bool;
type ref;
function Valid(r: ref): bool;
axiom (forall x: ref :: { Valid(x) } $Alloc[x] ==> Valid(x));
