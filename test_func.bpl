var $Alloc: [ref]bool;
type ref;
function Valid(r: ref): bool {
  $Alloc[r]
}
