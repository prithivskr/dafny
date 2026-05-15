var $Alloc: [ref]bool;
type ref;
procedure foo(x: ref where $Alloc[x]) {
  assert x == x;
}
