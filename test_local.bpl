var $Alloc: [ref]bool;
type ref;
procedure foo() {
  var x: ref where $Alloc[x];
}
