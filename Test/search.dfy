method Find(a: array?<int>, key: int) returns (idx: int)
  requires a != null
  ensures -1 <= idx < a.Length
  ensures idx >= 0 ==> a[idx] == key
{
  var i := 0;
  idx := -1;
  while i < a.Length && idx == -1
    invariant 0 <= i <= a.Length
    invariant -1 <= idx < a.Length
    invariant idx >= 0 ==> a[idx] == key
    invariant idx == -1 ==> forall j :: 0 <= j < i ==> a[j] != key
  {
    if a[i] == key {
      idx := i;
    }
    i := i + 1;
  }
}