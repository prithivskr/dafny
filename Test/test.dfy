// --- Algebraic datatype ---
datatype List = Nil | Cons(head: int, tail: List)

// Recursive function with QF pre/post
// (recursive body, but spec is QF)
function ListLength(l: List): nat
  decreases l
{
  match l
  case Nil => 0
  case Cons(_, t) => 1 + ListLength(t)
}

function ListHead(l: List): int
  requires l != Nil
{
  l.head
}

// --- Ghost lemma ---
ghost method LengthPositive(l: List)
  requires l != Nil
  ensures ListLength(l) >= 1
{
  // trivial by unfolding
}

// --- Simple class with heap ---
class Counter {
  var value: int
  var limit: int

  constructor(lim: int)
    requires lim >= 0
    ensures value == 0
    ensures limit == lim
  {
    value := 0;
    limit := lim;
  }

  method Increment()
    requires value < limit
    ensures value == old(value) + 1
    ensures limit == old(limit)
    modifies this
  {
    value := value + 1;
  }

  method Reset()
    ensures value == 0
    ensures limit == old(limit)
    modifies this
  {
    value := 0;
  }
}

// --- Array method with loop invariant ---
method SumArray(a: array<int>) returns (s: int)
  requires a.Length >= 1
  ensures s >= 0 || s < 0  // trivially QF postcondition
{
  s := 0;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant i >= 0
  {
    s := s + a[i];
    i := i + 1;
  }
}

// --- Method using the ADT ---
method ProcessList(l: List) returns (n: int)
  requires l != Nil
  ensures n >= 1
{
  ghost var len := ListLength(l);
  LengthPositive(l);
  n := 0;
  var cur := l;
  while cur != Nil
    invariant n >= 0
    invariant n + ListLength(cur) == ListLength(l)
    decreases ListLength(cur)
  {
    n := n + 1;
    match cur {
      case Nil => // unreachable
      case Cons(_, t) => cur := t;
    }
  }
}

// --- Method using class + array together ---
method FillAndCount(c: Counter, a: array<int>) returns (total: int)
  requires c.value >= 0
  requires c.limit >= 0
  requires a.Length >= 1
  ensures total >= 0
  modifies c
{
  c.Reset();
  total := 0;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant total >= 0
    invariant c.value == 0
  {
    if a[i] > 0 {
      total := total + a[i];
    }
    i := i + 1;
  }
}