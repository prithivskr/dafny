// Natural-proofs style (Madhusudan et al.): the recursive definitions are
// OPAQUE, so the solver never receives their quantified defining axioms.
// Each proof consists of a handful of unfoldings of the definitions at
// specific terms, after which quantifier-free SMT reasoning closes the VC.
//
// `ftpt` is the node's heaplet (the Dryad footprint). Dafny's frame axiom for
// `reads` clauses plays the role of the separation-logic frame rule, so no
// inductive framing lemma is needed.

class Node {
  var data: int
  var next: Node?
  ghost var ftpt: set<Node>

  constructor (d: int, nx: Node?, ghost f: set<Node>)
    ensures data == d && next == nx && ftpt == {this} + f
  {
    data := d;
    next := nx;
    ftpt := {this} + f;
  }
}

// ---------------------------------------------------------------------------
// Recursive definitions. Both are total: the guards make them well defined on
// any heap, so neither needs a precondition, and both are opaque.
// ---------------------------------------------------------------------------

ghost predicate {:opaque} List(n: Node?)
  reads if n == null then {} else {n} + n.ftpt
  decreases if n == null then 0 else |n.ftpt|
{
  n == null ||
  (n in n.ftpt &&
   (if n.next == null then
      n.ftpt == {n}
    else
      n.next in n.ftpt && n.ftpt == {n} + n.next.ftpt && n !in n.next.ftpt &&
      n.next.ftpt <= n.ftpt && |n.next.ftpt| < |n.ftpt| &&
      List(n.next)))
}

ghost function {:opaque} Keys(n: Node?): set<int>
  reads if n == null then {} else {n} + n.ftpt
  decreases if n == null then 0 else |n.ftpt|
{
  if n == null then {}
  else if n.next == null then {n.data}
  else if n.next in n.ftpt && n.next.ftpt <= n.ftpt && |n.next.ftpt| < |n.ftpt| then
    {n.data} + Keys(n.next)
  else {n.data}
}

// ---------------------------------------------------------------------------
// The only facts about the definitions ever exported: one instantiation each.
// ---------------------------------------------------------------------------

lemma UnfoldList(n: Node?)
  ensures List(n) <==>
    (n == null ||
     (n in n.ftpt &&
      (if n.next == null then
         n.ftpt == {n}
       else
         n.next in n.ftpt && n.ftpt == {n} + n.next.ftpt && n !in n.next.ftpt &&
         n.next.ftpt <= n.ftpt && |n.next.ftpt| < |n.ftpt| &&
         List(n.next))))
{
  reveal List();
}

// The instantiation of both definitions at nil.
lemma NilList()
  ensures List(null) && Keys(null) == {}
{
  reveal List();
  reveal Keys();
}

lemma UnfoldKeys(n: Node?)
  requires List(n)
  ensures n == null ==> Keys(n) == {}
  ensures n != null && n.next == null ==> Keys(n) == {n.data}
  ensures n != null && n.next != null ==> Keys(n) == {n.data} + Keys(n.next)
{
  reveal List();
  reveal Keys();
}

// ---------------------------------------------------------------------------
// The set.
// ---------------------------------------------------------------------------

class LinkedSet {
  var head: Node?

  ghost function Repr(): set<Node>
    reads this, if head == null then {} else {head}
  {
    if head == null then {} else {head} + head.ftpt
  }

  ghost predicate Valid()
    reads this, Repr()
  {
    List(head)
  }

  ghost function Contents(): set<int>
    reads this, Repr()
  {
    Keys(head)
  }

  constructor ()
    ensures Valid() && Contents() == {} && Repr() == {}
  {
    head := null;
    new;
    NilList();
  }

  static method FindFrom(n: Node?, x: int) returns (found: bool)
    requires List(n)
    ensures found <==> x in Keys(n)
    decreases if n == null then 0 else |n.ftpt|
  {
    NilList();
    UnfoldList(n);
    UnfoldKeys(n);
    if n == null { return false; }
    if n.data == x { return true; }
    found := FindFrom(n.next, x);
  }

  method Find(x: int) returns (found: bool)
    requires Valid()
    ensures found <==> x in Contents()
  {
    found := FindFrom(head, x);
  }

  method Add(x: int)
    requires Valid()
    modifies this
    ensures Valid() && Contents() == old(Contents()) + {x}
    ensures fresh(Repr() - old(Repr()))
  {
    var present := FindFrom(head, x);
    if present { return; }

    NilList();
    UnfoldList(head);
    UnfoldKeys(head);
    var n := new Node(x, head, if head == null then {} else head.ftpt);
    UnfoldList(n);
    UnfoldKeys(n);
    head := n;
  }

  // Unlinks every node holding x and returns the new first node.
  static method DeleteFrom(n: Node?, x: int) returns (r: Node?)
    requires List(n)
    modifies if n == null then {} else n.ftpt
    ensures List(r)
    ensures Keys(r) == old(Keys(n)) - {x}
    ensures r != null ==> n != null && r.ftpt <= old(n.ftpt)
    decreases if n == null then 0 else |n.ftpt|
  {
    NilList();
    UnfoldList(n);
    UnfoldKeys(n);
    if n == null { return null; }

    if n.next == null {
      if n.data == x { return null; }
      return n;
    }

    var t := DeleteFrom(n.next, x);
    UnfoldList(t);                 // t's shape, before n is written

    n.next := t;
    n.ftpt := {n} + (if t == null then {} else t.ftpt);
    UnfoldList(n);
    UnfoldKeys(n);

    if n.data == x { return t; }
    return n;
  }

  method Delete(x: int)
    requires Valid()
    modifies this, Repr()
    ensures Valid() && Contents() == old(Contents()) - {x}
    ensures Repr() <= old(Repr())
  {
    var r := DeleteFrom(head, x);
    UnfoldList(r);              // gives r in r.ftpt, for the footprint bound
    head := r;
  }
}

method Main()
{
  var s := new LinkedSet();
  s.Add(3);
  s.Add(5);
  s.Add(3);
  var a := s.Find(3);
  var b := s.Find(4);
  assert a && !b;
  s.Delete(3);
  var c := s.Find(3);
  var d := s.Find(5);
  assert !c && d;
  print a, " ", b, " ", c, " ", d, "\n";
}
