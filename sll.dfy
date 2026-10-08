//include "prelude.dfy"

// ===========================================================================
// Natural-proofs prelude for singly-linked lists.
//
// Following Murali, Balakrishnan, Councilman and Madhusudan (OOPSLA 2025),
// recursive definitions are OPAQUE: the solver never receives their
// quantified defining axioms. The only facts about them ever exported are
// single instantiations, given by the Unfold lemmas below. Every proof is
// then a handful of such instantiations plus quantifier-free SMT reasoning.
//
// `ftpt` is the node's heaplet, playing the role of Sp(List(x)) in FL.
// Dafny's frame axiom for `reads` clauses plays the role of the frame rule,
// so no inductive framing lemma is ever needed.
// ===========================================================================

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

// Sp(List(x)), as a plain (non-recursive) accessor.
ghost function Fp(n: Node?): set<Node>
  reads if n == null then {} else {n}
{
  if n == null then {} else n.ftpt
}

// List(x): x points to a null-terminated list whose heaplet is x.ftpt.
ghost predicate {:opaque} List(n: Node?)
  reads if n == null then {} else {n} + n.ftpt
  decreases if n == null then {} else n.ftpt
{
  n == null ||
  (n in n.ftpt &&
   (if n.next == null then
      n.ftpt == {n}
    else
      n.next in n.ftpt && n.ftpt == {n} + n.next.ftpt && n !in n.next.ftpt &&
      n.next.ftpt < n.ftpt &&
      List(n.next)))
}

// Keys(x): the set of keys stored in the list at x.
ghost function {:opaque} Keys(n: Node?): set<int>
  reads if n == null then {} else {n} + n.ftpt
  decreases if n == null then {} else n.ftpt
{
  if n == null then {}
  else if n.next == null then {n.data}
  else if n.next in n.ftpt && n.next.ftpt < n.ftpt then
    {n.data} + Keys(n.next)
  else {n.data}
}

// ---------------------------------------------------------------------------
// Instantiations of the definitions: at nil, and at an arbitrary term n.
// ---------------------------------------------------------------------------

lemma NilList()
  ensures List(null) && Keys(null) == {}
{
  reveal List();
  reveal Keys();
}

lemma UnfoldList(n: Node?)
  ensures List(n) <==>
    (n == null ||
     (n in n.ftpt &&
      (if n.next == null then
         n.ftpt == {n}
       else
         n.next in n.ftpt && n.ftpt == {n} + n.next.ftpt && n !in n.next.ftpt &&
         n.next.ftpt < n.ftpt &&
         List(n.next))))
{
  reveal List();
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

// ===========================================================================
// benchmarksFL/sll: one method per .fsl file, with the benchmark's own
// program name, contract and control structure.
//
//   (RecDef (List x) (ite (= x nil) True
//                        (and (List (next x))
//                             (not (IsMember x (Sp (List (antiSp (next x)))))))))
//   (RecDef (Keys x) (ite (= x nil) EmptySetInt (SetAdd (Keys (next x)) (key x))))
//
// (EqSp (List (Keys))) is automatic here: List and Keys read the same ftpt.
// The footprint clauses (modifies / Fp bounds) are what Dafny needs in place
// of FL's implicit heaplets; the functional contracts are the benchmarks'.
// ===========================================================================

// --- sll_find.fsl ---------------------------------------------------------
method sll_find(x: Node?, k: int) returns (ret: bool)
  requires List(x)
  ensures List(x) && Keys(x) == old(Keys(x))
  ensures ret == (k in Keys(x))
  decreases |Fp(x)|
{
  NilList();
  UnfoldList(x);
  UnfoldKeys(x);
  if x == null { return false; }
  if x.data == k { return true; }
  var aux := x.next;
  ret := sll_find(aux, k);
}

// --- sll_insert_front.fsl -------------------------------------------------
method sll_insert_front(x: Node?, k: int) returns (ret: Node)
  requires List(x)
  ensures List(ret) && Keys(ret) == old(Keys(x)) + {k}
  ensures Fp(ret) == {ret} + old(Fp(x)) && fresh(ret)
{
  NilList();
  UnfoldList(x);
  ret := new Node(k, x, Fp(x));
  UnfoldList(ret);
  UnfoldKeys(ret);
}

// --- sll_insert_back.fsl --------------------------------------------------
method sll_insert_back(x: Node?, k: int) returns (ret: Node)
  requires List(x)
  modifies Fp(x)
  ensures List(ret) && Keys(ret) == old(Keys(x)) + {k}
  ensures old(Fp(x)) <= Fp(ret) && fresh(Fp(ret) - old(Fp(x)))
  decreases |Fp(x)|
{
  NilList();
  UnfoldList(x);
  UnfoldKeys(x);
  if x == null {
    ret := new Node(k, null, {});
    UnfoldList(ret);
    UnfoldKeys(ret);
    return;
  }
  var aux := x.next;
  var tmp := sll_insert_back(aux, k);
  UnfoldList(tmp);
  x.next := tmp;
  x.ftpt := {x} + Fp(tmp);
  UnfoldList(x);
  UnfoldKeys(x);
  return x;
}

// --- sll_append.fsl -------------------------------------------------------
method sll_append(x: Node?, y: Node?) returns (ret: Node?)
  requires List(x) && List(y) && Fp(x) !! Fp(y)
  modifies Fp(x)
  ensures List(ret) && Keys(ret) == old(Keys(x)) + old(Keys(y))
  ensures Fp(ret) <= old(Fp(x)) + old(Fp(y))
  decreases |Fp(x)|
{
  NilList();
  UnfoldList(x);
  UnfoldKeys(x);
  if x == null { return y; }

  var aux := x.next;
  var tmp := sll_append(aux, y);
  UnfoldList(tmp);
  x.next := tmp;
  x.ftpt := {x} + Fp(tmp);
  UnfoldList(x);
  UnfoldKeys(x);
  return x;
}

// --- sll_copy_all.fsl -----------------------------------------------------
method sll_copy_all(x: Node?) returns (ret: Node?)
  requires List(x)
  ensures List(x) && Keys(x) == old(Keys(x))
  ensures List(ret) && Keys(ret) == old(Keys(x))
  ensures Fp(x) !! Fp(ret)
  ensures Fp(x) == old(Fp(x)) && fresh(Fp(ret))
  decreases |Fp(x)|
{
  NilList();
  UnfoldList(x);
  UnfoldKeys(x);
  if x == null { return null; }

  var nxt := x.next;
  var tmp := sll_copy_all(nxt);
  UnfoldList(tmp);
  ret := new Node(x.data, tmp, Fp(tmp));
  UnfoldList(ret);
  UnfoldKeys(ret);
}

// --- sll_delete.fsl -------------------------------------------------------
// (The benchmark frees the deleted node; Dafny has no free.)
method sll_delete(x: Node?, k: int) returns (ret: Node?)
  requires List(x)
  modifies Fp(x)
  ensures List(ret) && Keys(ret) == old(Keys(x)) - {k}
  ensures Fp(ret) <= old(Fp(x))
  decreases |Fp(x)|
{
  NilList();
  UnfoldList(x);
  UnfoldKeys(x);
  if x == null { return x; }

  if x.data == k {
    var tmp := x.next;
    ret := sll_delete(tmp, k);
    return;
  }

  var aux := x.next;
  var tmp := sll_delete(aux, k);
  UnfoldList(tmp);
  x.next := tmp;
  x.ftpt := {x} + Fp(tmp);
  UnfoldList(x);
  UnfoldKeys(x);
  return x;
}

// --- sll_reverse.fsl ------------------------------------------------------
method sll_reverse_helper(x: Node?, y: Node?) returns (ret: Node?)
  requires List(x) && List(y) && Fp(x) !! Fp(y)
  modifies Fp(x)
  ensures List(ret) && Keys(ret) == old(Keys(x)) + old(Keys(y))
  ensures Fp(ret) <= old(Fp(x)) + old(Fp(y))
  decreases |Fp(x)|
{
  NilList();
  UnfoldList(x);
  UnfoldKeys(x);
  UnfoldList(y);
  if x == null { return y; }

  var tmp := x.next;
  UnfoldList(tmp);
  x.next := y;
  x.ftpt := {x} + Fp(y);
  UnfoldList(x);
  UnfoldKeys(x);

  ret := sll_reverse_helper(tmp, x);
}

method sll_reverse(x: Node?) returns (ret: Node?)
  requires List(x)
  modifies Fp(x)
  ensures List(ret) && Keys(ret) == old(Keys(x))
  ensures Fp(ret) <= old(Fp(x))
{
  NilList();
  ret := sll_reverse_helper(x, null);
}
