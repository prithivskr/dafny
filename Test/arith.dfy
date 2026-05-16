class Node {
  var val:   int
  var tag:   int
  var score: int

  constructor(v: int, t: int, s: int)
    ensures val == v && tag == t && score == s
  { val := v; tag := t; score := s; }
}

method Bump(a: Node, b: Node, c: Node, d: Node, e: Node, f: Node)
  requires a != b && a != c && a != d && a != e && a != f
  requires b != c && b != d && b != e && b != f
  requires c != d && c != e && c != f
  requires d != e && d != f && e != f
  modifies a, b, c, d, e, f
  ensures a.val == old(a.val) + 1 && a.tag == old(a.tag) && a.score == old(a.score)
  ensures b.val == old(b.val) + 1 && b.tag == old(b.tag) && b.score == old(b.score)
  ensures c.val == old(c.val) + 1 && c.tag == old(c.tag) && c.score == old(c.score)
  ensures d.val == old(d.val) + 1 && d.tag == old(d.tag) && d.score == old(d.score)
  ensures e.val == old(e.val) + 1 && e.tag == old(e.tag) && e.score == old(e.score)
  ensures f.val == old(f.val) + 1 && f.tag == old(f.tag) && f.score == old(f.score)
{
  a.val := a.val + 1;
  b.val := b.val + 1;
  c.val := c.val + 1;
  d.val := d.val + 1;
  e.val := e.val + 1;
  f.val := f.val + 1;
}

method DoubleBump(a: Node, b: Node, c: Node, d: Node, e: Node, f: Node)
  requires a != b && a != c && a != d && a != e && a != f
  requires b != c && b != d && b != e && b != f
  requires c != d && c != e && c != f
  requires d != e && d != f && e != f
  modifies a, b, c, d, e, f
  ensures a.val == old(a.val) + 2 && a.tag == old(a.tag) && a.score == old(a.score)
  ensures b.val == old(b.val) + 2 && b.tag == old(b.tag) && b.score == old(b.score)
  ensures c.val == old(c.val) + 2 && c.tag == old(c.tag) && c.score == old(c.score)
  ensures d.val == old(d.val) + 2 && d.tag == old(d.tag) && d.score == old(d.score)
  ensures e.val == old(e.val) + 2 && e.tag == old(e.tag) && e.score == old(e.score)
  ensures f.val == old(f.val) + 2 && f.tag == old(f.tag) && f.score == old(f.score)
{
  Bump(a, b, c, d, e, f);
  Bump(a, b, c, d, e, f);
}

method QuadBump(a: Node, b: Node, c: Node, d: Node, e: Node, f: Node)
  requires a != b && a != c && a != d && a != e && a != f
  requires b != c && b != d && b != e && b != f
  requires c != d && c != e && c != f
  requires d != e && d != f && e != f
  modifies a, b, c, d, e, f
  ensures a.val == old(a.val) + 4 && a.tag == old(a.tag) && a.score == old(a.score)
  ensures b.val == old(b.val) + 4 && b.tag == old(b.tag) && b.score == old(b.score)
  ensures c.val == old(c.val) + 4 && c.tag == old(c.tag) && c.score == old(c.score)
  ensures d.val == old(d.val) + 4 && d.tag == old(d.tag) && d.score == old(d.score)
  ensures e.val == old(e.val) + 4 && e.tag == old(e.tag) && e.score == old(e.score)
  ensures f.val == old(f.val) + 4 && f.tag == old(f.tag) && f.score == old(f.score)
{
  DoubleBump(a, b, c, d, e, f);
  DoubleBump(a, b, c, d, e, f);
}

method BumpN(a: Node, b: Node, c: Node, d: Node, e: Node, f: Node, n: int)
  requires n >= 0
  requires a != b && a != c && a != d && a != e && a != f
  requires b != c && b != d && b != e && b != f
  requires c != d && c != e && c != f
  requires d != e && d != f && e != f
  modifies a, b, c, d, e, f
  ensures a.val == old(a.val) + n && a.tag == old(a.tag) && a.score == old(a.score)
  ensures b.val == old(b.val) + n && b.tag == old(b.tag) && b.score == old(b.score)
  ensures c.val == old(c.val) + n && c.tag == old(c.tag) && c.score == old(c.score)
  ensures d.val == old(d.val) + n && d.tag == old(d.tag) && d.score == old(d.score)
  ensures e.val == old(e.val) + n && e.tag == old(e.tag) && e.score == old(e.score)
  ensures f.val == old(f.val) + n && f.tag == old(f.tag) && f.score == old(f.score)
{
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant a.val == old(a.val) + i && a.tag == old(a.tag) && a.score == old(a.score)
    invariant b.val == old(b.val) + i && b.tag == old(b.tag) && b.score == old(b.score)
    invariant c.val == old(c.val) + i && c.tag == old(c.tag) && c.score == old(c.score)
    invariant d.val == old(d.val) + i && d.tag == old(d.tag) && d.score == old(d.score)
    invariant e.val == old(e.val) + i && e.tag == old(e.tag) && e.score == old(e.score)
    invariant f.val == old(f.val) + i && f.tag == old(f.tag) && f.score == old(f.score)
  {
    Bump(a, b, c, d, e, f);
    i := i + 1;
  }
}

method StressTest(
    a: Node, b: Node, c: Node, d: Node, e: Node, f: Node,
    p: Node, q: Node, r: Node, s: Node, t: Node, u: Node,
    n: int)
  requires n >= 0
  // group 1 internal distinctness
  requires a != b && a != c && a != d && a != e && a != f
  requires b != c && b != d && b != e && b != f
  requires c != d && c != e && c != f
  requires d != e && d != f && e != f
  // group 2 internal distinctness
  requires p != q && p != r && p != s && p != t && p != u
  requires q != r && q != s && q != t && q != u
  requires r != s && r != t && r != u
  requires s != t && s != u && t != u
  // cross-group distinctness
  requires a != p && a != q && a != r && a != s && a != t && a != u
  requires b != p && b != q && b != r && b != s && b != t && b != u
  requires c != p && c != q && c != r && c != s && c != t && c != u
  requires d != p && d != q && d != r && d != s && d != t && d != u
  requires e != p && e != q && e != r && e != s && e != t && e != u
  requires f != p && f != q && f != r && f != s && f != t && f != u
  modifies a, b, c, d, e, f, p, q, r, s, t, u
  ensures a.val == old(a.val) + n + 4 && a.tag == old(a.tag) && a.score == old(a.score)
  ensures b.val == old(b.val) + n + 4 && b.tag == old(b.tag) && b.score == old(b.score)
  ensures c.val == old(c.val) + n + 4 && c.tag == old(c.tag) && c.score == old(c.score)
  ensures d.val == old(d.val) + n + 4 && d.tag == old(d.tag) && d.score == old(d.score)
  ensures e.val == old(e.val) + n + 4 && e.tag == old(e.tag) && e.score == old(e.score)
  ensures f.val == old(f.val) + n + 4 && f.tag == old(f.tag) && f.score == old(f.score)
  ensures p.val == old(p.val) + 2 && p.tag == old(p.tag) && p.score == old(p.score)
  ensures q.val == old(q.val) + 2 && q.tag == old(q.tag) && q.score == old(q.score)
  ensures r.val == old(r.val) + 2 && r.tag == old(r.tag) && r.score == old(r.score)
  ensures s.val == old(s.val) + 2 && s.tag == old(s.tag) && s.score == old(s.score)
  ensures t.val == old(t.val) + 2 && t.tag == old(t.tag) && t.score == old(t.score)
  ensures u.val == old(u.val) + 2 && u.tag == old(u.tag) && u.score == old(u.score)
{
  BumpN(a, b, c, d, e, f, n);
  QuadBump(a, b, c, d, e, f);
  DoubleBump(p, q, r, s, t, u);
}