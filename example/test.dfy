class Node {
  var key: int
  var next: Node?
}

predicate HasKey(n: Node, v: int)
  reads n
{
  n.key == v
}

predicate AllPos(n: Node?, visited: set<Node>)
  reads visited


  decreases visited
{
  n == null || (n in visited && n.key >= 0 && AllPos(n.next, visited - {n}))
}

method Test(n: Node?)
  requires n != null
  requires HasKey(n, 0)
  modifies n
  ensures HasKey(n, 1)
{
  n.key := 1;
}