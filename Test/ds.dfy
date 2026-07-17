method Add(x: int, s: set<int>) returns (r: set<int>)
  ensures r == s + {x}
  ensures x in r
{
  r := s + {x};
}

class Bag {
  ghost var contents: set<int>

  constructor()
    ensures contents == {}
  {
    contents := {};
  }

  method Add(x: int)
    modifies this
    ensures contents == old(contents) + {x}
  {
    contents := contents + {x};
  }
}

method Count(s: set<int>) returns (n: nat)
  ensures n == |s|
{
  if s == {} {
    return 0;
  }

  var x :| x in s;
  var subCount := Count(s - {x});

  n := 1 + subCount;
}