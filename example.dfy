class Cell {
  var value: int ghost var fp: set<Cell>
}

ghost function {:opaque} Observe(x: Cell): int reads {x} + x.fp { x.value }

method Change(y: Cell) modifies y { y.value := y.value + 1; }

method Test(x: Cell, y: Cell) requires x != y && y !in x.fp modifies y {
  ghost var before := Observe(x);
  Change(y);
  assert Observe(x) == before;
}