class Cell {
  var value: int

  constructor(v: int)
    ensures value == v
  {
    value := v;
  }

  method SetValue(v: int)
    modifies this
    ensures value == v
  {
    value := v;
  }

  method Increment()
    modifies this
    ensures value == old(value) + 1
  {
    value := value + 1;
  }
}

method UpdateCells(a: Cell, b: Cell) returns (sum: int)
  requires a != b
  requires a.value >= 0
  requires b.value >= 0
  modifies a, b
  ensures a.value == old(a.value) + 1
  ensures b.value == old(b.value) + 2
  ensures sum == a.value + b.value
{
  a.Increment();

  b.value := b.value + 2;

  sum := a.value + b.value;
}

method Main()
{
  var x := new Cell(3);
  var y := new Cell(5);

  var total := UpdateCells(x, y);

  assert x.value == 4;
  assert y.value == 7;
  assert total == 11;
}