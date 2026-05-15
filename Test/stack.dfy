class Stack {
  var data: array?<int>
  var top: int

  predicate Valid()
    reads this, data
  {
    data != null &&
    0 <= top <= data.Length
  }

  constructor Init(capacity: int)
    requires capacity > 0
    ensures Valid()
    ensures top == 0
    ensures data.Length == capacity
  {
    data := new int[capacity];
    top := 0;
  }

  method Push(x: int)
    requires Valid()
    requires top < data.Length
    modifies this, data
    ensures Valid()
    ensures top == old(top) + 1
    ensures data[top - 1] == x
  {
    data[top] := x;
    top := top + 1;
  }

  method Pop() returns (x: int)
    requires Valid()
    requires top > 0
    modifies this
    ensures Valid()
    ensures top == old(top) - 1
    ensures x == old(data[top - 1])
  {
    top := top - 1;
    x := data[top];
  }

  method Size() returns (n: int)
    requires Valid()
    ensures n == top
  {
    n := top;
  }

  method IsEmpty() returns (b: bool)
    requires Valid()
    ensures b <==> top == 0
  {
    b := top == 0;
  }
}