class Counter {
  var value: int

  constructor()
    ensures value == 0
  {
    value := 0;
  }

  twostate function Increased(): bool
    reads this
  {
    old(value) <= value
  }

  twostate function IncreasedByOne(): bool
    reads this
  {
    value == old(value) + 1
  }

  method Increment()
    modifies this
    ensures Increased()
    ensures IncreasedByOne()
  {
    value := value + 1;
  }
}