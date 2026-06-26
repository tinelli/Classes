method Index(n: int) returns (i: int)
  requires 1 <= n
  ensures 0 <= i < n
{
  i := n / 2;

  // Or, the following statement also satisfies the specification:
  // i := 0;
}

method Caller1() {
  var x := Index(50);
  var y := Index(50);
  assert x == y; // error: the specification of Index does not allow you to prove this condition
}

function funIndex(n: int) : int
  ensures 0 <= funIndex(n) < n


method Caller2() {
  var x := funIndex(50);
  var y := funIndex(50);
  assert x == y; // no error: the specification of funIndex does allow you 
                 // to prove this condition because funIndex is a function
}
