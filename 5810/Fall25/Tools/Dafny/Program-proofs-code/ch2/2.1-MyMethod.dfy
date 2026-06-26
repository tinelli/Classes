method MyMethod(x: int) returns (y: int)
  requires 10 <= x
  ensures 25 <= y
{
  var a := x + 3;
  var b := 12;
  y := a + b;
}
