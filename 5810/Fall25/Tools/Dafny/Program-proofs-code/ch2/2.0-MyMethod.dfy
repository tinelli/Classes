method MyMethod(x: int) returns (y: int)
  requires 10 <= x
  ensures 25 <= y
{
  var a, b;
  a := x + 3;
  if x < 20 {
    b := 32 - x;
  } else {
    b := 16;
  }
  y := a + b;
}
