

method Min(x: int, y: int) returns (m: int)
  ensures m <= x && m <= y


method Test()
{
  var a := 10;
  var b := 4;

  var m := Min(a,b);

  assert m == 4;
}