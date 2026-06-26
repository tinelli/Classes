function Abs(x: int): int {
  if x < 0 then -x else x
}

method AbsMethod(x: int) returns (y: int)
  ensures 0 <= y && (x == y || x == -y)
{
  y := Abs(x);
}
