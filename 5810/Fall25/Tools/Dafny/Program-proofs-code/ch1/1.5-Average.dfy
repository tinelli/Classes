function Average(a: int, b: int): int
  requires 0 <= a && 0 <= b
{
  (a + b) / 2
}

method Triple(x: int) returns (r: int)
  ensures r == 3 * x
{
  if 0 <= x {
    r := Average(2 * x, 4 * x);
  } else {
    r := -Average(-2 * x, -4 * x);
  }
}
