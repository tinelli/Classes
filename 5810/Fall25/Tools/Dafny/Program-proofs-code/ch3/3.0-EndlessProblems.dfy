method BadDouble(x: int) returns (d: int)
  ensures d == 2 * x
{
  var y := BadDouble(x - 1); // error: failure to prove termination
  d := y + 2;
}

method PartialId(x: int) returns (y: int)
  ensures y == x
{
  if x % 2 == 0 {
    y := x;
  } else {
    y := PartialId(x); // error: failure to prove termination
  }
}

method Squarish(x: int, guess: int) returns (y: int)
  ensures x * x == y
{
  if
  case guess == x * x => // good guess!
    y := guess;
  case true =>
    y := Squarish(x, guess - 1); // error: failure to prove termination
  case true =>
    y := Squarish(x, guess + 1); // error: failure to prove termination
}

method Impossible(x: int) returns (y: int)
  ensures y % 2 == 0 && y == 10 * x - 3
{
  y := Impossible(x); // error: failure to prove termination
}

function Dubious(): int {
  1 + Dubious() // error: failure to prove termination
}
