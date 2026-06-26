method DivMod7() {
  var x, y;

  x, y := 0, 191;
  while 7 <= y
    invariant 0 <= y && 7 * x + y == 191
  {
    y := y - 7;
    x := x + 1;
  }
  assert x == 191 / 7 && y == 191 % 7;
}

method LeapToTheAnswer() {
  var x, y;

  x, y := 0, 191;
  while 7 <= y
    invariant 0 <= y && 7 * x + y == 191
  {
    x, y := 27, 2;
  }
  assert x == 191 / 7 && y == 191 % 7;
}

method GoingTwiceAsFast() {
  var x, y;

  x, y := 0, 191;
  while 7 <= y
    invariant 0 <= y && 7 * x + y == 191 // error: loop invariant not maintained
  {
    x, y := x + 2, y - 14;
  }
  assert x == 191 / 7 && y == 191 % 7;
}

method Sum() {
  var n, s;

  n, s := 0, 0;
  while n != 33
    invariant s == n * (n - 1) / 2
  {
    s := s + n;
    n := n + 1;
  }
}

method LoopFrameExample(X: int, Y: int)
  requires 0 <= X <= Y
{
  var i, a, b := 0, X, Y;
  while i < 100 {
    i, b := i + 1, b + X;
  }
  assert a == X;
  assert Y <= b; // not provable without an invariant for the loop
}
