method Swap(X: int, Y: int) {
  var x, y := X, Y;

  var tmp := x;
  x := y;
  y := tmp;

  assert x == Y && y == X;
}

method SwapArithetic(X: int, Y: int) {
  var x, y := X, Y;

  x := y - x;
  y := y - x;
  x := y + x;

  assert x == Y && y == X;
}

method SwapBitvectors(X: bv8, Y: bv8) {
  var x, y := X, Y;

  x := x ^ y;
  y := x ^ y;
  x := x ^ y;

  assert x == Y && y == X;
}

method SwapSimultaneous(X: int, Y: int) {
  var x, y := X, Y;

  x, y := y, x;

  assert x == Y && y == X;
}
