method DivMod7() {
  var x, y;

  x, y := 0, 191;
  while 7 <= y
    invariant 0 <= y && 7 * x + y == 191
    decreases y
  {
    y := y - 7;
    x := x + 1;
  }
}

method LeapToTheAnswer() {
  var x, y;

  x, y := 0, 191;
  while 7 <= y
    invariant 0 <= y && 7 * x + y == 191
    decreases y
  {
    x, y := 27, 2;
  }
}

method SwitchingDirections() {
  var x, y;

  x, y := 0, 191;
  while 7 <= y // cannot prove termination
    invariant 0 <= y && 7 * x + y == 191
  {
    x, y := x - 1, y + 7;
  }
}

method UpDoesNotTerminate() {
  var x, y;

  x, y := 0, 191;
  while 7 <= y // cannot prove termination
    invariant 0 <= y && 7 * x + y == 191
    invariant 7 <= y
  {
    x, y := x - 1, y + 7;
  }
}
