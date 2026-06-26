// Section 11.0.2

method Example0() {
  var x := 0;

  while x < 300
    invariant x % 2 == 0
}

method Example1() {
  var x := 1;

  while x % 2 == 1
    invariant 0 <= x <= 100
}

method Example2() {
  var x;

  x := 2;
  while x < 50
    invariant x % 2 == 0
  assert 50 <= x && x % 2 == 0;
}

method Example3() {
  var x;

  x := 0;
  while x % 2 == 0
    invariant 0 <= x <= 20
  assert x == 19; // not provable
}

// Section 11.0.3

method Example4() {
  var i;

  i := 0;
  while i != 100
    invariant 0 <= i <= 100
  assert i == 100;
}

method Example5() {
  var i;

  i := 0;
  while i != 100
    invariant true
  assert i == 100;
}

method Example6() {
  var i;

  i := 0;
  while i < 100
    invariant 0 <= i <= 100
  assert i == 100;
}

method Example7() {
  var i;

  i := 0;
  while i < 100
    invariant true
  assert i == 100; // not provable
}

// Section 11.0.4

method Example8() {
  var x, y;
  x, y := 0, 0;
  while x < 300
    invariant 2 * x == 3 * y
  assert 200 <= y;
}

method Example9() {
  var x, y;

  x, y := 0, 191;
  while !(0 <= y < 7)
    invariant 7 * x + y == 191
  assert x == 191 / 7 && y == 191 % 7;
}

method Example10() {
  var x, y;

  x, y := 0, 191;
  while 7 <= y
    invariant 0 <= y && 7 * x + y == 191
  assert x == 191 / 7 && y == 191 % 7;
}

method Example11() {
  var n, s;

  n, s := 0, 0;
  while n != 33
    invariant s == n * (n - 1) / 2
}

// Section 11.0.5

method Example12() {
  var r, N;

  r, N := 0, 104;
  while (r+1)*(r+1) <= N
    invariant 0 <= r && r*r <= N
  assert 0 <= r && r*r <= N < (r+1)*(r+1);
}
