function Fib(n: nat): nat {
  if n < 2 then n else Fib(n - 2) + Fib(n - 1)
}

method ComputeFib(n: nat) returns (x: nat)
  ensures x == Fib(n)
{
  x := 0;
  var y := 1;
  var i := 0;
  while i != n
    invariant 0 <= i <= n
    invariant x == Fib(i) && y == Fib(i + 1)
  {
    x, y := y, x + y;
    i := i + 1;
  }
}

method SquareFib(N: nat) returns (x: nat)
  ensures x == Fib(N) * Fib(N)
{
  x := 0;
  var n := 0;
  while n != N
    invariant 0 <= n <= N
    invariant x == Fib(n) * Fib(n)
}

method SquareFib'y(N: nat) returns (x: nat)
  ensures x == Fib(N) * Fib(N)
{
  x := 0;
  var n, y := 0, 1;
  while n != N
    invariant 0 <= n <= N
    invariant x == Fib(n) * Fib(n)
    invariant y == Fib(n + 1) * Fib(n + 1)
  {
    calc {
      Fib(n + 2) * Fib(n + 2);
    ==  // def. Fib
      (Fib(n) + Fib(n + 1)) * (Fib(n) + Fib(n + 1));
    ==  // cross multiply
      Fib(n) * Fib(n) + 2 * Fib(n) * Fib(n + 1) + Fib(n + 1) * Fib(n + 1);
    ==  // invariant
      x + 2 * Fib(n) * Fib(n + 1) + y;
    }
    x, y := y, Fib(n + 2) * Fib(n + 2);
    n := n + 1;
  }
}

method SquareFib'k(N: nat) returns (x: nat)
  ensures x == Fib(N) * Fib(N)
{
  x := 0;
  var n, y, k := 0, 1, 0;
  while n != N
    invariant 0 <= n <= N
    invariant x == Fib(n) * Fib(n)
    invariant y == Fib(n + 1) * Fib(n + 1)
    invariant k == 2 * Fib(n) * Fib(n + 1)
  {
    calc {
      2 * Fib(n + 1) * Fib(n + 2);
    ==  // def. Fib
      2 * Fib(n + 1) * (Fib(n) + Fib(n + 1));
    ==  // distribute arithmetic
      2 * Fib(n + 1) * Fib(n) + 2 * Fib(n + 1) * Fib(n + 1);
    }
    x, y, k := y, x + k + y, k + y + y;
    n := n + 1;
  }
}

method SquareFib'final(N: nat) returns (x: nat)
  ensures x == Fib(N) * Fib(N)
{
  x := 0;
  var n, y, k := 0, 1, 0;
  while n != N
    invariant 0 <= n <= N
    invariant x == Fib(n) * Fib(n)
    invariant y == Fib(n + 1) * Fib(n + 1)
    invariant k == 2 * Fib(n) * Fib(n + 1)
  {
    x, y, k := y, x + k + y, k + y + y;
    n := n + 1;
  }
}
