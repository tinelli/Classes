function Fib(n: nat): nat
  decreases n
{
  if n < 2 then n else Fib(n - 2) + Fib(n - 1)
}

function SeqSum(s: seq<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= |s|
  decreases hi - lo
{
  if lo == hi then 0 else s[lo] + SeqSum(s, lo + 1, hi)
}

function Ack(m: nat, n: nat): nat
  // decreases ...?
{
  if m == 0 then
    n + 1
  else if n == 0 then
    Ack(m - 1, 1)
  else
    Ack(m - 1, Ack(m, n - 1))
}

// Exercises:

function F(x: int): int
  // decreases ...?
{
  if x < 10 then x else F(x - 1)
}

function G(x: int): int
  // decreases ...?
{
  if 0 <= x then G(x - 2) else x
}

function H(x: int): int
  // decreases ...?
{
  if x < -60 then x else H(x - 1)
}

function I(x: nat, y: nat): int
  // decreases ...?
{
  if x == 0 || y == 0 then
    12
  else if x % 2 == y % 2 then
    I(x - 1, y)
  else
    I(x, y - 1)
}

function J(x: nat, y: nat): int
  // decreases ...?
{
  if x == 0 then
    y
  else if y == 0 then
    J(x - 1, 3)
  else
    J(x, y - 1)
}

function K(x: nat, y: nat, z: nat): int
  // decreases ...?
{
  if x < 10 || y < 5 then
    x + y
  else if z == 0 then
    K(x - 1, y, 5)
  else
    K(x, y - 1, z - 1)
}

function L(x: int): int
  // decreases ...?
{
  if x < 100 then L(x + 1) + 10 else x
}

function M(x: int, b: bool): int
  // decreases ...?
{
  if b then x else M(x + 25, true)
}

function N(x: int, y: int, b: bool): int
  // decreases ...?
{
  if x <= 0 || y <= 0 then
    x + y
  else if b then
    N(x, y + 3, !b)
  else
    N(x - 1, y, true)
}
