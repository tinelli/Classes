function Ack(m: nat, n: nat): nat
  decreases m, n
{
  if m == 0 then
    n + 1
  else if n == 0 then
    Ack(m - 1, 1)
  else
    Ack(m - 1, Ack(m, n - 1))
}

lemma {:induction false} Ack1(n: nat)
  ensures Ack(1, n) == n + 2
{
  if n == 0 {
    // trivial
  } else {
    calc {
      Ack(1, n);
    ==  // def. Ack
      Ack(0, Ack(1, n - 1));
    ==  // def. Ack(0, _)
      Ack(1, n - 1) + 1;
    ==  { Ack1(n - 1); } // induction hypothesis
      (n - 1) + 2 + 1;
    ==  // arithmetic
      n + 2;
    }
  }
}
