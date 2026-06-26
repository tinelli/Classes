function More(x: int): int {
  if x <= 0 then 1 else More(x - 2) + 3
}

lemma {:induction false} Increasing(x: int)
  ensures x < More(x)
{
  if x <= 0 {
    // let's get ridiculously detailed, to illustrate what you can do
    calc {
      x;
    <=  { assert x <= 0; }
      0;
    <  // arithmetic
      1;
    ==  // def. More
      More(x);
    }
  } else {
    calc {
      x < More(x);
    <==  // arithmetic
      x + 1 < More(x);
    ==  // def. More, since 0 < x
      x + 1 < More(x - 2) + 3;
    ==  // subtract 3 from each side
      x - 2 < More(x - 2);
    <==  { Increasing(x - 2); }
      true;
    }
  }
}
