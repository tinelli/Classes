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
    // here's a nice calculation
    calc {
      More(x);
    ==  // def. More, since 0 < x
      More(x - 2) + 3;
    >  { Increasing(x - 2); }
      x - 2 + 3;
    ==  // arithmetic
      x + 1;
    >  // arithmetic
      x;
    }
  }
}
