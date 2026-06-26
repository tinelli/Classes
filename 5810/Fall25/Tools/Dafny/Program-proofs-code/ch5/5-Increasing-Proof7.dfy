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
      true;
    ==>  { Increasing(x - 2); }
      x - 2 < More(x - 2);
    <==>  // add 3 to each side
      x + 1 < More(x - 2) + 3;
    <==>  // def. More, since 0 < x
      x + 1 < More(x);
    ==>  // arithmetic
      x < More(x);
    }
  }
}
