function More(x: int): int {
  if x <= 0 then 1 else More(x - 2) + 3
}

lemma {:induction false} Increasing(x: int)
  ensures x < More(x)
{
  if x <= 0 {

  } else {
    Increasing(x - 2); // induction hypothesis
  }
}

lemma {:induction false} Increasing2(x: int)
  ensures x < More(x)
{
  if x <= 0 {
    // deduction style
    assert x <= 0;
    assert More(x) == 1;
    assert x < More(x);
  } else {
    assert 0 < x;
    assert More(x) == More(x - 2) + 3;
    Increasing(x - 2); // induction hypothesis
    assert x - 2 < More(x - 2);
    assert x < More(x - 2) + 2 < More(x - 2) + 3 == More(x);
    assert x < More(x);
  }
  assert x < More(x);
}
