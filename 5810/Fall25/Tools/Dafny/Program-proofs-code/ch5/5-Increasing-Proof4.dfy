function More(x: int): int {
  if x <= 0 then 1 else More(x - 2) + 3
}

lemma {:induction false} Increasing(x: int)
  ensures x < More(x)
{
  if x <= 0 {
    assert More(x) == 1; // def. More for x <= 0
  } else {
    assert More(x) == More(x - 2) + 3; // def. More for 0 < x
    Increasing(x - 2); // induction hypothesis
    assert More(x) == More(x - 2) + 3 &&
           x - 2 < More(x - 2);
    assert More(x) == More(x - 2) + 3 &&
           x + 1 < More(x - 2) + 3;
    assert x + 1 < More(x);
  }
}
