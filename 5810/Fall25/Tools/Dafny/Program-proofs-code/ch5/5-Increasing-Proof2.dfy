function More(x: int): int {
  if x <= 0 then 1 else More(x - 2) + 3
}

lemma {:induction false} Increasing(x: int)
  ensures x < More(x)
{
  // let's consider only the interesting case
  if 0 < x {
    var y := x - 2;
    Increasing(y);
  }
}
