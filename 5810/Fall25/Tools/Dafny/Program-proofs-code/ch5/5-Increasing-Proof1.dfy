function More(x: int): int {
  if x <= 0 then 1 else More(x - 2) + 3
}

lemma {:induction false} Increasing(x: int)
  ensures x < More(x)
{
  if x <= 0 {
    // easy
  } else {
    Increasing(x - 2); // this call gives us: x-2 < More(x-2)
  }
}
