function More(x: int): int {
  if x <= 0 then 1 else More(x - 2) + 3
}

lemma Increasing(x: int)
  ensures x < More(x)
// proof omitted here, but see separate files

method ExampleLemmaUse(a: int)
{
  var b := More(a);
  var c := More(b);
//  assert 2 <= c - a;
}




method ExampleLemmaUse2(a: int)
{
  var b := More(a);
  Increasing(a);
  Increasing(b);
  var c := More(b);
  assert 2 <= c - a;
}
