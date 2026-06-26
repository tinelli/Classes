function More(x: int): int
//  ensures x < More(x)
// {
//   if x <= 0 then 1 else More(x - 2) + 3
// }
 
lemma {:induction true} Increasing(x: int)
  ensures x < More(x)
{
  // proof is automatic by Dafny's automatic induction
}
