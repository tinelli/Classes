method Min'(a: array<int>) returns (m: int)
  ensures forall i :: 0 <= i < a.Length ==> m <= a[i]
{
  m := *; // see https://program-proofs.com/errata.html about this line
  var n := 0;
  while n != a.Length
    invariant 0 <= n <= a.Length
    invariant forall i :: 0 <= i < n ==> m <= a[i]
  {
    if a[n] < m {
      m := a[n];
    }
    n := n + 1;
  }
}

method Min(a: array<int>) returns (m: int)
  requires a.Length != 0
  ensures forall i :: 0 <= i < a.Length ==> m <= a[i]
  ensures exists i :: 0 <= i < a.Length && m == a[i]
{
  m := a[0];
  var n := 0;
  while n != a.Length
    invariant 0 <= n <= a.Length
    invariant forall i :: 0 <= i < n ==> m <= a[i]
    invariant exists i :: 0 <= i < a.Length && m == a[i]
  {
    if a[n] < m {
      m := a[n];
    }
    n := n + 1;
  }
}
