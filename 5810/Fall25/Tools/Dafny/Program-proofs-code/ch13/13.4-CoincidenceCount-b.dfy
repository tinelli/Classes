method CoincidenceCount(a: array<int>, b: array<int>) returns (c: nat)
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  requires forall i, j :: 0 <= i < j < b.Length ==> b[i] <= b[j]
  ensures c == |multiset(a[..]) * multiset(b[..])|
{
  c := 0;
  var m, n := 0, 0;
  while m < a.Length && n < b.Length
    invariant 0 <= m <= a.Length && 0 <= n <= b.Length
    invariant c + |multiset(a[m..]) * multiset(b[n..])|
           == |multiset(a[..]) * multiset(b[..])|
    decreases a.Length - m + b.Length - n
  {
    if
    case a[m] == b[n] =>
      c, m, n := c + 1, m + 1, n + 1;
      assert c + |multiset(a[m..]) * multiset(b[n..])| // unable to prove this assertion
          == |multiset(a[..]) * multiset(b[..])|;
    case a[m] < b[n] =>
      m := m + 1;
      assert c + |multiset(a[m..]) * multiset(b[n..])| // unable to prove this assertion
          == |multiset(a[..]) * multiset(b[..])|;
    case b[n] < a[m] =>
      n := n + 1;
      assert c + |multiset(a[m..]) * multiset(b[n..])| // unable to prove this assertion
          == |multiset(a[..]) * multiset(b[..])|;
  }
}
