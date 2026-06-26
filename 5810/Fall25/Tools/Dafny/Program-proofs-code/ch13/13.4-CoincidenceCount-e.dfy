method CoincidenceCount_Debug4(a: array<int>, b: array<int>) returns (c: nat)
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
      MultisetIntersectionPrefix(a, b, m, n);
      c, m, n := c + 1, m + 1, n + 1;
    case a[m] < b[n] =>
      MultisetIntersectionAdvance(a, m, multiset(b[n..]));
      m := m + 1;
    case b[n] < a[m] =>
      n := n + 1;
      assert c + |multiset(a[m..]) * multiset(b[n..])| // unable to prove this assertion
          == |multiset(a[..]) * multiset(b[..])|;
  }
}

lemma MultisetIntersectionPrefix(a: array<int>, b: array<int>,
                                 m: nat, n: nat)
  requires m < a.Length && n < b.Length
  requires a[m] == b[n]
  ensures multiset(a[m..]) * multiset(b[n..])
       == multiset{a[m]} + (multiset(a[m+1..]) * multiset(b[n+1..]))
{
  var E := multiset{a[m]};
  calc {
    multiset(a[m..]) * multiset(b[n..]);
    multiset(a[m..]) * multiset(b[n..]);
  ==  { assert a[m..] == [a[m]] + a[m+1..]
            && b[n..] == [b[n]] + b[n+1..]; }
    (E + multiset(a[m+1..])) * (E + multiset(b[n+1..]));
  ==  // distribute * over +
    E + (multiset(a[m+1..]) * multiset(b[n+1..]));
  }
}

lemma MultisetIntersectionAdvance(a: array<int>, m: nat,
                                  B: multiset<int>)
  requires m < a.Length && a[m] !in B
  ensures multiset(a[m..]) * B == multiset(a[m+1..]) * B
{
  var E := multiset{a[m]};
  calc {
    multiset(a[m..]) * B;
  ==  { assert a[m..] == [a[m]] + a[m+1..]; }
    (E + multiset(a[m+1..])) * B;
  ==  // distribute * over +
    (E * B) + (multiset(a[m+1..]) * B);
  ==  { assert E * B == multiset{}; }
    multiset(a[m+1..]) * B;
  }
}
