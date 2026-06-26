function Dist(x: int, y: int): nat {
  if x < y then y - x else x - y
}

method CanyonSearch(a: array<int>, b: array<int>) returns (d: nat)
  requires a.Length != 0 && b.Length != 0
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  requires forall i, j :: 0 <= i < j < b.Length ==> b[i] <= b[j]
  ensures exists i, j ::
    0 <= i < a.Length && 0 <= j < b.Length && d == Dist(a[i], b[j])
  ensures
    forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length ==>
      d <= Dist(a[i], b[j])
{
  d := Dist(a[0], b[0]);
  var m, n := 0, 0;
  while m < a.Length && n < b.Length
    invariant 0 <= m <= a.Length && 0 <= n <= b.Length
    invariant exists i, j ::
      0 <= i < a.Length && 0 <= j < b.Length &&
        d == Dist(a[i], b[j])
    invariant forall i, j ::
      0 <= i < a.Length && 0 <= j < b.Length ==>
        d <= Dist(a[i], b[j]) || (m <= i && n <= j)
    decreases a.Length - m + b.Length - n
  {
    d := if Dist(b[n], a[m]) < d then Dist(b[n], a[m]) else d;
    if
    case a[m] <= b[n] =>
      m := m + 1;
    case b[n] <= a[m] =>
      n := n + 1;
  }
}

method CanyonSearch_Optimized(a: array<int>, b: array<int>) returns (d: nat)
  requires a.Length != 0 && b.Length != 0
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  requires forall i, j :: 0 <= i < j < b.Length ==> b[i] <= b[j]
  ensures exists i, j ::
    0 <= i < a.Length && 0 <= j < b.Length && d == Dist(a[i], b[j])
  ensures
    forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length ==>
      d <= Dist(a[i], b[j])
{
  d := Dist(a[0], b[0]);
  var m, n := 0, 0;
  while m < a.Length && n < b.Length
    invariant 0 <= m <= a.Length && 0 <= n <= b.Length
    invariant exists i, j ::
      0 <= i < a.Length && 0 <= j < b.Length &&
        d == Dist(a[i], b[j])
    invariant forall i, j ::
      0 <= i < a.Length && 0 <= j < b.Length ==>
        d <= Dist(a[i], b[j]) || (m <= i && n <= j)
    decreases a.Length - m + b.Length - n
  {
    d := if Dist(b[n], a[m]) < d then Dist(b[n], a[m]) else d;
    if
    case a[m] == b[n] =>
      return 0;
    case a[m] < b[n] =>
      m := m + 1;
    case b[n] < a[m] =>
      n := n + 1;
  }
}
