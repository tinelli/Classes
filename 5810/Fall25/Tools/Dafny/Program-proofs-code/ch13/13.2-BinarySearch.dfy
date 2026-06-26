// Sortedness

ghost predicate IsSorted0(a: array<int>)
  reads a
{
  forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

ghost predicate IsSorted1(a: array<int>)
  reads a
{
  forall i :: 0 <= i ==>
    forall j :: i < j < a.Length ==> a[i] <= a[j]
}

ghost predicate IsSorted2(a: array<int>)
  reads a
{
  forall i :: 0 <= i < a.Length - 1 ==> a[i] <= a[i + 1]
}

lemma SortedTheSame(a: array<int>)
  ensures IsSorted0(a) == IsSorted1(a) == IsSorted2(a)
{
  assert IsSorted0(a) == IsSorted1(a);
  assert IsSorted0(a) ==> IsSorted2(a);
  if IsSorted2(a) && a.Length != 0 {
    for n := 1 to a.Length
      invariant forall i, j :: 0 <= i < j < n ==> a[i] <= a[j]
    {
      assert a[n-1] <= a[n];
    }
  }
}

lemma SortedTransitive(a: array<int>, i: int, j: int)
  requires forall k :: 0 <= k < a.Length - 1 ==> a[k] <= a[k+1]
  requires 0 <= i <= j < a.Length
  ensures a[i] <= a[j]
// proof left as an exercise

// Binary Search

method BinarySearch(a: array<int>, key: int) returns (n: int)
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures 0 <= n <= a.Length
  ensures forall i :: 0 <= i < n ==> a[i] < key
  ensures forall i :: n <= i < a.Length ==> key <= a[i]
{
  var lo, hi := 0, a.Length;
  while lo < hi
    invariant 0 <= lo <= hi <= a.Length
    invariant forall i :: 0 <= i < lo ==> a[i] < key
    invariant forall i :: hi <= i < a.Length ==> key <= a[i]
  {
    calc {
      lo;
    ==
      (lo + lo) / 2;
    <=  { assert lo <= hi; }
      (lo + hi) / 2; // this is mid
    <  { assert lo < hi; }
      (hi + hi) / 2;
    ==
      hi;
    }
    var mid := (lo + hi) / 2;
    if a[mid] < key {
      lo := mid + 1;
    } else {
      hi := mid;
    }
  }
  n := lo;
}

method Contains(a: array<int>, key: int) returns (present: bool)
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures present == exists i :: 0 <= i < a.Length && key == a[i]
{
  var n := BinarySearch(a, key);
  present := n < a.Length && a[n] == key;
}
