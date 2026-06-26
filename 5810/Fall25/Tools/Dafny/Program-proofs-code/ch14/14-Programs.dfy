method SetEndPoints(a: array<int>, left: int, right: int)
  requires a.Length != 0
  modifies a
{
  a[0] := left;
  a[a.Length - 1] := right;
}

method Aliases(a: array<int>, b: array<int>)
  requires 100 <= a.Length
  modifies a
{
  a[0] := 10;
  var c := a;
  if b == a {
    b[10] := b[0] + 1;
  }
  c[20] := a[14] + 2;
}

method UpdateElements(a: array<int>)
  requires a.Length == 10
  modifies a
  ensures old(a[4]) < a[4]
  ensures a[6] <= old(a[6])
  ensures a[8] == old(a[8])
{
  a[4], a[8] := a[4] + 3, a[8] + 1;
  a[7], a[8] := 516, a[8] - 1;
}

method OldVsParameters(a: array<int>, i: int) returns (y: int)
  requires 0 <= i < a.Length
  modifies a
  ensures old(a[i] + y) == 25
{
  y := 25 - a[i];
}

method Increment(a: array<int>, i: int)
  requires 0 <= i < a.Length
  modifies a
  ensures a[i] == old(a)[i] + 1 // common mistake
{
  a[i] := a[i] + 1; // error: postcondition violation
}

method NewArray() returns (a: array<int>)
  ensures a.Length == 20
{
  a := new int[20];
  var b := new int[30];
  a[6] := 216;
  b[7] := 343;
}

method Caller() {
  var a := NewArray();
  a[8] := 512; // error: modification of a's elements not allowed
}


// ----------------------------------------

// Fix to NewArray specification

method NewArray'() returns (a: array<int>)
  ensures fresh(a) && a.Length == 20
{
  a := new int[20];
  var b := new int[30];
  a[6] := 216;
  b[7] := 343;
}

method Caller'() {
  var a := NewArray'();
  a[8] := 512;
}

// ----------------------------------------

predicate IsZeroArray(a: array<int>, lo: int, hi: int)
  requires 0 <= lo <= hi <= a.Length
  reads a
  decreases hi - lo
{
  lo == hi || (a[lo] == 0 && IsZeroArray(a, lo + 1, hi))
}

predicate IsZeroSeq(a: seq<int>, lo: int, hi: int)
  requires 0 <= lo <= hi <= |a|
  decreases hi - lo
{
  lo == hi || (a[lo] == 0 && IsZeroSeq(a, lo + 1, hi))
}

// ----------------------------------------

method InitArray<T>(a: array<T>, d: T)
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == d
{
  var n := 0;
  while n != a.Length
    invariant 0 <= n <= a.Length
    invariant forall i :: 0 <= i < n ==> a[i] == d
  {
    a[n] := d;
    n := n + 1;
  }
}

// ----------------------------------------

method InitMatrix<T>(a: array2<T>, d: T)
  modifies a
  ensures forall i, j ::
    0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == d
{
  var m := 0;
  while m != a.Length0
    invariant 0 <= m <= a.Length0
    invariant forall i, j ::
      0 <= i < m && 0 <= j < a.Length1 ==> a[i,j] == d
  {
    var n := 0;
    while n != a.Length1
      invariant 0 <= n <= a.Length1
      invariant forall i, j ::
        0 <= i < m && 0 <= j < a.Length1 ==> a[i,j] == d
      invariant forall j :: 0 <= j < n ==> a[m,j] == d
    {
      a[m,n] := d;
      n := n + 1;
    }
    m := m + 1;
  }
}

// ----------------------------------------

method IncrementArray(a: array<int>)
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[i]) + 1
{
  var n := 0;
  while n != a.Length
    invariant 0 <= n <= a.Length
    invariant forall i :: 0 <= i < n ==> a[i] == old(a[i]) + 1
    invariant forall i :: n <= i < a.Length ==> a[i] == old(a[i])
  {
    a[n] := a[n] + 1;
    n := n + 1;
  }
}

method IncrementArray_WithAsserts(a: array<int>)
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[i]) + 1
{
  var n := 0;
  while n != a.Length
    invariant 0 <= n <= a.Length
    invariant forall i :: 0 <= i < n ==> a[i] == old(a[i]) + 1
    invariant forall i :: n <= i < a.Length ==> a[i] == old(a[i])
  {
    assert a[n] + 1 == old(a[n]) + 1;
    a[n] := a[n] + 1;
    assert forall i :: 0 <= i < n ==> a[i] == old(a[i]) + 1;
    assert a[n] == old(a[n]) + 1;
    assert forall i :: 0 <= i < n + 1 ==> a[i] == old(a[i]) + 1;
    n := n + 1;
  }
}

// ----------------------------------------

method CopyArray(src: array, dst: array)
  requires src.Length == dst.Length
  modifies dst
  ensures forall i :: 0 <= i < src.Length ==> dst[i] == old(src[i])
{
  var n := 0;
  while n != src.Length
    invariant 0 <= n <= src.Length
    invariant forall i :: 0 <= i < n ==> dst[i] == old(src[i])
    invariant forall i :: 0 <= i < src.Length ==> src[i] == old(src[i])
  {
    dst[n] := src[n];
    n := n + 1;
  }
}

// ----------------------------------------

function F(i: int): int {
  i
}

method Aggregate_Int<T>(n: nat, d: int) {
  var a: array<int>;
  var m: array2<int>;

  a := new int[25](F);

  a := new int[25](i => i * i);

  a := new int[n](_ => 0);

  m := new int[50, 50]((i, j) => if i == j then d else 0);
}

method Aggregate_Generic<T>(a: array<T>) {
  var b: array<T>;

  b := new T[a.Length](i => a[i]); // error in accessing a

  b := new T[a.Length](i requires 0 <= i < a.Length reads a =>
                       a[i]);
}

// ----------------------------------------

method SequenceConstructor() {
  var s: seq<bool> := seq(500, i => i % 2 == 0);
}

// ----------------------------------------

method ArrayMultiassignment() {
  var a := new int[100];

  a[5], a[7] := a[5] + 25, a[7] + 49;

  forall i | 0 <= i < a.Length {
    a[i] := a[i] + i * i;
  }

  forall i | 0 <= i < a.Length && i % 2 == 0 {
    a[i] := a[i] + 1;
  }

  forall i | 0 <= i < a.Length {
    a[i] := a[i] + 1;
  }

  forall i | 0 <= i < a.Length {
    a[i] := a[(i + 1) % a.Length];
  }
}

method MatrixMultiassignment(d: int) {
  var a := new int[100, 100];

  forall i, j | 0 <= i < a.Length0 && 0 <= j < a.Length1 {
    a[i,j] := d;
  }
}

// ----------------------------------------

method CopyMatrix<T>(src: array2<T>, dst: array2<T>)
  requires src.Length0 == dst.Length0
  requires src.Length1 == dst.Length1
  modifies dst
  ensures forall i, j :: 0 <= i < dst.Length0 && 0 <= j < dst.Length1 ==>
    dst[i, j] == old(src[i, j])
{
  forall i, j | 0 <= i < dst.Length0 && 0 <= j < dst.Length1 {
    dst[i, j] := src[i, j];
  }
}

method TestHarness() {
  var m := new int[2, 1];
  m[0, 0], m[1, 0] := 5, 7;
  CopyMatrix(m, m);
  // the following assertion will not hold if you forget
  // 'old' in the specification of CopyMatrix
  assert m[1, 0] == 7;
  var n := new int[2, 1];
  CopyMatrix(m, n);
  assert m[1, 0] == n[1, 0] == 7;
}
