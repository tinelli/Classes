// Lists

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

ghost predicate Ordered(l: List<int>) {
  match l
  case Nil => true
  case Cons(x, Nil) => true
  case Cons(x, Cons(y, _)) => x <= y && Ordered(l.tail)
}

function Length<T>(l: List<T>): nat {
  match l
  case Nil => 0
  case Cons(_, tail) => 1 + Length(tail)
}

function Append<T>(l1: List<T>, l2: List<T>): List<T>
  ensures Length(Append(l1, l2)) == Length(l1) + Length(l2)
{
  match l1
  case Nil => l2
  case Cons(h, t) => Cons(h, Append(t, l2))
}

function At<T>(l: List<T>, i: nat): T
  requires i < Length(l)
{
  if i == 0 then l.head else At(l.tail, i - 1)
}

// Sorting

lemma AllOrdered(l: List<int>, i: nat, j: nat)
  requires Ordered(l) && i <= j < Length(l)
  ensures At(l, i) <= At(l, j)
{
  if i == j { }
  else if i == 0 {  
    //.           0  1  2  3 ... j-1 jj 
    //       l = e0 e1 e2 e3 ...     ej
    //  l.tail = e1 e2 e3 e4 ... ej

    assert 0 == i < j < Length(l);
    assert At(l,0) <= At(l,1);
    AllOrdered(l.tail, 0, j - 1); 
  }
  else { 
    assert 0 < i < j < Length(l);
    AllOrdered(l.tail, i - 1, j - 1); 
  } 
}

//     assert At(l, 0) <= At(l, 1); 


ghost function Count(l: List<int>, i: int): nat {
  match l
  case Nil => 0
  case Cons(h, t) => (if h == i then 1 else 0) + Count(t, i)
}

ghost function Project(l: List<int>, i: int): List<int> 
   ensures var li := Project(l, i);
     Length(li) == Count(l, i)
     && forall k :: 0 <= k < Length(li) ==> At(li, k) == i
{
  match l
  case Nil => Nil
  case Cons(h, t) =>
    if h == i then Cons(h, Project(t, i)) else Project(t, i)
}

//================
// Insertion Sort
//================
  // ensures Ordered(InsertionSort(l))
  // l = [1,4,2,1,5]

  // l' = [1,2,4,4,5]
function InsertionSort(l: List<int>): List<int>  {
  match l
  case Nil => Nil
  case Cons(h, t) => 
    Insert(h, InsertionSort(t))
//    Insert(h, InsertionSort(t))
}

//    InsertOrdered(h, InsertionSort(t));


function Insert(x: int, l: List<int>): List<int> 
  ensures Count(Insert(x, l), x) == Count(l, x) + 1
  ensures forall y :: y != x ==> Count(Insert(x, l), y) == Count(l, y)
{
  match l
  case Nil => Cons(x, Nil)
  case Cons(h, t) =>
    if x < h then Cons(x, l) else Cons(h, Insert(x, t))
}

method test3() {
  var l :=  Cons(1, Cons(4, Cons(6, Nil)));
  var l1 := Cons(1, Cons(4, Cons(5, Cons(6, Nil))));
  var l0 := Cons(0, Cons(1, Cons(4, Cons(6, Nil))));

  assert Insert(5, l) == l1;
  assert Insert(0, l) == l0;
}


//===============================
// Correctness of Insertion Sort
//===============================

// Output is ordered

lemma InsertOrdered(y: int, l: List<int>)
  requires Ordered(l)
  ensures Ordered(Insert(y, l))
{}

lemma InsertionSortOrdered(l: List<int>)
  ensures Ordered(InsertionSort(l))
{
  match l
  case Nil =>
  case Cons(h, t) => InsertOrdered(h, InsertionSort(t));
}

// Element preservation of Insertion Sort

lemma InsertSameElems(y: int, l: List<int>, n: int)
  ensures Project(Cons(y, l), n) == Project(Insert(y, l), n)
{}

lemma InsertionSortSameElements(l: List<int>, n: int)
  ensures Project(l, n) == Project(InsertionSort(l), n)
{
  match l
  case Nil =>
  case Cons(h, t) => InsertSameElems(h, InsertionSort(t), n);
}

// Count preservation of Insertion Sort

lemma InsertSameCount(y: int, l: List<int>, n: int)
  ensures Count(Cons(y, l), n) == Count(Insert(y, l), n)
{}

lemma InsertionSortSameCount(l: List<int>, n: int)
  ensures Count(l, n) == Count(InsertionSort(l), n)
{
  match l
  case Nil =>
  case Cons(h, t) => InsertSameCount(h, InsertionSort(t), n);
}


//============
// Merge Sort
//============

function MergeSort(l: List<int>): List<int> {
  MergeSortAux(l, Length(l))
}

function MergeSortAux(l: List<int>, n: nat): List<int>
  requires n == Length(l)
  decreases n
{
  if n < 2 then l
  else
    var n' := n / 2;
    var (left, right) := Split(l, n');
    Merge(MergeSortAux(left, n'), MergeSortAux(right, n - n'))
}

function Split(l: List, n: nat): (List, List)
  requires n <= Length(l)
  ensures var (l1, l2) := Split(l, n);
          Append(l1, l2) == l
          && Length(l1) == n && Length(l2) == Length(l) - n
{
  match n
  case 0 => (Nil , l)
  case _ => var Cons(h, t) := l;
            var (l1, l2) := Split(t, n - 1);
            (Cons(h, l1), l2)
}

function Merge(l1: List<int>, l2: List<int>): List<int>
{
  match (l1, l2)
  case (Nil, _) => l2
  case (_, Nil) => l1
  case (Cons(h1, t1), Cons(h2, t2)) =>
    if h1 <= h2 then
      Cons(h1, Merge(t1, l2))
    else
      Cons(h2, Merge(l1, t2))
}

function {:axiom} Split'(l: List, nn: List): (List, List)
  requires Length(nn) <= Length(l)
  ensures var (left, right) := Split'(l, nn);
    var n := Length(nn) / 2;
    Length(left) == n &&
    Length(right) == Length(l) - n &&
    Append(left, right) == l
// body left as an exercise


// Correctness of Merge Sort

lemma MergeOrdered(l1: List<int>, l2: List<int>)
  requires Ordered(l1) && Ordered(l2)
  ensures Ordered(Merge(l1, l2))
{}

lemma MergeSortOrdered(l: List<int>)
  ensures Ordered(MergeSort(l))
{
  MergeSortAuxOrdered(l, Length(l));
}

lemma MergeSortAuxOrdered(l: List<int>, n: nat)
  requires n == Length(l)
  ensures Ordered(MergeSortAux(l, n))
  decreases n
{
  if 2 <= n {
    var n' := n / 2;
    var (l1, l2) := Split(l, n');
    var l1' := MergeSortAux(l1, n');
    var l2' := MergeSortAux(l2, n - n');
    MergeOrdered(l1', l2');
  }
}

// Element preservation of Insertion Sort

lemma MergeSortSameElems(l: List<int>, p: int)
  ensures Project(l, p) == Project(MergeSort(l), p)
{
  MergeSortAuxSameElems(l, Length(l), p);
}

lemma MergeSameElems(l1: List<int>, l2: List<int>, p: int)
  requires Ordered(l1) && Ordered(l2)
  ensures Project(Merge(l1, l2), p)
       == Append(Project(l1, p), Project(l2, p))
{}

lemma AppendProject(l1: List<int>, l2: List<int>, p: int)
  ensures Append(Project(l1, p), Project(l2, p))
       == Project(Append(l1, l2), p)
{}

lemma MergeSortAuxSameElems(l: List<int>, n: nat, p: int)
  requires n == Length(l)
  ensures Project(l, p) == Project(MergeSortAux(l, n), p)
  decreases n
{
  if 2 <= n {
    var n' := n / 2;
    var (l1, l2) := Split(l, n');
    var ol1 := MergeSortAux(l1, n');
    var ol2 := MergeSortAux(l2, n - n');
    calc {
      Project(MergeSortAux(l, n), p);
    ==  // def. MergeSortAux
      Project(Merge(ol1, ol2), p);
    ==  { MergeSortAuxOrdered(l1, n');
          MergeSortAuxOrdered(l2, n - n');
          MergeSameElems(ol1, ol2, p);
        }
      Append(Project(ol1, p), Project(ol2, p));
    ==  { MergeSortAuxSameElems(l1, n', p); 
          MergeSortAuxSameElems(l2, n - n', p); }
      Append(Project(l1, p), Project(l2, p));
    ==  { AppendProject(l1, l2, p); }
      Project(Append(l1, l2), p);
    ==
      Project(l, p);
    }
  }
}
