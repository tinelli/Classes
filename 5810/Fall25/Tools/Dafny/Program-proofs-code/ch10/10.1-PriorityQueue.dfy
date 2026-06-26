module PriorityQueue {
  export
    provides PQueue, Empty, IsEmpty, Insert, RemoveMin
    provides Elements
    provides EmptyCorrect, IsEmptyCorrect
    provides InsertCorrect, RemoveMinCorrect
    reveals IsMin
    provides Valid

  type PQueue = BraunTree
  datatype BraunTree =
    | Leaf
    | Node(x: int, left: BraunTree, right: BraunTree)

  ghost predicate Valid(pq: PQueue)

  function Empty(): PQueue
  predicate IsEmpty(pq: PQueue)
  function Insert(pq: PQueue, y: int): PQueue
  function RemoveMin(pq: PQueue): (int, PQueue)
    requires !IsEmpty(pq)

  ghost function Elements(pq: PQueue): multiset<int>

  lemma EmptyCorrect()
    ensures var pq := Empty();
      Valid(pq) &&
      Elements(pq) == multiset{}
  lemma IsEmptyCorrect(pq: PQueue)
    requires Valid(pq)
    ensures IsEmpty(pq) <==> Elements(pq) == multiset{}
  lemma InsertCorrect(pq: PQueue, y: int)
    requires Valid(pq)
    ensures var pq' := Insert(pq, y);
      Valid(pq') &&
      Elements(pq') == Elements(pq) + multiset{y}
  lemma RemoveMinCorrect(pq: PQueue)
    requires Valid(pq) && !IsEmpty(pq)
    ensures var (y, pq') := RemoveMin(pq);
      Valid(pq') &&
      IsMin(y, Elements(pq)) &&
      Elements(pq') + multiset{y} == Elements(pq)

  ghost predicate IsMin(y: int, s: multiset<int>) {
    y in s && forall x :: x in s ==> y <= x
  }
}
