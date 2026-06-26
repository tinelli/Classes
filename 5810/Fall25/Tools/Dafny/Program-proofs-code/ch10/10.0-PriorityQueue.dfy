module PriorityQueue {
  export
    provides PQueue, Empty, IsEmpty, Insert, RemoveMin
    provides Elements
    provides EmptyCorrect, IsEmptyCorrect
    provides InsertCorrect, RemoveMinCorrect
    reveals IsMin

  type PQueue

  function Empty(): PQueue
  predicate IsEmpty(pq: PQueue)
  function Insert(pq: PQueue, y: int): PQueue
  function RemoveMin(pq: PQueue): (int, PQueue)
    requires !IsEmpty(pq)

  ghost function Elements(pq: PQueue): multiset<int>

  lemma EmptyCorrect()
    ensures Elements(Empty()) == multiset{}
  lemma IsEmptyCorrect(pq: PQueue)
    ensures IsEmpty(pq) <==> Elements(pq) == multiset{}
  lemma InsertCorrect(pq: PQueue, y: int)
    ensures Elements(Insert(pq, y))
         == Elements(pq) + multiset{y}
  lemma RemoveMinCorrect(pq: PQueue)
    requires !IsEmpty(pq)
    ensures var (y, pq') := RemoveMin(pq);
      IsMin(y, Elements(pq)) &&
      Elements(pq') + multiset{y} == Elements(pq)

  ghost predicate IsMin(y: int, s: multiset<int>) {
    y in s && forall x :: x in s ==> y <= x
  }
}
