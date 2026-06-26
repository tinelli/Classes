module ListLibrary {
  datatype List<T> = Nil | Cons(head: T, tail: List<T>)

  function Snoc<T>(xs: List<T>, y: T): List<T> {
    match xs
    case Nil => Cons(y, Nil)
    case Cons(x, tail) => Cons(x, Snoc(tail, y))
  }
}

module ImmutableQueue {
  import LL = ListLibrary

  export
    provides Queue, Empty, Enqueue, Dequeue
    provides LL, Elements
    provides EmptyCorrect, EnqueueCorrect, DequeueCorrect
    provides EmptyUnique

  type Queue<A>
  function Empty(): Queue
  function Enqueue<A>(q: Queue, a: A): Queue
  function Dequeue<A>(q: Queue): (A, Queue)
    requires q != Empty<A>()

  ghost function Elements(q: Queue): LL.List

  lemma EmptyCorrect<A>()
    ensures Elements(Empty<A>()) == LL.Nil
  lemma EnqueueCorrect<A>(q: Queue, x: A)
    ensures Elements(Enqueue(q, x)) == LL.Snoc(Elements(q), x)
  lemma DequeueCorrect(q: Queue)
    requires q != Empty()
    ensures var (a, q') := Dequeue(q);
      LL.Cons(a, Elements(q')) == Elements(q)

  lemma EmptyUnique(q: Queue)
    ensures Elements(q) == LL.Nil ==> q == Empty()
}

module QueueClient {
  import IQ = ImmutableQueue
  method Client() {
    IQ.EmptyCorrect<int>();   var q := IQ.Empty();
    IQ.EnqueueCorrect(q, 20); q := IQ.Enqueue(q, 20);
    IQ.DequeueCorrect(q);     var (a, q') := IQ.Dequeue(q);
    assert a == 20;
    IQ.EmptyUnique(q');
    assert q' == IQ.Empty();
  }
}
