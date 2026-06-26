module ImmutableQueue {
  import LL = ListLibrary

  export
    provides Queue, Empty, Enqueue, Dequeue
    provides LL, Elements
    provides EmptyCorrect, EnqueueCorrect, DequeueCorrect
    provides EmptyUnique
    provides IsEmpty

  datatype Queue<A> = FQ(front: LL.List<A>, rear: LL.List<A>)

  function Empty(): Queue {
    FQ(LL.Nil, LL.Nil)
  }

  predicate IsEmpty(q: Queue)
    ensures IsEmpty(q) <==> q == Empty()
  {
    q == FQ(LL.Nil, LL.Nil)
  }

  function Enqueue<A>(q: Queue, x: A): Queue {
    FQ(q.front, LL.Cons(x, q.rear))
  }

  function Dequeue<A>(q: Queue): (A, Queue)
    requires q != Empty()
  {
    match q.front
    case Cons(x, front') =>
      (x, FQ(front', q.rear))
    case Nil =>
      var front := LL.Reverse(q.rear);
      (front.head, FQ(front.tail, LL.Nil))
  }

  ghost function Elements(q: Queue): LL.List {
    LL.Append(q.front, LL.Reverse(q.rear))
  }

  lemma EmptyCorrect<A>()
    ensures Elements(Empty<A>()) == LL.Nil
  {
  }

  lemma EnqueueCorrect<A>(q: Queue, x: A)
    ensures Elements(Enqueue(q, x)) == LL.Snoc(Elements(q), x)
  {
    calc {
      Elements(Enqueue(q, x));
    ==  // def. Enqueue
      Elements(FQ(q.front, LL.Cons(x, q.rear)));
    ==  // def. Elements
      LL.Append(q.front, LL.Reverse(LL.Cons(x, q.rear)));
    ==  { LL.ReverseCons(x, q.rear); }
      LL.Append(q.front,
                LL.Append(LL.Reverse(q.rear), LL.Cons(x, LL.Nil)));               
    ==  { LL.AppendAssociative(q.front, LL.Reverse(q.rear),
                               LL.Cons(x, LL.Nil)); }
      LL.Append(LL.Append(q.front, LL.Reverse(q.rear)),
                LL.Cons(x, LL.Nil));
    ==  // def. Elements
      LL.Append(Elements(q), LL.Cons(x, LL.Nil));
    ==  { LL.SnocAppend(Elements(q), x); }
      LL.Snoc(Elements(q), x);
    }
  }

  lemma DequeueCorrect(q: Queue)
    requires q != Empty()
    ensures var (a, q') := Dequeue(q);
      LL.Cons(a, Elements(q')) == Elements(q)
  {
    match q.front
    case Cons(x, front') =>
    case Nil =>
      var front := LL.Reverse(q.rear);
      var (a, q') := (front.head, FQ(front.tail, LL.Nil));
      calc {
        LL.Cons(a, Elements(q'));
      ==  // def. Elements
        LL.Cons(a, LL.Append(q'.front, LL.Reverse(q'.rear)));
      ==  // what q' is
        LL.Cons(a, LL.Append(front.tail, LL.Reverse(LL.Nil)));
      ==  // def. LL.Reverse
        LL.Cons(a, LL.Append(front.tail, LL.Nil));
      ==  { LL.AppendNil(front.tail); }
        LL.Cons(a, front.tail);
      ==  // what a is, def. LL.Cons, and what front is
        LL.Reverse(q.rear);
      ==  // def. LL.Append, since q.front is empty
        LL.Append(q.front, LL.Reverse(q.rear));
      ==  // def. Elements
        Elements(q);
      }
  }

  lemma EmptyUnique(q: Queue)
    ensures Elements(q) == LL.Nil ==> q == Empty()
  {
  }
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

module QueueExtender {
  import IQ = ImmutableQueue

  function TryDequeue<A>(q: IQ.Queue, default: A): (A, IQ.Queue)
  {
    if IQ.IsEmpty(q) then (default, q) else IQ.Dequeue(q)
  }
}

// List library

module ListLibrary {
  datatype List<T> = Nil | Cons(head: T, tail: List<T>)

  function Length(xs: List): nat
  {
    match xs
    case Nil => 0
    case Cons(_, tail) => 1 + Length(tail)
  }

  function Append(xs: List, ys: List): List
  {
    match xs
    case Nil => ys
    case Cons(x, tail) => Cons(x, Append(tail, ys))
  }

  lemma AppendAssociative(xs: List, ys: List, zs: List)
    ensures Append(Append(xs, ys), zs) == Append(xs, Append(ys, zs))
  {
  }

  lemma AppendNil<T>(xs: List<T>)
    ensures Append(xs, Nil) == xs
  {
  }

  function Snoc<T>(xs: List<T>, y: T): List<T> {
    match xs
    case Nil => Cons(y, Nil)
    case Cons(x, tail) => Cons(x, Snoc(tail, y))
  }

  lemma SnocAppend<T>(xs: List<T>, y: T)
    ensures Snoc(xs, y) == Append(xs, Cons(y, Nil))
  {
  }

  function Reverse(xs: List): List
    ensures Length(Reverse(xs)) == Length(xs)
  {
    ReverseAux(xs, Nil)
  }

  function ReverseAux(xs: List, acc: List): List
    ensures Length(ReverseAux(xs, acc)) == Length(xs) + Length(acc)
  {
    match xs
    case Nil => acc
    case Cons(x, tail) => ReverseAux(tail, Cons(x, acc))
  }

  lemma ReverseCons<A>(y: A, xs: List)
    ensures Reverse(Cons(y, xs)) == Append(Reverse(xs), Cons(y, Nil))
  {
    ReverseAuxCons(y, xs, Nil);
  }

  lemma ReverseAuxCons<A>(y: A, xs: List, acc: List)
    ensures ReverseAux(Cons(y, xs), acc) == Append(Reverse(xs), Cons(y, acc))
  {
    ReverseAuxCorrect(xs, Cons(y, acc));
  }

  lemma ReverseAuxCorrect(xs: List, acc: List)
    ensures ReverseAux(xs, acc) == Append(Reverse(xs), acc)
  {
    match xs
    case Nil =>
    case Cons(x, tail) =>
      calc {
        ReverseAux(Cons(x, tail), acc);
      ==
        ReverseAux(tail, Cons(x, acc));
      ==  { ReverseAuxCorrect(tail, Cons(x, acc)); }
        Append(Reverse(tail), Cons(x, acc));
      ==
        Append(Reverse(tail), Append(Cons(x, Nil), acc));
      ==  { AppendAssociative(Reverse(tail), Cons(x, Nil), acc); }
        Append(Append(Reverse(tail), Cons(x, Nil)), acc);
      }
  }
}
