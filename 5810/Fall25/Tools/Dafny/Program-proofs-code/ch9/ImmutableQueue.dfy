// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module ListLibrary {
  datatype List<T> = Nil | Cons(head: T, tail: List<T>)

  function Snoc<T>(xs: List<T>, y: T): List<T> {
    match xs
    case Nil => Cons(y, Nil)
    case Cons(x, tail) => Cons(x, Snoc(tail, y))
  }
}

module PreFinal0 {
//# ImmutableQueue-0
//#
}

module AddingElementFunction {
  type Queue<A>
  type List<A>
//# Elements
  ghost function Elements(q: Queue): List
//#
}

//# ImmutableQueue-1:start
module ImmutableQueue {
  import LL = ListLibrary
//# export:all
  export provides *
//# export:0
  export
//#
    GoodExportSet
//# export:1
    provides Queue, Empty, Enqueue, Dequeue
    provides LL, Elements
    provides EmptyCorrect, EnqueueCorrect, DequeueCorrect
//#
    provides EmptyUnique
//# ImmutableQueue-1:decls

  type Queue<A>
  function Empty(): Queue
  function Enqueue<A>(q: Queue, a: A): Queue
  function Dequeue<A>(q: Queue): (A, Queue)
    requires q != Empty()

  ghost function Elements(q: Queue): LL.List
  lemma EmptyCorrect<A>()
    ensures Elements(Empty<A>()) == LL.Nil
  lemma EnqueueCorrect<A>(q: Queue, x: A)
    ensures Elements(Enqueue(q, x)) == LL.Snoc(Elements(q), x)
  lemma DequeueCorrect(q: Queue)
    requires q != Empty()
    ensures var (a, q') := Dequeue(q);
      LL.Cons(a, Elements(q')) == Elements(q)
//# EmptyUnique
  lemma EmptyUnique(q: Queue)
    ensures Elements(q) == LL.Nil ==> q == Empty()
//# ImmutableQueue-1:end
}
//#

module LengthInsteadOfElements {
//# ImmutableQueue-2:start
module ImmutableQueue {
  import LL = ListLibrary

  type Queue<A>
  function Empty(): Queue
  function Enqueue<A>(q: Queue, a: A): Queue
  function Dequeue<A>(q: Queue): (A, Queue)
    requires q != Empty<A>()

//# Length
  ghost function Length(q: Queue): nat
//# ImmutableQueue-2:more
  lemma EmptyCorrect<A>()
    ensures Length(Empty<A>()) == 0
  lemma EnqueueCorrect<A>(q: Queue, x: A)
    ensures Length(Enqueue(q, x)) == Length(q) + 1
  lemma DequeueCorrect(q: Queue)
    requires q != Empty()
    ensures Length(Dequeue(q).1) == Length(q) - 1
}
//#
}
