/*
   CS:5810 Formal Methods in Software Engineering
   Fall 2025
   The University of Iowa
   
   Instructor: Cesare Tinelli
*/

// Parametric, unbounded FIFO queue
// Implementation uses an array to store the queue elements
// in order of arrival

class Queue<T> {
  // Abtract representation of the queue's elements
  // Elements of the queue in order from least to most recent
  ghost var queue: seq<T>

  // Concrete implementation of the queue
  // container for the queue's elements
  var a: array<T>
  // size of the queue
  var n: nat

  ghost predicate Valid()
  reads this, a
  {
    // Concrete class invariant
    n <= a.Length && 
    0 < a.Length &&

    // Connection between abstract and concrete state
    queue == a[0..n]
  }

  // Empty queue constructor
  // Starts with an empty queue
  constructor (d: T)
    ensures Valid()
    ensures fresh(a)
    ensures queue == []
  {
    a := new T[5](_ => d); // initializes every array element to d
    n := 0;

    // ghost code
    queue := [];
  }

  // Front operation: it returns the oldest element of the queue
  // It does not modify the queue
method front() returns (e: T)
    requires queue != []
    requires Valid()
    ensures Valid()
    ensures queue == old(queue)
    ensures e == queue[0]
  {
    e := a[0]; 
  }
 
  // Dequeuing operation: removes and returns the oldest element of the queue
  // It has **linear** runtime in the worst-case 
  method dequeue() returns (e: T)
    modifies this, a

    requires queue != []
    requires Valid()
    ensures Valid()
    ensures queue == old(queue[1..])
    ensures e == old(queue[0])

    ensures a == old(a)
  {
    e := a[0];
    n := n - 1;
    forall i:int | 0 <= i < n {
      a[i] := a[i + 1];
    }

    // ghost code
    queue := queue[1..];
  }

  // Enqueuing operation: adds e at the end of the queue
  method enqueue(e: T)
    modifies this, a

    requires Valid()
    ensures Valid()
    ensures queue == old(queue) + [e]

    ensures old(n) < old(a.Length) ==> a == old(a)
    ensures old(n) == old(a.Length) ==> fresh(a)
  {
    if (n < a.Length) {
      a[n] := e;
    }
    else {
      var b := new T[2 * a.Length](_ => e);
      forall i:int | 0 <= i < n {
        b[i] := a[i];
      }
      a := b;
    }
    n := n + 1;

    // ghost code
    queue := queue + [e];
  }
}

method test ()
{
  var test := new Queue<int>(0);  assert test.queue == [];
  test.enqueue(1);                assert test.queue == [1];
  test.enqueue(2);                assert test.queue == [1,2];
  test.enqueue(3);                assert test.queue == [1,2,3];
  test.enqueue(2);                assert test.queue == [1,2,3,2];
  test.enqueue(4);                assert test.queue == [1,2,3,2,4];

  var f := test.front();          assert f == 1 && test.queue == [1,2,3,2,4];
  f := test.dequeue();            assert f == 1 && test.queue == [2,3,2,4];
  test.enqueue(5);                assert           test.queue == [2,3,2,4,5];
}
