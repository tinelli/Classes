/*
   CS:5810 Formal Methods in Software Engineering
   Fall 2025
   The University of Iowa
   
   Instructor: Cesare Tinelli
*/


// Parametric FIFO queue
// using two internal sequences to store queue elements

// The use of two sequences, one to enqueue to and one dequeue from,
// allow the implementation of a enqueue and a dequeue operation 
// whose runtine, in _both_ cases, is linear in the size of the queue.

class Queue<T> {
  // Abtract representation of the queue's elements
  // Elements of the queue in order from least to most recent
  ghost var queue: seq<T>

  // Concrete implementation of the queue
  var incoming: seq<T>  // values are enqueued at the front of this sequence
  var outgoing: seq<T>  // values are dequeued from the front of this sequence

  // Specification function:
  // returns reverse of input sequence
  ghost function reverse(s: seq<T>): seq<T>
    decreases s
    ensures |s| == |reverse(s)|
    ensures forall i:nat :: i < |s| ==> s[i] == reverse(s)[|s|-1-i]
  {
    if s == [] then
      []
    else
      reverse(s[1..]) + s[0..1]
  }

  // Class invariant predicate
  ghost predicate Valid()
    reads this
  {
    // Connection between abstract and concrete state
    queue == outgoing + reverse(incoming)
    /* Example:
       outgoing == [3,6,1,8]   [6,8,2,9] == incoming
                               [9,2,8,6] == reverse(incoming)
          queue == [3,6,1,8] + [9,2,8,6]
                == [3,6,1,8,9,2,8,6]
    */
  }

  // Axiliary (private) method: 
  // it progressively moves all elements from the front of incoming
  // to the front of outgoing 
  // Note that its contract is expressed in terms of the concrete state 
  // That is OK since this is a local method
  method moveFromIncoming()
    modifies this
    requires Valid()
    requires outgoing == []
    ensures incoming == []
    ensures outgoing == reverse(old(incoming))
    ensures Valid()
  {
    while incoming != []
      decreases |incoming|
      invariant reverse(incoming) + outgoing == reverse(old(incoming))
    {
      outgoing := incoming[0..1] + outgoing; // all constant time operations
      incoming := incoming[1..];             // all constant time operations
    }
 
    queue := outgoing;
  }

  // Empty queue constructor
  // Starts with an empty queue
  constructor ()
    ensures Valid()
    ensures queue == []
  {
     incoming := [];
   	 outgoing := [];

	   queue := [];
  }

  // Front operation: it returns the oldest element of the queue
  // It does not modify the queue
  method front() returns (e: T)
    modifies this

    requires queue != []
    requires Valid()
    ensures Valid()
    ensures queue == old(queue)
    ensures e == queue[0]
  {
    if outgoing == [] { 
      moveFromIncoming(); 
    }
    e := outgoing[0]; // constant time operation 
  }

  // Dequeuing operation: removes and returns the oldest element of the queue
  method dequeue() returns (e:T)
    modifies this

    requires queue != []
    requires Valid()
    ensures Valid()
    ensures queue == old(queue[1..])
    ensures [e] + queue == old(queue)
  {
    if outgoing == [] { 
      moveFromIncoming(); 
    }
    e := outgoing[0];           // constant time operation 
    outgoing := outgoing[1..];  // constant time operation 

    queue := queue[1..];
  }

  // Enqueuing operation: adds e at the end of the queue
  method enqueue(e: T)
    modifies this

    requires Valid()
    ensures Valid()
    ensures queue == old(queue) + [e]
  {
    incoming := [e] + incoming; // constant time operation 
                                // (because the cost of (s1 + s2) is linear
                                //  in the size of s1)
    queue := queue + [e];
  }
}


method test ()
{
  var q := new Queue<int>();  assert q.queue == [];
  // var x := test.front();
  q.enqueue(1);                assert q.queue == [1];
  q.enqueue(2);                assert q.queue == [1,2];
  q.enqueue(3);                assert q.queue == [1,2,3];
  q.enqueue(2);                assert q.queue == [1,2,3,2];
  q.enqueue(4);                assert q.queue == [1,2,3,2,4];

  var f := q.front();          assert f == 1 && q.queue == [1,2,3,2,4];
  f := q.dequeue();            assert f == 1 && q.queue == [2,3,2,4];
  q.enqueue(5);                assert           q.queue == [2,3,2,4,5];
}
