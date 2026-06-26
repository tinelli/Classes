/*
   CS:5810 Formal Methods in Software Engineering
   Fall 2025
   The University of Iowa
   
   Instructor: Cesare Tinelli

   Credits: Example from Dafny tutorial
*/


class Counter {
  // The "abstract" state which is visible to clients
  ghost var val: int

  // The actual implementation (also called the "concrete state")
  // This is meant to be hidden from the client
  var inc: nat
  var dec: nat

// The object invariant -- indicates how the abstract and
  // concrete states are related
  ghost predicate Valid()
    reads this
  {
    val == inc - dec
  }

  
  // The constructor
  constructor ()
    ensures Valid()
    ensures val == 0
  {
    inc := 0 ; dec := 0 ;

    // ghost code
    val := 0;
  }

  method Inc()
    modifies this 
    requires Valid()
    ensures Valid()
    ensures val == old(val) + 1
  {
    inc := inc + 1 ;

    val := val + 1;
  }

  method Dec()
    modifies this 
    requires Valid()
    ensures Valid()
    ensures val == old(val) - 1
  {
    dec := dec + 1 ;

    val := val - 1;
  }

  method Clear()
    modifies this
    requires Valid()
    ensures Valid()
    ensures val == 0
  {
    inc := 10 ; 
    dec := 10 ;

    val := 0;
  }

  method Get() returns (n: int)
    requires Valid()
    ensures Valid()
    ensures n == val
  {
   // return inc - dec;
    n := inc - dec;
  }

  method Set(n: int)
    modifies this
    requires Valid()
    ensures Valid()
    ensures val == n 
  {
    if n >= 0 { 
      inc := n;
      dec := 0;
    } 
    else { 
      inc := 0;
      dec := -n;
    }

    val := n;
  }
}



method test ()
{ 
	var n;
	var c := new Counter();      n := c.Get();  assert n == 0;
	c.Inc();                     n := c.Get();  assert n == 1;
	c.Inc();                     n := c.Get();  assert n == 2;
	c.Dec(); c.Dec(); c.Dec();   n := c.Get();  assert n == -1;
  c.Set(6);                    n := c.Get();  assert n == 6;
  c.Clear();                   n := c.Get();  assert n == 0;
}