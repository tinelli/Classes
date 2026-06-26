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
  constructor()
    ensures Valid()
    ensures val == 0
  {
    inc := 0 ; dec := 0 ;

    // ghost code (to establish the postcondition)
    val := 0;
  }

  // Method implementations.  Note that the specifications only
  // mention the abstract state and not the concrete state.  This
  // allows us to later change the implementation without breaking
  // any client code.

  method Inc()
    modifies this

    requires Valid() // (val = inc - dec)
    ensures Valid()
    ensures val == old(val) + 1
  {
    inc := inc + 1 ;

    // ghost code
    val := val + 1;
  }

  method Dec()
    modifies this
    requires Valid()
    ensures Valid()
    ensures val == old(val) - 1
  {
    dec := dec + 1 ;
		
    // ghost code
    val := val - 1;
  }

  method Clear()
    modifies this
    requires Valid()
    ensures Valid()
    ensures val == 0
  {
    inc := 0 ; 
    dec := 0 ;

    // ghost code
    val := 0;
  }

  method Get() returns (n: int)
    requires Valid()
    ensures Valid()
    ensures n == val
    ensures val == old(val) 
  {
    n := inc - dec;
  }

  method Set(n: int)
    modifies this
    requires Valid()
    ensures Valid()
    ensures n == val
  {
    if n < 0 { 
			inc := 0;
			dec := -n;
		} 
    else { 
			inc := n;
			dec := 0;
		}

 		// ghost code
    val := n;
  }
}

method test ()
{ 
  var c := new Counter();  
                assert c.val == 0;
  c.Inc();      assert c.val == 1;
  c.Inc();      assert c.val == 2;
  c.Dec();      assert c.val == 1;
  c.Inc();      assert c.val == 2;
  c.Clear();    assert c.val == 0;
  c.Dec();      assert c.val == -1;
  c.Set(5);     assert c.val == 5;
  c.Set(-3);    assert c.val == -3;
}