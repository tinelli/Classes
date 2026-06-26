/*
   CS:5810 Formal Methods in Software Engineering
   Fall 2025
   The University of Iowa
   
   Instructor: Cesare Tinelli

*/

/*
 This is a version of the counter that stores the counter 
 value in a separate Cell object, to demonstrate the use 
 of dynamic frames in Dafny.
*/
class Cell {
  var c: nat

  constructor (n: nat)
    ensures c == n
  {
    c := n;
  }

  method next()
    modifies this
    ensures c == old(c) + 1
  {
    c := c + 1;
  }

  function get(): nat
    reads this
    ensures get() == c
  { 
    c
  }

  method put(n: nat)
    modifies this
    ensures c == n
  {
    c := n;
  }
}

class Counter
{
  // Abstract (public) fields
  ghost var val: int

  // dynamic heap frame represented as a set of objects
  ghost var R: set<object> 

  // Concrete (private) fields
  var incs: Cell
  var decs: Cell

  ghost predicate Valid()
    reads this, R
  {
    // Class invariant for concrete representation 
    incs != decs

    // The heap frame R is invariant
    && R == {this, incs, decs}   

    // Connection between abstract and concrete representation
    && val == incs.get() - decs.get()
  }

  constructor ()
    ensures Valid()
    ensures val == 0

    ensures fresh(R)
  {
    incs := new Cell(0);
    decs := new Cell(0);

    // ghost code
    val := 0;
    R := { this, incs, decs };
  }

  method Inc()
    modifies R

    requires Valid()
    ensures Valid()
    ensures val == old(val) + 1

    ensures R == old(R)
  {
    incs.next();

    // ghost code
    val := val + 1;
  }

  method Dec()
    modifies R

    requires Valid()
    ensures Valid()
    ensures val == old(val) - 1

    ensures R == old(R)    
  {
    decs.next();

    // ghost code
    val := val - 1;
  }

  method Clear()
	  modifies R

		requires Valid()
		ensures Valid()
		ensures val == 0

    ensures R == old(R)    
  {
    incs.put(0) ; 
    decs.put(0) ;

    // ghost code
		val := 0;
  }

  method Get() returns (n: int)
    requires Valid()
    ensures Valid()
    ensures n == val
  {
    n := incs.get() - decs.get();
  }

	method Set(n: int)
	  modifies R

		requires Valid()
		ensures Valid()
		ensures val == n

    ensures R == old(R)    
  { 
    if n >= 0 
		  { incs.put(n) ; decs.put(0);} 
    else
		  { incs.put(0); decs.put(-n);}

		val := n;
	}
}

method test()
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
