/*
   CS:5810 Formal Methods in Software Engineering
   Fall 2025
   The University of Iowa
   
   Instructor: Cesare Tinelli
*/

// Bank account example showcasing the idea of (heap) frames

class Trans {
  var total: nat

  constructor ()
    ensures total == 0
  {
    total := 0;
  }

  method add(n: nat)
    modifies this
    ensures total == old(total) + n
  {
    total := total + n;
  }
}


class Account
{
  // (public) abstract variables
  ghost var Balance: int         // the current balance of the account.
  ghost var Frame: set<object>   // set of all objects (in the heap)
                                 // that methods can read or modify

  // private variables
  var deposits: Trans    // stores the total amount of deposits
  var withdrawls: Trans  // stores the total amount of withdrawls

  ghost predicate Valid()
    reads this, Frame
  {
    // concrete state invariants
    && deposits != withdrawls
    
    // Frame invariant
    && Frame == {this, deposits, withdrawls}  
	  
    // connection between abstract and concrete state
    && Balance == deposits.total - withdrawls.total
  }

  constructor ()
    ensures Valid()
    ensures Balance == 0

    ensures fresh(Frame)
  {
    deposits := new Trans();
    withdrawls := new Trans();
    
    // Ghost code
    Balance := 0;
    // establishes the initial frame
    Frame := {this, deposits, withdrawls};
  }

  method GetBalance() returns (b: int)
    requires Valid()
    ensures Valid()
    ensures b == Balance
  {
    b := deposits.total - withdrawls.total;
  }

  method Deposit(amount: nat)
    modifies Frame

    requires Valid()
    ensures Valid()
    ensures Balance == old(Balance) + amount

    ensures Frame == old(Frame)
  {
    deposits.add(amount);
    
    // ghost code
    Balance := Balance + amount;
    Frame := {this, deposits, withdrawls};

  }

  method Withdraw(amount: nat)
    modifies Frame

    requires Valid()
    ensures Valid()
    ensures Balance == old(Balance) - amount

    ensures Frame == old(Frame)
  {
    withdrawls.add(amount);
    
    // ghost code
    Balance := Balance - amount;
    Frame := {this, deposits, withdrawls};
  }
}

method test()
{
  var c := new Account();  assert c.Balance == 0;
  c.Deposit(50);           assert c.Balance == 50;
  c.Withdraw(3);           assert c.Balance == 47;
  c.Deposit(50);           assert c.Balance == 97;
  c.Withdraw(100);         assert c.Balance == -3;
}
