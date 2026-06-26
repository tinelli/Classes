class C {
  // all fields of a class are mutable
  var v: int
  var s: set<int>
  var a: array<int>

  method m(i: int, a1: array<int>, s1: seq<array<int>>)
    requires v == 42
    requires a.Length > 0
    requires a[0] == 5

    requires i == 6
    requires a1.Length > 0
    requires s1 != []
    requires s1[0].Length > 0
    requires s1[0][0] == 1

    modifies this, s1
  {
    var j: int := 17;
    v := 43;
    j := 18;
    v := 44;
    assert old(i) == 6; // i is input, so it can't be changed anyway
    assert old(j) == 18; // j is local and not have a value in the prestate

    assert v > old(this.v); // this.v has a value in the prestate 
                            // which could differ from the current one
    assert old(v) == 42;    // v is just an abbreviation of this.v

    assert old(a1) == a1;        // a1 is an input and so is immutatable
    assert old(a1[0]) == a1[0];  // In contrast, a1[0] is both mutable and
                                 // stored in the heap so its prestate value 
                                 // may change

    assert old(s1) == s1;        // s1 is an input
    assert old(s1[0]) == s1[0];  // the content of s1 cannot be changed as
                                 // it is a sequence
    
    s1[0][0] := 76;             // s1[0][0] is part of the content of the first array
    assert old(s1[0][0]) <  2;  // in s1, so its prestate value can change

    assert old(this.s) == s;    // field is mutable (and in the heap)
    assert old(a) == a;         // field is mutable (and in the heap) 
    assert old(a[0]) == 5;      // content of a is mutable (and in the heap)
  }
}


class A {
  var v: int
  constructor ()
     ensures v == 10
  {
     v := 10;
  }
}

class B {
  var a1: A
  var a2: A

  constructor () { 
    a1 := new A();
    a2 := new A();
  }

   method m()
     requires a1.v == 11
     requires a2.v == 12
     modifies this, a1, a2
     ensures a2 == old(a2)
     ensures a2.v != old(a2.v)
  {
     a1.v := 1;
    //  a1 := new A(); 
     a1.v := 20;


     assert old(this.a1.v) == 11;
     assert old(this.a1).v != 1; // this.a is from pre-state, 
                                 // but .v in current state

     a2.v := 3;
  }

  method m1()
    modifies a1, a2
    requires a1.v == a2.v == 0
    ensures {a1, a2} == old({a1, a2})
  {
     a1.v := 11;
     a2.v := 22;
  }
}

