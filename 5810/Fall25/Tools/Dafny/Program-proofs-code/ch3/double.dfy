
method Double(x: int) returns (d: int)
  requires x >= 0
  ensures d == 2 * x
{ 
  if x == 0 
  { 
    d := 0; 
  } else {
    var d1;
    d1 := Double(x - 1);
    d := d1 + 2;
  }
}

/*
method Double(x: int) returns (d: int)
  requires x >= 0
  ensures d == 2 * x
{ 
assert (x != 0 ==> x > 0);
assert (x == 0 ==> 0 == 2 * x) && (x != 0 ==> x - 1 >= 0);
  if x == 0 
  { 
assert 0 == 2 * x;
    d := 0; 
assert d == 2 * x;
  } else {
assert x - 1 >= 0;
    var d1;
assert x - 1 >= 0;
assert x - 1 >= 0 && forall r1 : int :: (r1 == 2 * (x - 1)) ==> (r1 + 2 == 2 * x);
    d1 := Double(x - 1);
assert d1 + 2 == 2 * x;
    d := d1 + 2;
assert d == 2 * x;
  }
assert d == 2 * x;
}
*/