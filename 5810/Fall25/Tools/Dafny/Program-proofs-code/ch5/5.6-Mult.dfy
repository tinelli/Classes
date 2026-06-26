function Mult(x: nat, y: nat): nat {
  if y == 0 then 0 else x + Mult(x, y - 1)
}

lemma MultIsTime(x: nat, y: nat)
  ensures Mult(x, y) == x * y
{}

lemma {:induction false} MultCommutative(x: nat, y: nat)
  ensures Mult(x, y) == Mult(y, x)
{
  if x == y 
  { 
    // trivial
  } 
  else if x == 0 
  {
    assert 0 == x < y;
    MultCommutative(x, y - 1);
  } 
  else if y < x 
  {
    assert 0 <= y < x;
    MultCommutative(y, x);
  }
  else 
  {
    assert 0 < x < y;
    calc {
      Mult(x, y);
    ==  // def. Mult
      x + Mult(x, y - 1);
    ==  { MultCommutative(x, y - 1); }
      x + Mult(y - 1, x);
    ==  // def. Mult
      x + y - 1 + Mult(y - 1, x - 1);
    ==  { MultCommutative(x - 1, y - 1); }
      x + y - 1 + Mult(x - 1, y - 1);
    ==  // arithmetic 
      y + x - 1 + Mult(x - 1, y - 1);
    ==  // def. Mult
      y + Mult(x - 1, y);
    ==  { MultCommutative(x - 1, y); }
      y + Mult(y, x - 1);
    ==  // def. Mult
      Mult(y, x);
    }
  }
}
