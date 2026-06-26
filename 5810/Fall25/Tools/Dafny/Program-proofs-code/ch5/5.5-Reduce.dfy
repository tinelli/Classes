function Reduce(m: nat, x: int): int {
  if m == 0 then x else Reduce(m / 2, x + 1) - m
}


lemma {:induction false} ReduceUpperBound(m: nat, x: int)
  ensures Reduce(m, x) <= x
{
  match m
  case 0 => // trivial
  case _ =>
    calc {
      Reduce(m, x);
    ==  // def. Reduce
      Reduce(m / 2, x + 1) - m;
    <=  { ReduceUpperBound(m / 2, x + 1);
          assert Reduce(m / 2, x + 1) <= x + 1; 
        }
      x + 1 - m;
    <=  { assert 0 < m; }
      x;
    }
}

lemma {:induction false} ReduceLowerBound(m: nat, x: int)
  ensures x - 2 * m <= Reduce(m, x)
{
  match m
  case 0 => // trivial
  case _ =>
    calc {
      Reduce(m, x);
    ==  // def. Reduce
      Reduce(m / 2, x + 1) - m;
    >=  { ReduceLowerBound(m / 2, x + 1);
          assert Reduce(m / 2, x + 1) >= x + 1 - 2 * (m / 2) ; 
          assert Reduce(m / 2, x + 1) - m >= x + 1 - 2 * (m / 2) - m; 
        }
      x + 1 - 2 * (m / 2) - m;
    >= { assert m >= 2 * (m / 2); }
      x + 1 - m - m;
    >  // reduce it further by -1
      x - 2 * m;
    }
}
