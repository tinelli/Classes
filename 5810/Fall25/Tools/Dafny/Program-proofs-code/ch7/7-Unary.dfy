datatype Unary = Zero | Suc(pred: Unary)

function UnaryToNat(x: Unary): nat {
  match x
  case Zero => 0
  case Suc(x') => 1 + UnaryToNat(x')
}

function NatToUnary(n: nat): Unary {
  if n == 0 then Zero else Suc(NatToUnary(n-1))
}

lemma NatUnaryCorrespondence(n: nat, x: Unary)
  ensures UnaryToNat(NatToUnary(n)) == n
  ensures NatToUnary(UnaryToNat(x)) == x
{
}

predicate Less(x: Unary, y: Unary) {
  y != Zero && (x.Suc? ==> Less(x.pred, y.pred))
}

predicate LessAlt(x: Unary, y: Unary) {
  y != Zero && (x == Zero || Less(x.pred, y.pred))
}

lemma LessSame(x: Unary, y: Unary)
  ensures Less(x, y) == LessAlt(x, y)
{
}

lemma LessCorrect(x: Unary, y: Unary)
  ensures Less(x, y) <==> UnaryToNat(x) < UnaryToNat(y)
{
}

lemma LessTransitive(x: Unary, y: Unary, z: Unary)
  requires Less(x, y) && Less(y, z)
  ensures Less(x, z)
{
}

lemma LessTrichotomous(x: Unary, y: Unary)
  // 1 or 3 of them are true:
  ensures Less(x, y) <==> x == y <==> Less(y, x)
  // not all 3 are true:
  ensures !(Less(x, y) && x == y && Less(y, x))
{
}

function Add(x: Unary, y: Unary): Unary {
  match y
  case Zero => x
  case Suc(y') => Suc(Add(x, y'))
}

lemma {:induction false} AddCorrect(x: Unary, y: Unary)
  ensures UnaryToNat(Add(x, y)) == UnaryToNat(x) + UnaryToNat(y)
{
  match y
  case Zero =>
  case Suc(y') =>
    calc {
      UnaryToNat(Add(x, y));
    ==  // y == Suc(y')
      UnaryToNat(Add(x, Suc(y')));
    ==  // def. Add
      UnaryToNat(Suc(Add(x, y')));
    ==  // def. UnaryToNat
      1 + UnaryToNat(Add(x, y'));
    ==  { AddCorrect(x, y'); }
      1 + UnaryToNat(x) + UnaryToNat(y');
    ==  // def. UnaryToNat
      UnaryToNat(x) + UnaryToNat(Suc(y'));
    ==  // y == Suc(y')
      UnaryToNat(x) + UnaryToNat(y);
    }
}

lemma {:induction false} SucAdd(x: Unary, y: Unary)
  ensures Suc(Add(x, y)) == Add(Suc(x), y)
{
  match y
  case Zero =>
  case Suc(y') =>
    calc {
      Suc(Add(x, Suc(y')));
    ==  // def. Add
      Suc(Suc(Add(x, y')));
    ==  { SucAdd(x, y'); }
      Suc(Add(Suc(x), y'));
    ==  // def. Add
      Add(Suc(x), Suc(y'));
    }
}

lemma {:induction false} AddZero(x: Unary)
  ensures Add(Zero, x) == x
{
  match x
  case Zero =>
  case Suc(x') =>
    calc {
      Add(Zero, Suc(x'));
    ==  // def. Add
      Suc(Add(Zero, x'));
    ==  { AddZero(x'); }
      Suc(x');
    }
}

function Sub(x: Unary, y: Unary): Unary
  requires !Less(x, y)
{
  match y
  case Zero => x
  case Suc(y') => Sub(x.pred, y')
}

lemma SubCorrect(x: Unary, y: Unary)
  requires !Less(x, y)
  ensures UnaryToNat(Sub(x, y)) == UnaryToNat(x) - UnaryToNat(y)
{
}

function Mul(x: Unary, y: Unary): Unary {
  match x
  case Zero => Zero
  case Suc(x') => Add(Mul(x', y), y)
}

lemma MulCorrect(x: Unary, y: Unary)
  ensures UnaryToNat(Mul(x, y)) == UnaryToNat(x) * UnaryToNat(y)
{
  match x
  case Zero =>
  case Suc(x') =>
    calc {
      UnaryToNat(Mul(x, y));
    ==  // def. Mul
      UnaryToNat(Add(Mul(x', y), y));
    ==  { AddCorrect(Mul(x', y), y); }
      UnaryToNat(Mul(x', y)) + UnaryToNat(y);
      // Dafny can take it from here on
    }
}

function DivMod(x: Unary, y: Unary): (Unary, Unary)
  requires y != Zero
  decreases UnaryToNat(x)
{
  if Less(x, y) then
    (Zero, x)
  else
    SubCorrect(x, y);
    var r := DivMod(Sub(x, y), y);
    (Suc(r.0), r.1)
}

lemma SubStructurallySmaller(x: Unary, y: Unary)
  requires !Less(x, y) && y != Zero
  ensures Sub(x, y) < x
{
}

lemma AddSub(x: Unary, y: Unary)
  requires !Less(x, y)
  ensures Add(Sub(x, y), y) == x
// proof left as an exercise

lemma AddCommAssoc(x: Unary, y: Unary, z: Unary)
  ensures Add(Add(x, y), z) == Add(Add(x, z), y)
// proof left as an exercise

lemma DivModCorrect(x: Unary, y: Unary)
  requires y != Zero
  ensures var (d, m) := DivMod(x, y);
    Add(Mul(d, y), m) == x &&
    Less(m, y)
{
  var (d, m) := DivMod(x, y);
  if Less(x, y) {
    assert d == Zero && m == x; // since (d, m) == DivMod(x, y)
    calc {
      Add(Mul(d, y), m) == x;
    ==  // d, m
      Add(Mul(Zero, y), x) == x;
    ==  // def. Mul
      Add(Zero, x) == x;
    ==  { AddZero(x); }
      true;
    }
  } else {
    var (d', m') := DivMod(Sub(x, y), y);
    assert d == Suc(d') && m == m'; // since (d, m) == DivMod(x, y)
    calc {
      true;
    ==>  { SubStructurallySmaller(x, y);
           DivModCorrect(Sub(x, y), y); }
      Add(Mul(d', y), m) == Sub(x, y) && Less(m, y);
    ==>  // add y to both sides
      Add(Add(Mul(d', y), m), y) == Add(Sub(x, y), y) &&
      Less(m, y);
    ==  { AddSub(x, y); }
      Add(Add(Mul(d', y), m), y) == x && Less(m, y);
    ==  { AddCommAssoc(Mul(d', y), m, y); }
      Add(Add(Mul(d', y), y), m) == x && Less(m, y);
    ==  // def. Mul, d
      Add(Mul(d, y), m) == x && Less(m, y);
    }
  }
}
