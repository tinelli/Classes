// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "Unary.dfy"

// ----------------------------------------------------------------------

module DivMod0 {
  import opened UnaryLibrary

//# SubStructurallySmaller
lemma SubStructurallySmaller(x: Unary, y: Unary)
  requires !Less(x, y) && y != Zero
  ensures Sub(x, y) < x
{
}
//#

//# DivMod:0
function DivMod(x: Unary, y: Unary): (Unary, Unary)
//# DivMod:1
  requires y != Zero
//# DivMod:2
{
  if Less(x, y) then
    (Zero, x)
  else
    var r := DivMod(Sub(x, y), y); // cannot prove termination
    (Suc(r.0), r.1)
}
//#
}

// ----------------------------------------------------------------------

module DivModTermination0 {
  import opened UnaryLibrary

}

module DivModTermination1 {
  import opened UnaryLibrary

function DivMod(x: Unary, y: Unary): (Unary, Unary)
  requires y != Zero
  decreases UnaryToNat(x)
{
  if Less(x, y) then
    (Zero, x)
  else
//# DivMod:termination:decr:1
    var r := (SubCorrect(x, y); DivMod(Sub(x, y), y));
//#
    (Suc(r.0), r.1)
}
}

module DivModTermination2 {
  import opened UnaryLibrary

function DivMod(x: Unary, y: Unary): (Unary, Unary)
  requires y != Zero
  decreases UnaryToNat(x)
{
  if Less(x, y) then
    (Zero, x)
  else
//# DivMod:termination:decr:2
    var r := DivMod(SubCorrect(x, y); Sub(x, y), y);
//#
    (Suc(r.0), r.1)
}
}

// ----------------------------------------------------------------------

module DivMod1 {
  import opened UnaryLibrary
  import opened DivMod0

//# DivMod
function DivMod(x: Unary, y: Unary): (Unary, Unary)
  requires y != Zero
{
  if Less(x, y) then
    (Zero, x)
  else
    SubStructurallySmaller(x, y);
    var r := DivMod(Sub(x, y), y);
    (Suc(r.0), r.1)
}
//#

/*
//# DivMod:alt
    var (d, m) := DivMod(Sub(x, y), y);
    (Suc(d), m)
//#
*/
}

// ----------------------------------------------------------------------

module DivMod2 {
  import opened UnaryLibrary
  import opened DivMod0

//# DivModCorrect:0
lemma DivModCorrect(x: Unary, y: Unary)
  requires y != Zero
  ensures var (d, m) := DivMod(x, y);
    Add(Mul(d, y), m) == x &&
    Less(m, y)
//# DivModCorrect:1
{
  var (d, m) := DivMod(x, y);
//# DivModCorrect:2
  if Less(x, y) {
    assert d == Zero && m == x; // since (d, m) == DivMod(x, y)
//# DivModCorrect:3
    calc {
      Add(Mul(d, y), m) == x;
    ==  // d, m
      Add(Mul(Zero, y), x) == x;
    ==  // def. Mul
      Add(Zero, x) == x;
    ==  { AddZero(x); }
      true;
    }
//# DivModCorrect:4
  } else {
    var (d', m') := DivMod(Sub(x, y), y);
    assert d == Suc(d') && m == m'; // since (d, m) == DivMod(x, y)
//# DivModCorrect:5
    calc {
      true;
//# DivModCorrect:6
    ==>  { SubStructurallySmaller(x, y);
           DivModCorrect(Sub(x, y), y); }
      Add(Mul(d', y), m) == Sub(x, y) && Less(m, y);
//# DivModCorrect:7
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
//#
}
