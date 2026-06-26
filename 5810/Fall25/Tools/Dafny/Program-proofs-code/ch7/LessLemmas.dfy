// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "Unary.dfy"

// ----------------------------------------------------------------------

module LessLemmas0 {
  import opened UnaryLibrary

//# LessCorrect
//#

//#
lemma LessCorrect_AltPost(x: Unary, y: Unary)
//# LessCorrect:AltPost
  ensures Less(x, y) == (UnaryToNat(x) < UnaryToNat(y))
//#
{
}

//# LessTransitive:0
lemma LessTransitive(x: Unary, y: Unary, z: Unary)
  requires Less(x, y) && Less(y, z)
  ensures Less(x, z)
{
}
//#
}

// ----------------------------------------------------------------------

module LessLemmas1 {
  import opened UnaryLibrary

//# LessTransitive:1
lemma LessTransitive(x: Unary, y: Unary, z: Unary)
  ensures Less(x, y) && Less(y, z) ==> Less(x, z)
//# LessTransitive:1:0
{
  if Less(x, y) && Less(y, z) {
//# LessTransitive:1:1
    if x.Suc? {
//# LessTransitive:1:2
      LessTransitive(x.pred, y.pred, z.pred);
    }
  }
}
//#

//# LessTrichotomous
lemma LessTrichotomous(x: Unary, y: Unary)
  // 1 or 3 of them are true:
  ensures Less(x, y) <==> x == y <==> Less(y, x)
  // not all 3 are true:
  ensures !(Less(x, y) && x == y && Less(y, x))
{
}
//#

}
