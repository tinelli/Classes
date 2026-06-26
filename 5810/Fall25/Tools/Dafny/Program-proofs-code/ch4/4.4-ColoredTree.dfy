datatype ColoredTree = Leaf(Color)
                     | Node(ColoredTree, ColoredTree)

datatype Color = Blue | Yellow | Green | Red

predicate IsSwedishFlagColor(c: Color) {
  c.Blue? || c.Yellow?
}

predicate IsLithuanianFlagColor(c: Color) {
  c != Blue
}

lemma Test(a: Color) {
  var y := Yellow;
  assert IsSwedishFlagColor(y) && IsLithuanianFlagColor(y);
  var b := Blue;
  assert IsSwedishFlagColor(b) && !IsLithuanianFlagColor(b);
  var r := Red;
  assert !IsSwedishFlagColor(r) && IsLithuanianFlagColor(r);

  if IsSwedishFlagColor(a) && IsLithuanianFlagColor(a) {
    assert a == Yellow;
  }
}
