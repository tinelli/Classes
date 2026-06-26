datatype Color = Blue | Yellow | Green | Red

datatype Tree<T>  =  Leaf(data: T) |  Node(left: Tree<T>, right: Tree<T>)
//           ^^^
                 

predicate AllBlue(t: Tree<Color>) {
  match t
  case Leaf(c) => c == Blue
  case Node(left, right) => AllBlue(left) && AllBlue(right) 
}

predicate AllPositive(t: Tree<int>) {
  match t
  case Leaf(c) => c > 0
  case Node(l, r) => AllPositive(l) && AllPositive(r) 
}

predicate All<T>(p: T -> bool, t: Tree<T>) 
//               ^^^^^^^^^^^^
{
  match t
  case Leaf(c) => p(c)
  case Node(l, r) => All(p, l) && All(p, r) 
}

// IsPos : int -> Bool
function IsPos(n: int): bool {
  n > 0
}

method test0() {
  var t := Node(Leaf(4), Node(Leaf(9), Leaf(3)));
  assert All(IsPos, t);
//           ^^^^^
}

method test1() {
  var t := Node(Leaf(4), Node(Leaf(9), Leaf(3)));
  assert All(x => x > 0, t);
//           ^^^^^^^^^^
}

predicate Some<T>(p: T -> bool, t: Tree<T>) 
{
  match t
  case Leaf(c) => p(c)
  case Node(l, r) => Some(p, l) || Some(p, r) 
}

method test2() {
  var t := Node(Leaf(4), Node(Leaf(9), Leaf(3)));
  assert Some(x => x > 4, t);
}


function Size<T>(t: Tree<T>): nat {
  match t
  case Leaf(_) => 1
  case Node(l, r) => Size(l) + Size(r)
}

lemma Test() {
  var a := Leaf(Blue);
  var b := Leaf(Yellow);
  var t := Node(a, Node(a, b));

  assert Size(t) == 3;
}

lemma SizeIsNat<T>(t: Tree<T>) 
  ensures Size(t) >= 0
  ensures Size(Node(t, t)) % 2 == 0
{
}

lemma SizeSub<T>(t: Tree<T>) 
  requires t.Node?
  ensures Size(t) > Size(GetRight(t))
{
}



function GetRight<T>(t: Tree<T>): Tree<T>
  requires t.Node?
{
  match t
  case Node(_, r) => r
}

/*
// general recursor (fold) over Tree<T>
function Recurse<T,U>(base: T -> U, comb: (Tree<T>, Tree<T>, U, U) -> U, t: Tree<T>): U {
  match t
  case Leaf(v) => base(v)
  case Node(t1, t2) => 
    var u1 := Recurse(base, comb, t1);
    var u2 := Recurse(base, comb, t2);
    comb(t1, t2, u1, u2)
}

function Size2<T>(t: Tree<T>): int 
  //ensures t.Node? ==> Size2(t) == Size(t.left) + Size(t.right) + 1
{
  Recurse(x => 1, (t1, t2, s1, s2) => s1 + s2, t)
}

method test3() {
  var t := Node(Leaf(Blue), Node(Leaf(Red), Leaf(Yellow)));
  assert Size2(t) == 3;
}

predicate All2<T>(p: T -> bool, t: Tree<T>)
  //ensures t.Node? ==> Size2(t) == Size(t.left) + Size(t.right) + 1
{
  Recurse(p, (t1, t2, b1, b2) => b1 && b2, t)
}

predicate Some2<T>(p: T -> bool, t: Tree<T>)
  //ensures t.Node? ==> Size2(t) == Size(t.left) + Size(t.right) + 1
{
  Recurse(p, (t1, t2, b1, b2) => b1 || b2, t)
}

method test4() {
  var t := Node(Leaf(Blue), Node(Leaf(Red), Leaf(Yellow)));
  assert !All2(x => x == Blue, t);
  assert All2(x => x != Green, t);
  assert Some2(x => x == Blue, t);
  assert !Some2(x => x == Green, t);
}

function f(g: int -> int -> int): int
{
  g(1)(3)
}
*/