datatype BYTree = BlueLeaf
                | YellowLeaf
                | Node(left: BYTree, right: BYTree)
//                     ^^^^          ^^^^^

function BlueCount(t: BYTree): nat {
  if t.BlueLeaf? then 
    1
  else if t.YellowLeaf? then 
    0
  else 
    BlueCount(t.left) + BlueCount(t.right)
//              ^^^^                ^^^^^
}

method Test() {
  assert BlueCount(BlueLeaf) == 1;
  assert BlueCount(Node(YellowLeaf, BlueLeaf)) == 1;
}

method Test1(t: BYTree) {
  assert t.BlueLeaf? <==> t == BlueLeaf;
  assert t.YellowLeaf? <==> t == YellowLeaf;
  assert t.Node? <==> IsNode(t);
}


method Test2(t: BYTree)
  requires t.Node?
{ 
  assert t.left == GetLeft(t);
  assert t.right == GetRight(t);
}



predicate IsNode(t: BYTree) {
  match t
  case Node(_, _) => true
  case _ => false
}

function GetLeft(t: BYTree): BYTree
  requires t.Node?
{
  match t
  case Node(l, _) => l
}

function GetRight(t: BYTree): BYTree
  requires t.Node?
{
  match t
  case Node(_, r) => r
}
