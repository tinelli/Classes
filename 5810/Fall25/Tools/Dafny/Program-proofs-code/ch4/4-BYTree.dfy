datatype Status = On | Off | Other (n: nat)

datatype Person = P(age: nat, firstName: string, lastName: string, height: real)

// P(32, "john", "doe", 2.04)

datatype BYTree = BlueLeaf | YellowLeaf | Node(BYTree, BYTree)

function ExampleTree(): BYTree {
  Node(BlueLeaf, Node(YellowLeaf, BlueLeaf))
/*
             Node
           /      \
       BlueLeaf   Node
                /      \
          YellowLeaf  BlueLeaf
*/
}

function BlueCount(t: BYTree): nat {
  match t
  case BlueLeaf => 1
  case YellowLeaf => 0
  case Node(l, r) => 
    BlueCount(l) + BlueCount(r)
}

method testBlueCount()
{
  var t := ExampleTree();
  var c := BlueCount(t);
  assert c == 2;

  var t2 := Node(t, t);
/*
                       Node
                     /      \
                   /          \
                 /              \
             Node               Node
           /      \           /      \
      BlueLeaf    Node   BlueLeaf   Node
                 /    \            /     \
         YellowLeaf BlueLeaf YellowLeaf BlueLeaf
*/
  c := BlueCount(t2);
  assert c == 4;
}

function LeftDepth(t: BYTree): nat {
  match t
  case BlueLeaf => 0
  case YellowLeaf => 0
  case Node(l, _) => 1 + LeftDepth(l)

}

predicate IsNode(t: BYTree) {
  match t
  case YellowLeaf => false
  case BlueLeaf => false
  case Node(_, _) => true
}

predicate IsNode2(t: BYTree) {
  match t
  case Node(_, _) => true
  case _ => false
}

function GetLeft(t: BYTree): BYTree
  requires IsNode(t)
{
  match t
  case Node(l, _) => l
}

method testGetLeft() {
  var t1 := YellowLeaf;
  var t2 := Node(YellowLeaf, YellowLeaf);
  var l := GetLeft(t2);
  assert l == YellowLeaf;
}


function GetRight1(t: BYTree): BYTree
  requires t.Node?
{
  match t
  case Node(_, r) => r
}
