module PriorityQueue {
  export
    provides PQueue, Empty, IsEmpty, Insert, RemoveMin
    provides Elements
    provides EmptyCorrect, IsEmptyCorrect
    provides InsertCorrect, RemoveMinCorrect
    reveals IsMin
    provides Valid

  type PQueue = BraunTree
  datatype BraunTree =
    | Leaf
    | Node(x: int, left: BraunTree, right: BraunTree)

  ghost predicate Valid(pq: PQueue) {
    IsBinaryHeap(pq) && IsBalanced(pq)
  }

  ghost predicate IsBinaryHeap(pq: PQueue) {
    match pq
    case Leaf => true
    case Node(x, left, right) =>
      IsBinaryHeap(left) && IsBinaryHeap(right) &&
      (left == Leaf || x <= left.x) &&
      (right == Leaf || x <= right.x)
  }

  ghost predicate IsBalanced(pq: PQueue) {
    match pq
    case Leaf => true
    case Node(_, left, right) =>
      IsBalanced(left) && IsBalanced(right) &&
      var L, R := |Elements(left)|, |Elements(right)|;
      L == R || L == R + 1
  }

  function Empty(): PQueue {
    Leaf
  }

  predicate IsEmpty(pq: PQueue) {
    pq == Leaf
  }

  function Insert(pq: PQueue, y: int): PQueue {
    match pq
    case Leaf => Node(y, Leaf, Leaf)
    case Node(x, left, right) =>
      if y < x then
        Node(y, Insert(right, x), left)
      else
        Node(x, Insert(right, y), left)
  }

  function RemoveMin(pq: PQueue): (int, PQueue)
    requires Valid(pq) && !IsEmpty(pq)
  {
    (pq.x, DeleteMin(pq))
  }

  function DeleteMin(pq: PQueue): PQueue
    requires IsBalanced(pq) && !IsEmpty(pq)
  {
    if pq.right == Leaf then
      pq.left
    else if pq.left.x <= pq.right.x then
      Node(pq.left.x, pq.right, DeleteMin(pq.left))
    else
      Node(pq.right.x, ReplaceRoot(pq.right, pq.left.x),
           DeleteMin(pq.left))
  }

  function ReplaceRoot(pq: PQueue, y: int): PQueue
    requires !IsEmpty(pq)
  {
    if pq.left == Leaf ||
       (y <= pq.left.x && (pq.right == Leaf || y <= pq.right.x))
    then
      Node(y, pq.left, pq.right)
    else if pq.right == Leaf then
      Node(pq.left.x, Node(y, Leaf, Leaf), Leaf)
    else if pq.left.x < pq.right.x then
      Node(pq.left.x, ReplaceRoot(pq.left, y), pq.right)
    else
      Node(pq.right.x, pq.left, ReplaceRoot(pq.right, y))
  }

  ghost function Elements(pq: PQueue): multiset<int> {
    match pq
    case Leaf => multiset{}
    case Node(x, left, right) =>
      multiset{x} + Elements(left) + Elements(right)
  }

  lemma EmptyCorrect()
    ensures var pq := Empty();
      Valid(pq) &&
      Elements(pq) == multiset{}
  {
  }

  lemma IsEmptyCorrect(pq: PQueue)
    requires Valid(pq)
    ensures IsEmpty(pq) <==> Elements(pq) == multiset{}
  {
  }

  lemma InsertCorrect(pq: PQueue, y: int)
    requires Valid(pq)
    ensures var pq' := Insert(pq, y);
      Valid(pq') &&
      Elements(pq') == Elements(pq) + multiset{y}
  {
  }

  lemma RemoveMinCorrect(pq: PQueue)
    requires Valid(pq) && !IsEmpty(pq)
    ensures var (y, pq') := RemoveMin(pq);
      Valid(pq') &&
      IsMin(y, Elements(pq)) &&
      Elements(pq') + multiset{y} == Elements(pq)
  {
    DeleteMinCorrect(pq);
  }

  lemma DeleteMinCorrect(pq: PQueue)
    requires Valid(pq) && pq != Leaf
    ensures var pq' := DeleteMin(pq);
      Valid(pq') &&
      Elements(pq') + multiset{pq.x} == Elements(pq)
  {
    if pq.left == Leaf || pq.right == Leaf {
    } else if pq.left.x <= pq.right.x {
      DeleteMinCorrect(pq.left);
    } else {
      var left, right :=
        ReplaceRoot(pq.right, pq.left.x), DeleteMin(pq.left);
      var pq' := Node(pq.right.x, left, right);
      assert pq' == DeleteMin(pq);
      ReplaceRootCorrect(pq.right, pq.left.x);
      DeleteMinCorrect(pq.left);
      calc {
        Elements(pq') + multiset{pq.x};
      ==  // def. Elements, since pq' is a Node
        multiset{pq.right.x} + Elements(left) +
        Elements(right) + multiset{pq.x};
      ==
        Elements(left) + multiset{pq.right.x} +
        Elements(right) + multiset{pq.x};
      ==  { assert Elements(left) + multiset{pq.right.x}
                == Elements(pq.right) + multiset{pq.left.x}; }
        Elements(pq.right) + multiset{pq.left.x} +
        Elements(right) + multiset{pq.x};
      ==
        Elements(right) + multiset{pq.left.x} +
        Elements(pq.right) + multiset{pq.x};
      ==  { assert Elements(right) + multiset{pq.left.x}
                == Elements(pq.left); }
        Elements(pq.left) + Elements(pq.right) +
        multiset{pq.x};
      ==
        multiset{pq.x} + Elements(pq.left) +
        Elements(pq.right);
      ==  // def. Elements, since pq is a Node
        Elements(pq);
      }
    }
  }

  lemma ReplaceRootCorrect(pq: PQueue, y: int)
    requires Valid(pq) && !IsEmpty(pq)
    ensures var pq' := ReplaceRoot(pq, y);
      Valid(pq') &&
      Elements(pq) + multiset{y} == Elements(pq') + multiset{pq.x} &&
      |Elements(pq')| == |Elements(pq)|
  {
    if pq.left == Leaf ||
       (y <= pq.left.x && (pq.right == Leaf || y <= pq.right.x))
    {
    } else if pq.right == Leaf {
    } else if pq.left.x < pq.right.x {
      var left := ReplaceRoot(pq.left, y);
      var pq' := Node(pq.left.x, left, pq.right);
      assert pq' == ReplaceRoot(pq, y);
      ReplaceRootCorrect(pq.left, y);
      calc {
        Elements(pq) + multiset{y};
      ==  // def. Elements, since pq is a Node
        multiset{pq.x} + Elements(pq.left) +
        Elements(pq.right) + multiset{y};
      ==
        Elements(pq.left) + multiset{y} +
        Elements(pq.right) + multiset{pq.x};
      ==  { assert Elements(pq.left) + multiset{y}
                == Elements(left) + multiset{pq.left.x}; } // I.H.
        multiset{pq.left.x} + Elements(left) +
        Elements(pq.right) + multiset{pq.x};
      ==  // def. Elements, since pq' is a Node
        Elements(pq') + multiset{pq.x};
      }
    } else {
      var right := ReplaceRoot(pq.right, y);
      var pq' := Node(pq.right.x, pq.left, right);
      assert pq' == ReplaceRoot(pq, y);
      ReplaceRootCorrect(pq.right, y);
      calc {
        Elements(pq) + multiset{y};
      ==  // def. Elements, since pq is a Node
        multiset{pq.x} + Elements(pq.left) +
        Elements(pq.right) + multiset{y};
      ==
        Elements(pq.right) + multiset{y} +
        Elements(pq.left) + multiset{pq.x};
      ==  { assert Elements(pq.right) + multiset{y}
                == Elements(right) + multiset{pq.right.x}; }
        multiset{pq.right.x} + Elements(pq.left) +
        Elements(right) + multiset{pq.x};
      ==  // def. Elements, since pq' is a Node
        Elements(pq') + multiset{pq.x};
      }
    }
  }

  ghost predicate IsMin(y: int, s: multiset<int>) {
    y in s && forall x :: x in s ==> y <= x
  }
}
