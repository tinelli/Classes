datatype Tree<T> = Leaf(data: T)
                 | Node(left: Tree<T>, right: Tree<T>)

function Mirror<T>(t: Tree<T>): Tree<T> {
  match t
  case Leaf(_) => t
  case Node(l, r) => Node(Mirror(r), Mirror(l))
}

lemma {:induction false} DoubleMirror<T>(t: Tree<T>)
  ensures Mirror(Mirror(t)) == t
{
  match t
  case Leaf(_) =>
    calc {
      Mirror(Mirror(t));
    ==  // def. Mirror (inner application)
      Mirror(t);
    ==  // def. Mirror
      t;
    }
  case Node(l, r) =>
    calc {
      Mirror(Mirror(t));
    ==  // by this case
      Mirror(Mirror(Node(l, r)));
    ==  // def. Mirror (inner)
      Mirror(Node(Mirror(r), Mirror(l)));
    ==  // def. Mirror (outer)
      Node(Mirror(Mirror(l)), Mirror(Mirror(r)));
    ==  { DoubleMirror(l); DoubleMirror(r); } // Induction hypothesis
      Node(l, r);
    ==
      t;
    }
}

lemma {:induction false} DoubleMirrorShort<T>(t: Tree<T>)
  ensures Mirror(Mirror(t)) == t
{
  match t
  case Leaf(_) =>
  case Node(l, r) =>
    calc {
       Mirror(Mirror(t));
    ==  { DoubleMirrorShort(l); DoubleMirrorShort(r); } // Induction hypothesis
      t;
    }
}


// number of leafs
function Size<T>(t: Tree<T>): nat {
  match t
  case Leaf(_) => 1
  case Node(l, r) => Size(l) + Size(r)
}

lemma {:induction false} MirrorSize<T>(t: Tree<T>)
  ensures Size(Mirror(t)) == Size(t)
{
  match t
  case Leaf(x) => 
    calc {
      Size(Mirror(t));
    ==  // by this case
      Size(Mirror(Leaf(x)));
    ==  // def. Mirror
      Size(Leaf(x));
    == 
      Size(t);
    }
  case Node(l, r) =>
    calc {
      Size(Mirror(t));
    ==  // by this case
      Size(Mirror(Node(l, r)));
    ==  // def. Mirror
      Size(Node(Mirror(r), Mirror(l)));
    ==  // def. Size
      Size(Mirror(r)) + Size(Mirror(l));
    ==  { MirrorSize(r); MirrorSize(l); } // Induction hypothesis
      Size(r) + Size(l);
    ==  // def. Size
      Size(Node(l, r));
    == 
      Size(t);
    }
}

lemma {:induction false} MirrorSizeShort<T>(t: Tree<T>)
  ensures Size(Mirror(t)) == Size(t)
{
  match t
  case Leaf(x) => 
  case Node(l, r) =>
    calc {
      Size(Mirror(t));
    ==  { MirrorSize(r); MirrorSize(l); } // Induction hypothesis
      Size(t);
    }
}


lemma {:induction false} DoubleMirrorSize<T>(t: Tree<T>)
  ensures Size(Mirror(t)) == Size(Mirror(Mirror(t)))
{
  MirrorSize(t);
  assert Size(Mirror(t)) == Size(t);
  DoubleMirror(t);
  assert Size(Mirror(Mirror(t))) == Size(t);
}