module ListLibrary {
  datatype List<T> = Nil | Cons(head: T, tail: List<T>)

  function Append(xs: List, ys: List): List
  {
    match xs
    case Nil => ys
    case Cons(x, tail) => Cons(x, Append(tail, ys))
  }

  lemma AppendAssociative(xs: List, ys: List, zs: List)
    ensures Append(Append(xs, ys), zs) == Append(xs, Append(ys, zs))
  {
  }

  // many other declarations go here...
}

method Main() {
  var xs, i := ListLibrary.Nil, 0;
  while i < 5 {
    xs, i := ListLibrary.Cons(i, xs), i + 1;
  }
  print xs, "\n";
}
