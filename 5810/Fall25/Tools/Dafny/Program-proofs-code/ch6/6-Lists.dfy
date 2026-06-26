datatype List<T> = Nil | Cons(head: T, tail: List<T>)

// l == [1,2,3]
const l := Cons(1, Cons(2, Cons(3, Nil)))

function Length<T>(l: List<T>): nat {
  match l
  case Nil => 0
  case Cons(_, tail) => 1 + Length(tail)
}

function Length'<T>(l: List<T>): nat {
  if l == Nil then 0 else 1 + Length'(l.tail)
}

lemma {:induction false} LengthSameAsLength'<T>(l: List<T>)
  ensures Length(l) == Length'(l)
{
  match l
  case Nil =>
  case Cons(h, t) => 
    calc {
      Length(l);
    == 
      1 + Length(t);
    == { LengthSameAsLength'(t); } // Induction Hypothesis
//    == { assume Length(t) == Length'(t); } // Induction Hypothesis
      1 + Length'(t);
    ==
      Length'(l);
    }
// alternative proof
    //  assert Length(l) == 1 + Length(t);
    //  LengthSameAsLength'(t); // assume Length(t) == Length'(t);
    //  assert Length'(l) == 1 + Length'(t);
}


function At<T>(l: List<T>, i: nat): T
  requires i < Length(l)
{
  if i == 0 then l.head else At(l.tail, i - 1)
}

function update<T>(l: List<T>, i: nat, x: T): List<T>
  requires i < Length(l)
  ensures var l' := update(l, i, x);
    Length(l') == Length(l) 
    && At(l', i) == x
    && forall j: nat :: j < Length(l) && j != i ==> At(l', j) == At(l, j)
{
  match l
  case Cons(h, Nil) => Cons(x, Nil)
  case Cons(h, t) =>
    if i == 0 then Cons(x, t)
    else Cons(h, update(t, i - 1, x))
}

const sl := Cons("a", Cons("b", Cons("c", Nil)))

const sl0 := update(sl, 0, "A")
const sl1 := update(sl, 1, "B")
const sl2 := update(sl, 2, "C")

method test() {
  assert sl0 == Cons("A", Cons("b", Cons("c", Nil)));
  assert sl1 == Cons("a", Cons("B", Cons("c", Nil)));
  assert sl2 == Cons("a", Cons("b", Cons("C", Nil)));
  assert sl  == Cons("a", Cons("b", Cons("c", Nil)));
}

// const slm1 := update(sl, -1, "B") // error
// const sl3 := update(sl, 3, "B") // error


function Append<T>(l1: List<T>, l2: List<T>): List<T>
  ensures Length(Append(l1, l2)) == Length(l1) + Length(l2)
{
  match l1
  case Nil => l2
  case Cons(x, tail) => Cons(x, Append(tail, l2))
}

lemma LengthAppend<T>(l1: List<T>, l2: List<T>)
  ensures Length(Append(l1, l2)) == Length(l1) + Length(l2)
{
}

lemma {:induction false} AppendNil<T>(l: List<T>)
  ensures Append(l, Nil) == l
{
  match l
  case Nil =>
  case Cons(x, tail) =>
    calc {
      Append(l, Nil);
    ==  // def. Append
      Cons(x, Append(tail, Nil));
    ==  { AppendNil(tail); }
      Cons(x, tail);
    ==
      l;
    }
}

lemma {:induction false} AppendAssociative<T>(l1: List<T>, l2: List<T>, l3: List<T>)
  ensures Append(Append(l1, l2), l3) == Append(l1, Append(l2, l3))
{
  match l1
  case Nil =>
  case Cons(h1, t1) =>
    calc {
       Append(Append(l1, l2), l3);
    == Append(Append(Cons(h1, t1), l2), l3);
    == Append(Cons(h1, Append(t1, l2)), l3);
    == Cons(h1, Append(Append(t1, l2), l3));
    == { AppendAssociative(t1, l2, l3); }
       Cons(h1, Append(t1, Append(l2, l3)));
    == Append(l1, Append(l2, l3));
    }
}

function Take<T>(l: List<T>, n: nat): List<T>
  requires n <= Length(l)
{
  if n == 0 then Nil else Cons(l.head, Take(l.tail, n - 1))
}
function Drop<T>(l: List<T>, n: nat): List<T>
  requires n <= Length(l)
{
  if n == 0 then l else Drop(l.tail, n - 1)
}

lemma {:induction false} AppendTakeDrop<T>(l: List<T>, n: nat)
  requires n <= Length(l)
  ensures Append(Take(l, n), Drop(l, n)) == l
{
  match n
  case 0 =>
  case _ => 
    calc {
       Append(Take(l, n), Drop(l, n));
    == Append(Cons(l.head, Take(l.tail, n - 1)), Drop(l.tail, n - 1));
    == Cons(l.head, Append(Take(l.tail, n - 1), Drop(l.tail, n - 1)));
    == { AppendTakeDrop<T>(l.tail, n - 1); }
       l;
    }
}

const il := Cons(10, Cons(20, Cons(30, Nil)))


method test2() {
   assert Drop(il, 0) == Cons(10, Cons(20, Cons(30, Nil)));
   assert Drop(il, 1) ==          Cons(20, Cons(30, Nil));
   assert Drop(il, 2) ==                   Cons(30, Nil);
   assert Drop(il, 3) ==                            Nil;
}


lemma {:induction false} AtAppend<T>(l1: List<T>, l2: List<T>, i: nat)
  requires i < Length(l1) + Length(l2)
  // ensures At(Append(l1, l2), i) == if i < Length(l1) then At(l1, i)
  //                                                    else At(l2, i - Length(l1))
  ensures i <  Length(l1) ==> At(Append(l1, l2), i) == At(l1, i)
  ensures i >= Length(l1) ==> At(Append(l1, l2), i) == At(l2, i - Length(l1))
{
  if i == 0 {
  }
  else if  i < Length(l1) {
    assert 0 < i < Length(l1);

    var h1 := l1.head;
    var t1 := l1.tail;
    calc {
       At(Append(l1, l2), i);
    == At(Append(Cons(h1, t1), l2), i);
    == At(Cons(h1, Append(t1, l2)), i);
    == At(Append(t1, l2), i - 1);
    == { AtAppend(t1, l2, i - 1); }
       At(t1, i - 1);
    == At(l1, i);
    }
  }
  else {
    assert 0 <= Length(l1) <= i;
    if l1 == Nil {}
    else {
      var t1 := l1.tail;
      calc {
         At(Append(l1, l2), i);
      == At(Append(t1, l2), i - 1);
      == { AtAppend(t1, l2, i - 1); }
         At(l2, i - Length(l1));
      }
    }
  }
}


function Find<T(==)>(l: List<T>, y: T): nat
  ensures var p := Find(l,y);
    p <= Length(l)
    && (p < Length(l) ==> At(l, p) == y)
{
  match l
  case Nil => 0
  case Cons(x, tail) =>
    if x == y then 0 else 1 + Find(tail, y)
}




function Snoc<T>(l: List<T>, y: T): List<T> {
  match l
  case Nil => Cons(y, Nil)
  case Cons(x, tail) => Cons(x, Snoc(tail, y))
}

lemma LengthSnoc<T>(l: List<T>, x: T)
  ensures Length(Snoc(l, x)) == Length(l) + 1
{
}


lemma SnocAppend<T>(l: List<T>, y: T)
  ensures Snoc(l, y) == Append(l, Cons(y, Nil))
{
}


function LiberalTake<T>(l: List<T>, n: nat): List<T>
{
  if n == 0 || l == Nil then
    Nil
  else
    Cons(l.head, LiberalTake(l.tail, n - 1))
}

function LiberalDrop<T>(l: List<T>, n: nat): List<T>
{
  if n == 0 || l == Nil then
    l
  else
    LiberalDrop(l.tail, n - 1)
}

lemma TakesDrops<T>(l: List<T>, n: nat)
  requires n <= Length(l)
  ensures Take(l, n) == LiberalTake(l, n)
  ensures Drop(l, n) == LiberalDrop(l, n)
{
}


lemma TakeDropAppend<T>(l: List<T>, l2: List<T>)
  ensures Take(Append(l, l2), Length(l)) == l
  ensures Drop(Append(l, l2), Length(l)) == l2
{
}


lemma AtDropHead<T>(l: List<T>, i: nat)
  requires i < Length(l)
  ensures Drop(l, i).Cons? && At(l, i) == Drop(l, i).head
{
}


ghost function SlowReverse<T>(l: List<T>): List<T> {
  match l
  case Nil => Nil
  case Cons(x, tail) => Snoc(SlowReverse(tail), x)
}

lemma LengthSlowReverse<T>(l: List<T>)
  ensures Length(SlowReverse(l)) == Length(l)
{
  match l
  case Nil =>
  case Cons(x, tail) =>
    LengthSnoc(SlowReverse(tail), x);
}

function ReverseAux<T>(l: List<T>, acc: List<T>): List<T>
{
  match l
  case Nil => acc
  case Cons(x, tail) => ReverseAux(tail, Cons(x, acc))
}

lemma ReverseAuxSlowCorrect<T>(l: List<T>, acc: List<T>)
  ensures ReverseAux(l, acc) == Append(SlowReverse(l), acc)
{
  match l
  case Nil =>
  case Cons(x, tail) =>
    calc {
      Append(SlowReverse(l), acc);
    ==  // def. SlowReverse
      Append(Snoc(SlowReverse(tail), x), acc);
    ==  { SnocAppend(SlowReverse(tail), x); }
      Append(Append(SlowReverse(tail), Cons(x, Nil)), acc);
    ==  { AppendAssociative(SlowReverse(tail), Cons(x, Nil), acc); }
      Append(SlowReverse(tail), Append(Cons(x, Nil), acc));
    ==  { assert Append(Cons(x, Nil), acc) == Cons(x, acc); }
      Append(SlowReverse(tail), Cons(x, acc));
    ==  { ReverseAuxSlowCorrect(tail, Cons(x, acc)); }
      ReverseAux(tail, Cons(x, acc));
    ==  // def. ReverseAux
      ReverseAux(l, acc);
    }
}


function Reverse<T>(l: List<T>): List<T> {
  ReverseAux(l, Nil)
}

lemma ReverseCorrect<T>(l: List<T>)
  ensures Reverse(l) == SlowReverse(l)
{
  calc {
    Reverse(l);
  ==  // def. Reverse
    ReverseAux(l, Nil);
  ==  { ReverseAuxSlowCorrect(l, Nil); }
    Append(SlowReverse(l), Nil);
  ==  { AppendNil(SlowReverse(l)); }
    SlowReverse(l);
  }
}

lemma ReverseAuxCorrect<T>(l: List<T>, acc: List<T>)
  ensures ReverseAux(l, acc) == Append(Reverse(l), acc)
{
  ReverseCorrect(l);
  ReverseAuxSlowCorrect(l, acc);
}

lemma LengthReverse<T>(l: List<T>)
  ensures Length(Reverse(l)) == Length(l)
{
  ReverseCorrect(l);
  LengthSlowReverse(l);
}

lemma ReverseAuxAppend<T>(l: List<T>, l2: List<T>, acc: List<T>)
  ensures ReverseAux(Append(l, l2), acc)
       == Append(Reverse(l2), ReverseAux(l, acc))
{
  match l
  case Nil =>
    ReverseAuxCorrect(l2, acc);
  case Cons(x, tail) =>
}

lemma AtReverse<T>(l: List<T>, i: nat)
  requires i < Length(l)
  ensures (LengthReverse(l);
    At(l, i) == At(Reverse(l), Length(l) - 1 - i))
{
  var x, tail := l.head, l.tail;
  LengthReverse(l);
  calc {
    At(Reverse(l), Length(l) - 1 - i);
  ==  // def. Reverse
    At(ReverseAux(l, Nil), Length(l) - 1 - i);
  ==  // def. ReverseAux
    At(ReverseAux(tail, Cons(x, Nil)), Length(l) - 1 - i);
  ==  { ReverseAuxSlowCorrect(tail, Cons(x, Nil)); }
    At(Append(SlowReverse(tail), Cons(x, Nil)), Length(l) - 1 - i);
  ==  { ReverseCorrect(tail); }
    At(Append(Reverse(tail), Cons(x, Nil)), Length(l) - 1 - i);
  ==  { AtAppend(Reverse(tail), Cons(x, Nil), Length(l) - 1 - i); }
    if Length(l) - 1 - i < Length(Reverse(tail)) then
      At(Reverse(tail), Length(l) - 1 - i)
    else
      At(Cons(x, Nil), Length(l) - 1 - i-Length(Reverse(tail)));
  ==  { LengthReverse(tail); }
    if Length(l) - 1 - i < Length(tail) then
      At(Reverse(tail), Length(l) - 1 - i)
    else
      At(Cons(x, Nil), Length(l) - 1 - i - Length(tail));
  ==  // arithmetic, using Length(l1) == Length(tail) + 1 and 0 <= i
    if 0 < i then
      At(Reverse(tail), Length(tail) - 1 - (i - 1))
    else
      At(Cons(x, Nil), 0);
  }
  if 0 < i {
    LengthReverse(tail);
    calc {
      At(Reverse(tail), Length(tail) - 1 - (i - 1));
    ==  { AtReverse(tail, i - 1); }
      At(tail, i - 1);
    ==  // def. At
      At(l, i);
    }
  }
}
