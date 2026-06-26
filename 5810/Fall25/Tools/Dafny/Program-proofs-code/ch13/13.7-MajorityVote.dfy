function Count<T(==)>(a: seq<T>, lo: int, hi: int, x: T): nat
  requires 0 <= lo <= hi <= |a|
{
  if lo == hi then
    0
  else
    Count(a, lo, hi - 1, x) + if a[hi - 1] == x then 1 else 0
}

lemma SplitCount<T>(a: seq<T>, lo: int, mid: int, hi: int, x: T)
  requires 0 <= lo <= mid <= hi <= |a|
  ensures Count(a, lo, mid, x) + Count(a, mid, hi, x)
       == Count(a, lo, hi, x);
{
}

lemma DistinctCounts<T>(a: seq<T>, lo: int, hi: int, x: T, y: T)
  requires 0 <= lo <= hi <= |a|
  ensures x != y ==>
    Count(a, lo, hi, x) + Count(a, lo, hi, y) <= hi - lo
{
}

// ----------------------------------------

predicate HasMajority<T(==)>(a: seq<T>, lo: int, hi: int, x: T)
  requires 0 <= lo <= hi <= |a|
{
  hi - lo < 2 * Count(a, lo, hi, x)
}

predicate HasMajority_Alternative<T(==)>(a: seq<T>, lo: int, hi: int, x: T)
  requires 0 <= lo <= hi <= |a|
{
  (hi - lo) / 2 < Count(a, lo, hi, x)
}

lemma HasMajority_Alt_Same<T>(a: seq<T>, lo: int, hi: int, x: T)
  requires 0 <= lo <= hi <= |a|
  ensures HasMajority(a, lo, hi, x) == HasMajority_Alternative(a, lo, hi, x)
{
}

// ----------------------------------------

method FindWinner'<Candidate(==)>(a: seq<Candidate>) returns (k: Candidate)
  requires exists K :: HasMajority(a, 0, |a|, K)
  ensures HasMajority(a, 0, |a|, k)
{
  ghost var K :| HasMajority(a, 0, |a|, K);
  k := FindWinner(a, K);
}

method FindWinner_Ghost<Candidate(==)>(a: seq<Candidate>, ghost K: Candidate)
    returns (ghost k: Candidate)
  requires HasMajority(a, 0, |a|, K)
  ensures k == K
{
  k := K;
}

// ----------------------------------------

method FindWinner<Candidate(==)>(a: seq<Candidate>, ghost K: Candidate)
    returns (k: Candidate)
  requires HasMajority(a, 0, |a|, K)
  ensures k == K
{
  k := a[0];
  var lo, hi, c := 0, 1, 1;
  while hi < |a|
    invariant 0 <= lo <= hi <= |a|
    invariant c == Count(a, lo, hi, k)
    invariant HasMajority(a, lo, hi, k)
    invariant HasMajority(a, lo, |a|, K)
  {
    if a[hi] == k {
      hi, c := hi + 1, c + 1;
    } else if hi + 1 - lo < 2 * c {
      hi := hi + 1;
    } else {
      hi := hi + 1;
      calc {
        true;
      ==>
        2 * Count(a, lo, hi, k) == hi - lo;
      ==>  { DistinctCounts(a, lo, hi, k, K); }
        2 * Count(a, lo, hi, K) <= hi - lo;
      ==>  { SplitCount(a, lo, hi, |a|, K); }
        |a| - hi < 2 * Count(a, hi, |a|, K);
      ==  // def. HasMajority
        HasMajority(a, hi, |a|, K);
      }
      k, lo, hi, c := a[hi], hi, hi + 1, 1;
    }
  }
  DistinctCounts(a, lo, |a|, k, K);
}

// ----------------------------------------

method FindWinner_NoCalc<Candidate(==)>(a: seq<Candidate>, ghost K: Candidate)
    returns (k: Candidate)
  requires HasMajority(a, 0, |a|, K)
  ensures k == K
{
  k := a[0];
  var lo, hi, c := 0, 1, 1;
  while hi < |a|
    invariant 0 <= lo <= hi <= |a|
    invariant c == Count(a, lo, hi, k)
    invariant HasMajority(a, lo, hi, k)
    invariant HasMajority(a, lo, |a|, K)
  {
    if a[hi] == k {
      hi, c := hi + 1, c + 1;
    } else if hi + 1 - lo < 2 * c {
      hi := hi + 1;
    } else {
      hi := hi + 1;
      DistinctCounts(a, lo, hi, k, K);
      SplitCount(a, lo, hi, |a|, K);
      k, lo, hi, c := a[hi], hi, hi + 1, 1;
    }
  }
  DistinctCounts(a, lo, |a|, k, K);
}

// ----------------------------------------

method SearchForWinner<Candidate(==)>(a: seq<Candidate>,
                                      ghost hasWinner: bool,
                                      ghost K: Candidate)
    returns (k: Candidate)
  requires |a| != 0
  requires hasWinner ==> HasMajority(a, 0, |a|, K)
  ensures hasWinner ==> k == K
{
  k := a[0];
  var lo, hi, c := 0, 1, 1;
  while hi < |a|
    invariant 0 <= lo <= hi <= |a|
    invariant c == Count(a, lo, hi, k)
    invariant HasMajority(a, lo, hi, k)
    invariant hasWinner ==> HasMajority(a, lo, |a|, K)
  {
    if a[hi] == k {
      hi, c := hi + 1, c + 1;
    } else if hi + 1 - lo < 2 * c {
      hi := hi + 1;
    } else {
      hi := hi + 1;
      DistinctCounts(a, lo, hi, k, K);
      SplitCount(a, lo, hi, |a|, K);
      if hi == |a| {
        return;
      }
      k, lo, hi, c := a[hi], hi, hi + 1, 1;
    }
  }
  DistinctCounts(a, lo, |a|, k, K);
}

// ----------------------------------------

datatype Result<Candidate> = NoWinner | Winner(Candidate)

// Note, method "DetermineElection" is slightly different here than
// in Section 13.7.5 of the book (pages 317 and 318). The difference
// comes about from a necessary change in the Dafny verifier that
// took place after the book had gone into production. It now takes
// more work to convince the verifier that "DetermineElection" returns
// "NoWinner" under the right circumstances.
//
// There are several ways to convince the verifier of the method's
// correctness. The solution that's easiest to understand is to add
// a call to a new lemma, "MajorityIsAmongTheVotes(a)", which says:
//
//     If the votes in a sequence "a" contain a majority winner,
//     then that winner is among the votes in "a".
//
// The lemma seems obvious, but needs to be given to the verifier.
//
// In more detail, the delicate part of the situation is that, if
// the type parameter "Candidate" stands for some kind of reference
// type (like the "class" types that are used in Chapters 16 and 17),
// then what if there's no winner at the time "SearchForWinner" is
// called, but then "SearchForWinner" allocates a new "Candidate"
// object that turns out to be a majority winner? This situation
// cannot arise, because any majority winner must already be in the
// sequence given to "SearchForWinner". But the verifier does not
// figure that out by itself.
//
// A moral of the story is that it's often not a good idea to, as
// I had done, quantify over all values of a given type. A more
// advisable approach is to give "SearchForWinner" a set "S" of
// candidates (say, a set of registered candidates of the election),
// require that all candidates in "a" are drawn from the set "S",
// and to restrict the quantifications such that they range only
// over candidates in "S".

method DetermineElection<Candidate(==)>(a: seq<Candidate>)
    returns (result: Result<Candidate>)
  ensures match result
    case Winner(c) => HasMajority(a, 0, |a|, c)
    case NoWinner => !exists c :: HasMajority(a, 0, |a|, c)
{
  if |a| == 0 {
    return NoWinner;
  }

  ghost var hasWinner := exists c :: HasMajority(a, 0, |a|, c);
  ghost var w;
  if hasWinner {
    w :| HasMajority(a, 0, |a|, w);
  } else {
    w := a[0];
  }
  var c := SearchForWinner(a, hasWinner, w);
  MajorityIsAmongTheVotes(a); // this lemma call was not in the book (see comment above)
  return if HasMajority(a, 0, |a|, c) then
      Winner(c)
    else
      NoWinner;
}

// The following two lemmas were not used in the book.

lemma MajorityIsAmongTheVotes<Candidate>(a: seq<Candidate>)
  ensures forall c :: HasMajority(a, 0, |a|, c) ==> c in a;
{
  // The "forall" statement on the following line is a variation of
  // the aggregate statement that is used in Chapters 14 and 15.
  // Here, it corresponds to the "universal introduction" rule in logi.
  // For details, see the Dafny reference manual.
  forall c | Count(a, 0, |a|, c) != 0
    ensures c in a
  {
    NonemptyCount(a, 0, |a|, c);
  }
}

lemma NonemptyCount<T>(a: seq<T>, lo: int, hi: int, x: T)
  requires 0 <= lo <= hi <= |a|
  requires Count(a, lo, hi, x) != 0
  ensures x in a
{
  // proved by automatic induction
}

// There are other ways to solve the problem. Since the problem only
// occurs when type parameter "Candidate" can stand for some kind of
// reference type, another solution is to restrict the type parameters
// to non-reference types. This is done by adding the "(!new)" type
// characteristic, as the following method does:

method DetermineElection'<Candidate(==,!new)>(a: seq<Candidate>)
    returns (result: Result<Candidate>)
  ensures match result
    case Winner(c) => HasMajority(a, 0, |a|, c)
    case NoWinner => !exists c :: HasMajority(a, 0, |a|, c)
{
  if |a| == 0 {
    return NoWinner;
  }

  ghost var hasWinner := exists c :: HasMajority(a, 0, |a|, c);
  ghost var w;
  if hasWinner {
    w :| HasMajority(a, 0, |a|, w);
  } else {
    w := a[0];
  }
  var c := SearchForWinner(a, hasWinner, w);
  return if HasMajority(a, 0, |a|, c) then
      Winner(c)
    else
      NoWinner;
}
