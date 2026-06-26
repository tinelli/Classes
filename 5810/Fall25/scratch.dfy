

method LinearSearch0<T>(a: array<T>, P: T -> bool) returns (n: int) 
  ensures 0 <= n <= a.Length
  ensures n == a.Length || P(a[n])
  ensures n == a.Length ==> forall i :: 0 <= i < a.Length ==> !P(a[i]) 
{
  n := 0;

  while (n < a.Length)
    decreases a.Length - n
    invariant 0 <= n <= a.Length
    invariant forall i :: 0 <= i < n ==> !P(a[i])
  {
     if P(a[n]) {return ;}
     n := n + 1;
  }
    
}

predicate isSorted(a:array<int>)
  reads a
{
	forall i:nat,j:nat :: i <= j < a.Length ==> a[i] <= a[j]
}

// a[lo] <= a[lo+1] <= ... <= a[hi-2] <= a[hi-1]  
method binSearch(a:array<int>, K:int) returns (b:bool)
  requires isSorted(a)
  ensures b == exists i:nat :: i < a.Length && a[i] == K 
{
	var lo: nat := 0 ;
	var hi: nat := a.Length ;
	while (lo < hi)
    decreases hi - lo+1
    invariant 0 <= lo <= hi <= a.Length
    invariant forall i:nat :: (i < lo || hi <= i < a.Length) ==> a[i] != K ;
	{
		var mid: nat := (lo + hi) / 2 ;  assert  lo <= mid <= hi ;
		if (a[mid] < K) {                assert  a[lo] <= a[mid] < K ;
			lo := mid + 1 ;                assert              mid < lo <= hi;
		} else if (a[mid] > K) {         assert  K < a[mid];
			hi := mid ;                    assert              lo <= hi == mid;
		} else {
			return true ;                  assert a[mid] == K;
		}
	}
                                     assert forall i:nat :: i < a.Length ==> a[i] != K;
	return false ;                     
}


// When a method modifies values accessible through
// reference parameters (and stored in the heap),
// its specification must identify the relevant parts 
// of the heap using frames 

method SetEndPoints(a: array<int>, left: int, right: int)
 	requires a.Length != 0 
	modifies a 
{  
	a[0] := left; 
  a[a.Length - 1] := right;  
}


// If a method changes the elements of an array a given as a parameter,
// its specification must include modifies a 
method Aliases(a: array<int>, b: array<int>) 
	requires 100 <= a.Length 
	modifies a 
{ 
	a[0] := 10; 
	var c := a; 
	if b == a { 
		b[10] := b[0] + 1;   // ok since b == a
	} 
	c[20] := a[14] + 2;    // ok since c == a
}

// The expression old(E) denotes the value of E on entry to 	the enclosing method. 
	
method UpdateElements(a: array<int>) 
	requires a.Length == 10 
	modifies a 
	ensures old(a[4]) < a[4] 
	ensures a[6] <= old(a[6]) 
	ensures a[8] == old(a[8]) 
{ 
	a[4], a[8] := a[4] + 3, a[8] + 1; 
	a[7], a[8] := 516, a[8] - 1; 
}

// old affects only the heap dereferences in its argument
// Example:

		method OldVsParameters(a: array<int>, i: int) 
		returns (y: int) 
			requires 0 <= i < a.Length 
			modifies a 
			ensures old(a[i] + y) == 25
	
//	only a[i] is interpreted in the pre-state of the method




// A method is allowed to allocate a new array and change 	
// the elements of that array without mentioning this array 	
// in the modifies clause
method NewArray() returns (a: array<int>) 
	ensures a.Length == 20 
  ensures fresh(a) && a.Length == 20 
{ 
	a := new int[20]; 
	var b := new int[30]; 
	a[6] := 216; 
	b[7] := 343; 
} 		

method Caller() { 
	var a := NewArray();
	a[8] := 512;     // error: modification of a not allowed 
}

	/* To fix error, strengthen specification of NewArray to

		 method NewArray() returns (a: array<int>) 
			ensures fresh(a) && a.Length == 20 
  *
