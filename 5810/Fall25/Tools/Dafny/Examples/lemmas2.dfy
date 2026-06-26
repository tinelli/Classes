
method Arith<T>(s: seq<int>, x:int, y:int) 
  requires y > 0
  ensures x == x * 1
  ensures x <= x + 1
  ensures x + y == y + 1 + x - 1
  ensures s == ([1] + s)[1..]
  ensures y > -y
  ensures x > 10 ==> x > -x
{

}