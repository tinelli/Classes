method IllegalAssignment() returns (y: int) {
  ghost var x := 10;
  y := 2 * x; // error: cannot assign to compiled variable using a ghost
}
