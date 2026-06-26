method CalcExample0(x: int) {
  calc {
    5 * (x + 3);
  ==  // distribute multiplication over addition
    5 * x + 5 * 3;
  ==  // use the arithmetic fact that 5 * 3 == 15
    5 * x + 15;
  }
}

method CalcExample1(x: int, y: int) {
  calc {
    (x + y) * (x - y);
  ==  // distribute * over + and - (i.e., cross multiply)
    x*x - x*y + y*x - y*y;
  ==  // * is commutative: y*x == x*y
    x*x - x*y + x*y - y*y;
  ==  // the terms - x*y and + x*y cancel
    x*x - y*y;
  }
}

method CalcExample2(x: int, n: nat) {
  calc {
    3*x + n + n;
  ==  // n + n == 2*n
    3*x + 2*n;
  <=  // 2*n <= 3*n, since 0 <= n
    3*x + 3*n;
  ==  // distribute * over +
    3 * (x + n);
  }
}

// Shorter forms

method CalcExample0a(x: int, n: nat) {
  calc {
    5 * (x + 3);
    5 * x + 5 * 3;
    5 * x + 15;
  }
}

method CalcExample2a(x: int, n: nat) {
  calc {
    3*x + n + n;
    3*x + 2*n;
  <=
    3*x + 3*n;
    3*(x + n);
  }
}

method CalcExample2b(x: int, n: nat) {
  calc <= { // set default operator to be <=
    3*x + n + n;
  ==
    3*x + 2*n;
    3*x + 3*n;
  ==
    3*(x + n);
  }
}
