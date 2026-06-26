module ModuleA {
  function Plus(x: int, y: int): int {
    x + y
  }
}

module ModuleB {
  import ModuleA
  function Double(x: int): int {
    ModuleA.Plus(x, x)
  }
}
