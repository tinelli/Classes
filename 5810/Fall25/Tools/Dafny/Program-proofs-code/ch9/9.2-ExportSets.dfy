
module ModuleC {
  export
    provides Color
    reveals Double

  datatype Color = Blue | Yellow | Green | Red

  function Double(x: int): nat
    requires 0 <= x
    ensures Double(x) % 2 == 0
  {
    if x == 0 then 0 else 2 + Double(x - 1)
  }
}

module ModuleD {
  import ModuleC

  method Test() {
    var c: ModuleC.Color;
    c := ModuleC.Yellow; // error: unresolved identifier 'Yellow'
    assert ModuleC.Double(3) == 6;
  }
}

module ModuleE {
  export
    provides Parity, F

  datatype Parity = Even | Odd

  function F(x: int): Parity
  {
    if x % 2 == 0 then Even else Odd
  }
}
