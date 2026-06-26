module BlockChain {
  export
    provides Ledger, Balance
    provides Init, Deposit, Withdraw

  import LL = ListLibrary

  type Ledger = LL.List<int>

  function Init(): Ledger
    // specification left as an exercise...

  function Deposit(ledger: Ledger, n: nat): Ledger
    // specification left as an exercise...

  function Withdraw(ledger: Ledger, n: nat): Ledger
    // specification left as an exercise...

  ghost function Balance(ledger: Ledger): int
    // specification left as an exercise...
}

module ListLibrary {
  datatype List<T> = Nil | Cons(T, List<T>)
}
