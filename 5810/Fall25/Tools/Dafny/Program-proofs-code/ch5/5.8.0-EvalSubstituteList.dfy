// This file contains a more detailed proof of EvalSubstituteList

datatype List<T> = Nil | Cons(head: T, tail: List<T>)
datatype Op = Add | Mul
datatype Expr = Const(nat)
              | Var(string)
              | Node(op: Op, args: List<Expr>)

function Eval(e: Expr, env: map<string, nat>): nat {
  match e
  case Const(c) => c
  case Var(s) => if s in env.Keys then env[s] else 0
  case Node(op, args) => EvalList(args, op, env)
}

function EvalList(args: List<Expr>, op: Op,
                  env: map<string, nat>): nat
{
  match args
  case Nil =>
    (match op case Add => 0 case Mul => 1)
  case Cons(e, tail) =>
    var v0, v1 := Eval(e, env), EvalList(tail, op, env);
    match op
    case Add => v0 + v1
    case Mul => v0 * v1
}

function Substitute(e: Expr, n: string, c: nat): Expr
{
  match e
  case Const(_) => e
  case Var(s) => if s == n then Const(c) else e
  case Node(op, args) => Node(op, SubstituteList(args, n, c))
}

function SubstituteList(es: List<Expr>, n: string, c: nat): List<Expr>
{
  match es
  case Nil => Nil
  case Cons(e, tail) =>
    Cons(Substitute(e, n, c), SubstituteList(tail, n, c))
}

lemma EvalSubstitute(e: Expr, n: string, c: nat, env: map<string, nat>)
  ensures Eval(Substitute(e, n, c), env) == Eval(e, env[n := c])
{
  match e
  case Const(_) =>
  case Var(_) =>
  case Node(op, args) =>
    EvalSubstituteList(args, op, n, c, env);
}

lemma {:induction false} EvalSubstituteList(
    args: List<Expr>, op: Op, n: string, c: nat, env: map<string, nat>)
  ensures EvalList(SubstituteList(args, n, c), op, env)
       == EvalList(args, op, env[n := c])
{
  match args
  case Nil =>
  case Cons(e, tail) =>
    calc {
      EvalList(SubstituteList(args, n, c), op, env);
    ==  // args == Cons(e, tail)
      EvalList(SubstituteList(Cons(e, tail), n, c), op, env);
    ==  // def. SubstituteList
      EvalList(Cons(Substitute(e, n, c),
               SubstituteList(tail, n, c)), op, env);
    ==  // def. EvalList
      var v0, v1 :=
        Eval(Substitute(e, n, c), env),
        EvalList(SubstituteList(tail, n, c), op, env);
      match op
      case Add => v0 + v1
      case Mul => v0 * v1;
    ==  { EvalSubstitute(e, n, c, env); }
      var v0, v1 :=
        Eval(e, env[n := c]),
        EvalList(SubstituteList(tail, n, c), op, env);
      match op
      case Add => v0 + v1
      case Mul => v0 * v1;
    ==  { EvalSubstituteList(tail, op, n, c, env); }
      var v0, v1 :=
        Eval(e, env[n := c]),
        EvalList(tail, op, env[n := c]);
      match op
      case Add => v0 + v1
      case Mul => v0 * v1;
    ==  // def. EvalList
      EvalList(Cons(e, tail), op, env[n := c]);
    ==  // args == Cons(e, tail)
      EvalList(args, op, env[n := c]);
    }
}
