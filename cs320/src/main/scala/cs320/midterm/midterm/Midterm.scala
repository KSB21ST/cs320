package cs320

trait Midterm extends Homework {
  // Expressions
  trait Expr
  case class Num(num: Int) extends Expr
  case class Add(left: Expr, right: Expr) extends Expr
  case class Sub(left: Expr, right: Expr) extends Expr
  case class BooleanE(b: Boolean) extends Expr
  case class Eq(l: Expr, r: Expr) extends Expr
  case class Lt(l: Expr, r: Expr) extends Expr
  case class Id(name: String) extends Expr
  case class Fun(param: String, body: Expr) extends Expr
  case class App(fun: Expr, arg: Expr) extends Expr
  case class Set(field: String, expr: Expr) extends Expr
  case class While(c: Expr, b: Expr) extends Expr

  // environment
  type Addr = Int
  type Env = Map[String, Addr]
  type Sto = Map[Addr, Value]

  // value type
  sealed trait Value
  case class NumV(n: Int) extends Value
  case class CloV(param: String, body: Expr, env: Env) extends Value
  case class BooleanV(b: Boolean) extends Value
  case object NullV extends Value
}
