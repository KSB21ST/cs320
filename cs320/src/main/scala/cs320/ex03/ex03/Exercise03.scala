package cs320

import scala.util.parsing.combinator._

trait Exercise03 extends Homework {
  // Expressions
  trait Expr
  case class Num(nums: List[Int]) extends Expr                       // e ::= n | (n, ..., n)
  case class Add(left: Expr, right: Expr) extends Expr               //     | (e + e)
  case class Sub(left: Expr, right: Expr) extends Expr               //     | (e - e)
  case class Val(name: String, expr: Expr, body: Expr) extends Expr  //     | {val x = e; e}
  case class Id(id: String) extends Expr                             //     | x
  case class Min(left: Expr, mid: Expr, right: Expr) extends Expr    //     | min(e, e, e)
  case class Max(left: Expr, mid: Expr, right: Expr) extends Expr    //     | max(e, e, e)

  // Parser for Expr
  object Expr extends RegexParsers {
    def wrapC[T](rule: Parser[T]): Parser[T] = "{" ~> rule <~ "}"
    def wrapR[T](rule: Parser[T]): Parser[T] = "(" ~> rule <~ ")"
    lazy val int: Parser[Int] = """-?\d+""".r ^^ (_.toInt)
    val keywords = Set("val", "min", "max")
    lazy val str: Parser[String] =
    "[a-zA-Z_][a-zA-Z0-9_]*".r.withFilter(!keywords.contains(_))
    lazy val expr: Parser[Expr] =
      int                         ^^ (n => Num(List(n)))         |
      wrapR(repsep(int, ","))     ^^ Num                         |
      wrapR((expr <~ "+") ~ expr) ^^ { case l ~ r => Add(l, r) } |
      wrapR((expr <~ "-") ~ expr) ^^ { case l ~ r => Sub(l, r) } |
      wrapC(("val" ~> str <~ "=") ~ (expr <~ ";") ~ expr) ^^
                                     { case x ~ i ~ b => Val(x, i, b) } |
      "min" ~> wrapR(expr ~ ("," ~> expr <~ ",") ~ expr) ^^
                                     { case l ~ m ~ r => Min(l, m, r) } |
      "max" ~> wrapR(expr ~ ("," ~> expr <~ ",") ~ expr) ^^
                                     { case l ~ m ~ r => Max(l, m, r) } |
      str ^^ Id
    def apply(str: String): Expr =
      parseAll(expr, str).getOrElse(error(s"bad syntax: $str"))
  }

  type Env = Map[String, List[Int]]
  def interp(expr: Expr, env: Env): List[Int]
  def run(str: String): List[Int] = interp(Expr(str), Map.empty)
}
