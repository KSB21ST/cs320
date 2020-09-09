package cs320

import scala.util.parsing.combinator._

trait Exercise02 extends Homework {
  // Expressions
  trait Expr
  case class Num(num: Int) extends Expr                             // e ::= n
  case class Add(left: Expr, right: Expr) extends Expr              //     | (e + e)
  case class Sub(left: Expr, right: Expr) extends Expr              //     | (e - e)
  case class Val(name: String, expr: Expr, body: Expr) extends Expr //     | {val x = e; e}
  case class Id(id: String) extends Expr                            //     | x

  // Parser for Expr
  object Expr extends RegexParsers {
    def wrapC[T](rule: Parser[T]): Parser[T] = "{" ~> rule <~ "}"
    def wrapR[T](rule: Parser[T]): Parser[T] = "(" ~> rule <~ ")"
    lazy val int: Parser[Int] = """-?\d+""".r ^^ (_.toInt)
    lazy val str: Parser[String] =
    "[a-zA-Z_][a-zA-Z0-9_]*".r.withFilter(_ != "val")
    lazy val expr: Parser[Expr] =
      int                         ^^ { case n => Num(n) }        |
      wrapR((expr <~ "+") ~ expr) ^^ { case l ~ r => Add(l, r) } |
      wrapR((expr <~ "-") ~ expr) ^^ { case l ~ r => Sub(l, r) } |
      wrapC(("val" ~> str <~ "=") ~ (expr <~ ";") ~ expr) ^^
                              { case x ~ i ~ b => Val(x, i, b) } |
      str                         ^^ { case x => Id(x)         }
    def apply(str: String): Expr =
      parseAll(expr, str).getOrElse(error(s"bad syntax: $str"))
  }

  // Problem 1
  def freeIds(expr: Expr): Set[String]

  // Problem 2
  def bindingIds(expr: Expr): Set[String]

  // Problem 3
  def boundIds(expr: Expr): Set[String]

  // Tests
  def tests: Unit
}
