package cs320

import scala.util.parsing.combinator._

trait Exercise05 extends Homework {
  // Expr type
  trait Expr
  case class Num(num: Int) extends Expr                               // e ::= n
  case class Add(left: Expr, right: Expr) extends Expr                //     | (e + e)
  case class Sub(left: Expr, right: Expr) extends Expr                //     | (e - e)
  case class Val(name: String, value: Expr, body: Expr) extends Expr  //     | {val x=e;e}
  case class Id(name: String) extends Expr                            //     | x
  case class App(func: Expr, args: List[Expr]) extends Expr           //     | e(e,...,e)
  case class Fun(params: List[String], body: Expr) extends Expr       //     | {(x,...,x)=>e}
  case class Rec(rec: Map[String, Expr]) extends Expr                 //     | {x=e,...,x=e}
  case class Acc(expr: Expr, name: String) extends Expr               //     | e.x

  // Record map
  type RecMap = Map[String, Value]

  // Value type
  trait Value
  case class NumV(n: Int) extends Value
  case class CloV(params: List[String], body: Expr, env: Env) extends Value
  case class RecV(map: RecMap) extends Value

  // Check duplicated string values in a given string list.
  def dupCheck(ss: List[String]): Boolean = ss.distinct.length != ss.length

  // Parser for Expr
  object Expr extends RegexParsers {
    def wrapC[T](rule: Parser[T]): Parser[T] = "{" ~> rule <~ "}"
    def wrapR[T](rule: Parser[T]): Parser[T] = "(" ~> rule <~ ")"
    lazy val int: Parser[Int] = """-?\d+""".r ^^ (_.toInt)
    val keywords = Set("val")
    lazy val str: Parser[String] =
      "[a-zA-Z_][a-zA-Z0-9_]*".r.withFilter(!keywords(_))

    lazy val expr: Parser[Expr] =
      e1 ~ rep(
        wrapR(repsep(expr, ",")) ^^ EApp |
        "." ~> str ^^ EAcc
      ) ^^ { case e ~ es => es.foldLeft(e){
        case (e, EApp(as)) => App(e, as)
        case (e, EAcc(f)) => Acc(e, f)
      }}
    lazy val e1: Parser[Expr] =
      int ^^ Num | str ^^ Id |
      wrapR((expr <~ "+") ~ expr) ^^ { case l ~ r => Add(l, r) } |
      wrapR((expr <~ "-") ~ expr) ^^ { case l ~ r => Sub(l, r) } |
      wrapC(("val" ~> str <~ "=") ~ (expr <~ ";") ~ expr) ^^
        { case x ~ i ~ b => Val(x, i, b) } |
      wrapC(str ~ ("=>" ~> expr)) ^^ { case p ~ b => Fun(p :: Nil, b) } |
      wrapC(wrapR(repsep(str, ",")) ~ ("=>" ~> expr)) ^^ {
        case ps ~ b =>
          if (dupCheck(ps)) error(s"bad syntax: duplicate parameters: $ps")
          Fun(ps, b)
      } |
      wrapC(repsep(str ~ ("=" ~> expr), ",")) ^^ (fs => {
        val l = fs.map{ case f ~ e => (f, e) }
        val ns = l.map(_._1)
        if (dupCheck(ns)) error(s"duplicate fields: $ns")
        Rec(l.toMap)
      })

    sealed trait E
    case class EApp(as: List[Expr]) extends E
    case class EAcc(f: String) extends E
      
    def apply(str: String): Expr =
      parseAll(expr, str).getOrElse(error(s"bad syntax: $str"))
  }

  // Environment
  type Env = Map[String, Value]

  def interp(expr: Expr, env: Env): Value

  // Evaluate a Expr program contained in a string
  def run(str: String): String = interp(Expr(str), Map.empty) match {
    case NumV(n) => n.toString
    case _: CloV => "function"
    case _: RecV => "record"
  }
}
