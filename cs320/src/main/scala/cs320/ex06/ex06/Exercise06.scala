package cs320

import scala.util.parsing.combinator._
import scala.collection.immutable.{Set => ISet}

trait Exercise06 extends Homework {
  // Expr type
  trait Expr
  case class Num(num: Int) extends Expr                                // e ::= n
  case class Add(left: Expr, right: Expr) extends Expr                 //     | (e+e)
  case class Sub(left: Expr, right: Expr) extends Expr                 //     | (e-e)
  case class Id(name: String) extends Expr                             //     | x
  case class Fun(param: String, body: Expr) extends Expr               //     | {x=>e}
  case class App(fun: Expr, arg: Expr) extends Expr                    //     | e(e)
  case class NewBox(expr: Expr) extends Expr                           //     | Box(e)
  case class SetBox(box: Expr, expr: Expr) extends Expr                //     | e.set(e)
  case class OpenBox(box: Expr) extends Expr                           //     | e.get
  case class Seqn(left: Expr, right: List[Expr]) extends Expr          //     | {e;...;e}
  case class Rec(fields: List[(String, Expr)]) extends Expr            //     | {x=e,...,x=e}
  case class Get(record: Expr, field: String) extends Expr             //     | e.x
  case class Set(record: Expr, field: String, expr: Expr) extends Expr //     | {e.x=e}

  // environment
  type Addr = Int
  type Env = Map[String, Value]
  type Sto = Map[Addr, Value]

  // value type
  trait Value
  case class NumV(n: Int) extends Value
  case class CloV(param: String, body: Expr, env: Env) extends Value
  case class BoxV(addr: Addr) extends Value
  case class RecV(fields: Map[String, Addr]) extends Value

  // Check duplicated string values in a given string list.
  def dupCheck(ss: List[String]): Boolean = ss.distinct.length != ss.length

  // Parser for Expr
  object Expr extends RegexParsers {
    def wrapC[T](rule: Parser[T]): Parser[T] = "{" ~> rule <~ "}"
    def wrapR[T](rule: Parser[T]): Parser[T] = "(" ~> rule <~ ")"
    lazy val int: Parser[Int] = """-?\d+""".r ^^ (_.toInt)
    val keywords = ISet("val", "Box", "set", "get")
    lazy val str: Parser[String] =
      "[a-zA-Z_][a-zA-Z0-9_]*".r.withFilter(!keywords(_))

    lazy val expr: Parser[Expr] =
      e1 ~ rep(
        wrapR(expr) ^^ EApp |
        "." ~> "set" ~> wrapR(expr) ^^ ESetBox |
        "." ~ "get" ^^^ EOpenBox |
        "." ~> str ^^ EGet
      ) ^^ { case e ~ es => es.foldLeft(e){
        case (e, EApp(a)) => App(e, a)
        case (e, ESetBox(a)) => SetBox(e, a)
        case (e, EOpenBox) => OpenBox(e)
        case (e, EGet(f)) => Get(e, f)
      }}
    lazy val e1: Parser[Expr] =
      "Box" ~> wrapR(expr) ^^ NewBox | int ^^ Num | str ^^ Id |
      wrapR((expr <~ "+") ~ expr) ^^ { case l ~ r => Add(l, r) } |
      wrapR((expr <~ "-") ~ expr) ^^ { case l ~ r => Sub(l, r) } |
      wrapC(str ~ ("=>" ~> expr)) ^^ { case p ~ b => Fun(p, b) } |
      wrapC(rep1sep(expr, ";")) ^^ {
        case Nil => error("Seqn cannot be empty")
        case l :: r => Seqn(l, r)
      } |
      wrapC(repsep(str ~ ("=" ~> expr), ",")) ^^ (fs => {
        val l = fs.map{ case f ~ e => (f, e) }
        val ns = l.map(_._1)
        if (dupCheck(ns)) error(s"duplicate fields: $ns")
        Rec(l)
      }) |
      wrapC(rExpr ~ ("=" ~> expr)) ^^ { case (r, f) ~ e => Set(r, f, e) }
    lazy val rExpr: Parser[(Expr, String)] =
      expr ^? { case Get(e, f) => (e, f) }

    sealed trait E
    case class EApp(a: Expr) extends E
    case class ESetBox(e: Expr) extends E
    case object EOpenBox extends E
    case class EGet(f: String) extends E

    def apply(str: String): Expr = parseAll(expr, str).getOrElse(error(s"bad syntax: $str"))
  }

  // Evaluate a Expr program contained in a string
  def run(str: String): String =
    interp(Expr(str), Map.empty, Map.empty)._1 match {
      case NumV(n) => n.toString
      case _: CloV => "function"
      case _: BoxV => "box"
      case _: RecV => "record"
    }

  // interpreter
  def interp(e: Expr, env: Env, sto: Sto): (Value, Sto)
}
