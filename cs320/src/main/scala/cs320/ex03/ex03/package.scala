package cs320

import cs320._

package object ex03 extends Exercise03 {
  // applies a binary numeric function on all combinations of numbers from
  // the two input lists, and return the list of all of the results
  def binOp(
    op: (Int, Int) => Int,
    ls: List[Int],
    rs: List[Int]
  ): List[Int] = ls match {
    case Nil => Nil
    case l :: rest =>
      def f(r: Int): Int = op(l, r)
      rs.map(f) ++ binOp(op, rest, rs)
  }

  def interp(expr: Expr, env: Env): List[Int] = expr match{
    case Num(nums) => nums
    case Add(left, right) => binOp((x, y) => x+y, interp(left, env), interp(right, env))
    case Sub(left, right) => binOp((x, y)=> x-y, interp(left, env), interp(right, env))
    case Val(name, expr, body) => interp(body, env + (name -> interp(expr, env)))
    case Id(id: String) => env.getOrElse(id, error(s"free identifier: $id"))
    case Min(left, mid, right) => binOp((x, y)=>x.min(y), binOp((x, y)=>x.min(y), interp(left, env), interp(mid, env)), interp(right, env))
    case Max(left, mid, right) => binOp((x, y)=>x.max(y), binOp((x, y)=>x.max(y), interp(left, env), interp(mid, env)), interp(right, env))
  }

  def tests: Unit = {
    test(run("(3 + 7)"), List(10))
    test(run("(10 - (3, 5))"), List(7, 5))
    test(run("{ val x = (5 + 5); (x + x) }"), List(20))
    test(run("min(3, 4, 5)"), List(3))
    test(run("max((1 + 2), 4, 5)"), List(5))
    test(run("min((1, 4), (2, 9), 3)"), List(1, 1, 2, 3))
    test(run("max((1, 6), (2, 5), (3, 4))"), List(3, 4, 5, 5, 6, 6, 6, 6))

    /* Write your own tests */
  }
}
