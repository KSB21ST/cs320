package cs320

package object ex02 extends Exercise02 {
  // Problem 1
  def freeIds(expr: Expr): Set[String] = expr match{
    case Num(a) => Set()
    case Add(a, b) => freeIds(a) ++ freeIds(b)
    case Sub(a, b) => freeIds(a) ++ freeIds(b)
    case Val(a, b, c) => freeIds(c) diff Set(a)
    case Id(a) => Set(a)
  }

  // Problem 2
  def bindingIds(expr: Expr): Set[String] = expr match{
    case Num(a) => Set()
    case Add(a, b) => Set()
    case Sub(a, b) => Set()
    case Val(a, b, c) => Set(a)
    case Id(a) => Set()
  }

  // Problem 3
  def boundIds(expr: Expr): Set[String] = expr match{
    case Num(a) => Set()
    case Add(a, b) => boundIds(a) ++ boundIds(b)
    case Sub(a, b) => boundIds(a) ++ boundIds(b)
    case Val(a, b, c) =>
      if(boundIds(c)(a)) Set(a)
      else Set()
    case Id(a) => Set(a)
  }

  // Tests
  def tests: Unit = {
    test(freeIds(Expr("{ val x = 1; (x + y) }")), Set("y"))
    test(freeIds(Expr("{ val z = 2; 1 }")), Set())
    test(bindingIds(Expr("{ val x = 1; (x + y) }")), Set("x"))
    test(bindingIds(Expr("{ val z = 2; 1 }")), Set("z"))
    test(boundIds(Expr("{ val x = 1; (x + y) }")), Set("x"))
    test(boundIds(Expr("{ val z = 2; 1 }")), Set())

    /* Write your own tests */
  }
}
