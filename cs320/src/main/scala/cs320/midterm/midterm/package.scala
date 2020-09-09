package cs320

package object midterm extends Midterm {
  def numVop(op: (Int, Int) => Int): (Value, Value) => NumV = (_, _) match {
    case (NumV(x), NumV(y)) => NumV(op(x, y))
    case (x, y) => error(s"not both numbers: $x, $y")
  }
  val numVAdd = numVop(_ + _)
  val numVSub = numVop(_ - _)

  def relop(op: (Int, Int) => Boolean) : (Value, Value) => Value =(_, _) match{
    case(NumV(x), NumV(y)) => BooleanV(op(x, y))
    case(x, y) => error("error!")
  }
  val numEq = relop(_==_)
  val numLt = relop(_<_)

  def lookup(x: String, env: Env): Addr =
    env.getOrElse(x, throw new Exception)

  def storeLookup(a: Addr, sto: Sto): Value =
    sto.getOrElse(a, throw new Exception)

  def malloc(sto: Sto): Addr = (-1 :: sto.keys.toList).max + 1

  def interp(e: Expr, env: Env, sto: Sto): (Value, Sto) = e match{
    case Num(n) => (NumV(n), sto)
    case BooleanE(b: Boolean) => (BooleanV(b), sto)
    case Eq(l: Expr, r: Expr) =>
      val (lv, ls) = interp(l, env, sto)
      val (rv, rs) = interp(r, env, ls)
      (numEq(lv, rv), rs)
    case Lt(l: Expr, r: Expr) =>
      val (lv, ls) = interp(l, env, sto)
      val (rv, rs) = interp(r, env, ls)
      (numLt(lv, rv), rs)
    case Add(l, r) =>
      val (lv, ls) = interp(l, env, sto)
      val (rv, rs) = interp(r, env, ls)
      (numVAdd(lv, rv), rs)
    case Sub(l, r) =>
      val (lv, ls) = interp(l, env, sto)
      val (rv, rs) = interp(r, env, ls)
      (numVSub(lv, rv), rs)
    case Id(x) => (storeLookup(lookup(x, env), sto), sto)
    case Fun(p, b) =>
      val cloV = CloV(p, b, env)
      (cloV, sto)
    case App(f, a) =>
      val (CloV(x, b, fEnv), ls) = interp(f, env, sto)
      val (v, rs) = interp(a, env, ls)
      val addr = malloc(rs)
      interp(b, fEnv + (x -> addr), rs + (addr -> v))
    case Set(x, e) =>
      val(v, s) = interp(e, env, sto)
      (v, s + (lookup(x, env) -> v))
    case While(c, b) => interp(c, env, sto) match {
      case (b2, s) => b2 match{
        case BooleanV(true) =>
          val (bs, bsto) = interp(b, env, s)
          interp(While(c, b), env, bsto)
        case BooleanV(false) => (NullV, s)
        case _ => error("error!")
      }}
    }

  def tests: Unit = {
    test(interp(Num(1), Map.empty, Map.empty), (NumV(1), Map.empty))
    test(interp(BooleanE(true), Map.empty, Map.empty), (BooleanV(true), Map.empty))
    test(interp(Eq(Num(1), Num(2)), Map.empty, Map.empty), (BooleanV(false), Map.empty))
    test(interp(Lt(Num(1), Num(2)), Map.empty, Map.empty), (BooleanV(true), Map.empty))
    test(interp(Add(Num(1), Num(2)), Map.empty, Map.empty), (NumV(3), Map.empty))
    test(interp(App(Fun("x", Add(Add(Id("x"), Set("x", Num(1))), Id("x"))), Num(0)), Map.empty, Map.empty), (NumV(2), Map(0->NumV(1))))
    //test case 1
    test(interp(App(Fun("x", While(Lt(Id("x"), Num(3)), Set("x", Add(Id("x"), Num(2))))), Num(0)), Map.empty, Map.empty), (NullV, Map(0->NumV(4))))
    //test case 2
    test(interp(While(Lt(Num(5), Num(4)), Num(3)), Map.empty, Map.empty), (NullV, Map.empty))
    //test case3
    test(interp(
      App(
        Fun("x",
           While(Lt(Num(0), Id("x")),
             Set("x", Sub(Id("x"), Num(1)))
           )
         ), Num(5)), Map.empty, Map.empty), (NullV, Map(0->NumV(0))))
  }
}
