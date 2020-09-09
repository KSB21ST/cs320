package cs320
//20180109 김수빈
package object proj01 extends Project01 {

  def interp(e: Expr, env: Env): Value = e match{
    case Id(x: String) => env.getOrElse(x, error("error!"))
    case IntE(n: Int) => IntV(n)
    case BooleanE(b: Boolean) => BooleanV(b)
    case Add(l: Expr, r: Expr) => numAdd(interp(l, env), interp(r, env))
    case Mul(l: Expr, r: Expr) => numMul(interp(l, env), interp(r, env))
    case Div(l: Expr, r: Expr) => interp(r, env) match{
      case IntV(0) => error("error!")
      case _ => numDiv(interp(l, env), interp(r, env))
    }
    case Mod(l: Expr, r: Expr) => interp(r, env) match{
      case IntV(0) => error("error!")
      case _ => numMod(interp(l, env), interp(r, env))
    }
    case Eq(l: Expr, r: Expr) => numEq(interp(l, env), interp(r, env))
    case Lt(l: Expr, r: Expr) => numLt(interp(l, env), interp(r, env))
    case If(c: Expr, t: Expr, f: Expr) => interp(c, env) match{
      case BooleanV(true) => interp(t, env)
      case BooleanV(false) => interp(f, env)
      case _ => error("error!")
    }
    case TupleE(es: List[Expr]) => TupleV(es.map(interp(_, env)))
    case Proj(t: Expr, i: Int) => interp(t, env) match{
      case TupleV(v) => {
        if (v.length < i) error("error!")
        v(i-1)
      }
      case _ => error("error!")
    }
    case NilE => NilV
    case ConsE(h: Expr, t: Expr) => interp(t, env) match{
      case ConsV(a, b) => ConsV(interp(h, env), ConsV(a, b))
      case NilV => ConsV(interp(h, env), interp(t, env))
      case _ => error("error!")
    }
    case Empty(l: Expr) => interp(l, env) match {
      case NilV => BooleanV(true)
      case ConsV(a, b) => BooleanV(false)
      case _ => error("error!")
    }
    case Head(l: Expr) => interp(l, env) match{
      case ConsV(h, t) => h
      case _ => error("error!")
    }
    case Tail(l: Expr) => interp(l, env) match{
      case ConsV(h, t) => t
      case _ => error("error!")
    }
    case Val(x: String, e: Expr, b: Expr) => interp(b, env + (x -> interp(e, env)))
    case Fun(ps: List[String], b: Expr) => CloV(ps, b, env)
    case RecFuns(ds: List[FunDef], b: Expr) => {
      val funcs = ds.map({case FunDef(n, ps, b) => CloV(ps, b, env)})
      val prs = ds.map({case FunDef(n, ps, b) => n})
      val newev = env ++ (prs zip funcs)
      funcs.foreach(x=> x match{
        case CloV(ps, b, env) => x.env = newev
        case _ => error("error!")
        })
      interp(b, newev)
    }

    case App(f: Expr, as: List[Expr]) => interp(f, env) match {
      case CloV(params, b, fenv) => {
        val avals = as.map(interp(_, env))
        if (as.length != params.length) error("error!")
        interp(b, fenv ++ (params zip avals))
      }
      case _ => error("error!")
    }
    case Test(e: Expr, t: Type) => interp(e, env) match{
      case IntV(n) => t match{
        case IntT => BooleanV(true)
        case _ => BooleanV(false)
      }
      case BooleanV(b) => t match{
        case BooleanT => BooleanV(true)
        case _ => BooleanV(false)
      }
      case TupleV(vs) => t match{
        case TupleT => BooleanV(true)
        case _ => BooleanV(false)
      }
      case NilV => t match{
        case ListT => BooleanV(true)
        case _ => BooleanV(false)
      }
      case ConsV(h, h2) => t match{
        case ListT => BooleanV(true)
        case _ => BooleanV(false)
      }
      case CloV(ps, b, env) =>t match{
        case FunctionT => BooleanV(true)
        case _ => BooleanV(false)
      }
      case _ => error("error!")
    }
  }

  def numop(op: (Int, Int) => Int): (Value, Value) => Value= (_, _) match{
    case(IntV(x), IntV(y)) => IntV(op(x, y))
    case(x, y) => error("error!")
  }

  def relop(op: (Int, Int) => Boolean) : (Value, Value) => Value =(_, _) match{
    case(IntV(x), IntV(y)) => BooleanV(op(x, y))
    case(x, y) => error("error!")
  }

  val numAdd = numop(_+_)
  val numSub = numop(_-_)
  val numMul = numop(_*_)
  val numDiv = numop(_/_)
  val numMod = numop(_%_)
  val numEq = relop(_==_)
  val numLt = relop(_<_)
  val numNeq = relop(_!=_)
  val numLte = relop(_<=_)

  def tests: Unit = {
    // test-int
    test(run("42"), "42")
    // test-add
    test(run("1 + 2"), "3")
    test(run("2 + -2"), "0")
    test(run("val f ={x => x + 7};f(3) + 2"), "12")
    // test-sub
    test(run("7 - 2"), "5")
    // test-mul
    test(run("2 * 4"), "8")
    test(run("-2 * 0"), "0")
    // test-div
    test(run("5 / 2"), "2")
    test(run("5/-2"), "-2")
    test(run("2 % -3"), "2")
    // test-mod
    test(run("13 % 5"), "3")
    // test-neg
    test(run("1 - -1"), "2")

    // test-boolean
    test(run("true"), "true")
    test(run("false"), "false")
    // test-eq
    test(run("1 == 3 - 2"), "true")
    test(run("5 <= -2"), "false")
    test(run("5 != -2"), "true")
    // test-lt
    test(run("1 < 3 - 2"), "false")

    // test-tuple1
    test(run("(1, 2 + 3, true)"), "(1, 5, true)")
    // test-tuple2
    test(run("((42, 3 * 2), false)"), "((42, 6), false)")
    test(run("((1, 2, (1 +1, 2, 3 -1)), 3, (1, 2))"), "((1, 2, (2, 2, 2)), 3, (1, 2))")
    test(run("(3)"), "3")
    // test-proj1
    test(run("(1, 2 + 3, true)._1"), "1")
    // test-proj2
    test(run("((42, 3 * 2), false)._1._2"), "6")
    test(run("((1, 2, (1 +1, 2, 3 -1)), 3, (1, 2))._3._2"), "2")

    // test-nil
    test(run("Nil"), "Nil")
    // test-cons
    test(run("1 :: 1 + 1 :: Nil"), "(1 :: (2 :: Nil))")
    test(run("1:: 2 :: 3:: 4:: Nil"), "(1 :: (2 :: (3 :: (4 :: Nil))))")
    test(run("1::(1, 2)::Nil"), "(1 :: ((1, 2) :: Nil))")
    test(run("1::true::Nil"), "(1 :: (true :: Nil))")
    // test-isempty1
    test(run("Nil.isEmpty"), "true")
    test(run("(1::Nil).isEmpty"), "false")
    test(run("(1::(1, 2)::Nil).isEmpty"), "false")
    // test-isempty2
    test(run("(1 :: Nil).isEmpty"), "false")
    // test-head
    test(run("(1 :: Nil).head"), "1")
    // test-tail
    test(run("(1 :: Nil).tail"), "Nil")
    test(run("(1::2::Nil).tail"), "(2 :: Nil)")
    test(run("(1::2::3::Nil).tail"), "(2 :: (3 :: Nil))")
    test(run("(1 :: 2 :: Nil).tail.tail"), "Nil")
    // test-tail-head
    test(run("(1 :: 2 :: Nil).tail.head"), "2")
    test(run("(1::2::3::Nil).tail.head"), "2")
    test(run("(1::2::Nil).tail::3::Nil"), "((2 :: Nil) :: (3 :: Nil))")

    // test-local1
    test(run("""val x = 1 + 2;val y = x * 4 + 1;y / (x - 1) """), "6")
    // test-local2
    test(run("""val (x, y) = (1 + 2, 3 + 4);val z = x * y;val (a, b, c) = (z, z + z, z + z + z);c - b"""), "21")
    test(run("{ val f = { (x, y) => (x + y) }; f(1, 2) }"), "3")

    // test-fun
    test(run("x => x + x"), "<function>")
    test(run("(x, y)=> x + x*y"), "<function>")
    test(run("{x=>x+x}"), "<function>")
    test(run("val f ={x => x + 7};f"), "<function>")
    test(run("x => y => x + y"), "<function>")
    test(run("val f ={x => x + 7};f(3)"), "10")
    test(run("{ val g = { r => r._1 }; g((0, 12, 7))}"), "0")
    // test-app1
    test(run("(x => x + x)(1)"), "2")
    // test-app2
    test(run("(x => y => x + y)(1)(2)"), "3")
    // test-app3
    test(run("((x, y) => x + y)(1, 2)"), "3")
    test(run("def f(x, y) = x - 1;f(1, 2)"), "0")
    // test-type1
    test(run("1.isInstanceOf[Int]"), "true")
    // test-type2
    test(run("1.isInstanceOf[Boolean]"), "false")
    // test-type3
    test(run("(1 :: Nil).isInstanceOf[List]"), "true")
    test(run("Nil.isInstanceOf[List]"), "true")
    test(run("(1, 2).isInstanceOf[List]"), "false")
    test(run("Nil.isInstanceOf[Tuple]"), "false")
    test(run("(1, 2).isInstanceOf[Tuple]"), "true")
    // test-type4
    test(run("(x => x + x).isInstanceOf[Function]"), "true")
    test(run("(def f(x, y) = x - 1; f).isInstanceOf[Function]"), "true")
    test(run("(3).isInstanceOf[Int]"), "true")
    test(run("(3).isInstanceOf[List]"), "false")
    test(run("(3).isInstanceOf[Tuple]"), "false")

    // test-if
    test(run("if (true) 1 else 2"), "1")
    test(run("if (false) 3.tail else 3"), "3")
    // test-not
    test(run("!true"), "false")
    // test-and
    test(run("true && false"), "false")
    // test-or
    test(run("true || false"), "true")
    // test-neq
    test(run("1 != 2"), "true")
    // test-lte
    test(run("1 <= 1"), "true")
    // test-gt
    test(run("1 > 1"), "false")
    // test-gte
    test(run("1 >= 1"), "true")
    // test-nonempty
    test(run("Nil.nonEmpty"), "false")
    test(run("(1::Nil).nonEmpty"), "true")

    // test-rec1
    test(run("""
      def f(x) = x - 1;
      f(2)
    """), "1")
    // test-rec2
    test(run("""
      def f(x) = if (x < 1) 0 else x + f(x - 1);
      f(10)
    """), "55")
    test(run("""
      def f(x) = if (x < 1) 0 else g(x-1) + 3;
      def g(x) = if (x < 1) 0 else f(x-1) + 5;
      f(5)"""), "19")
    test(run("def f(x) = if (x < 1) 0 else x + f(x - 1);def g(x) = x - 1;f(g(10))"), "45")
    test(run("def f(x, y) = x*y - 1;def g(x) = 2*x ; f(1, g(2))"), "3")
    test(run("def f(x, y) = x*y - 1;def g() = 2 ; f(4, g())"), "7")
    test(run("def f () = 4 ;def g(x) = { val g = { x => (x + x) };g(x)}; def k(x) = 10; (g(1) + f()) - k(1)"), "-4")
    test(run("def f () = 4 ;def g(x) = { val g = { x => (x + x) };f()}; def k(x) = 10; (g(1) + f()) - k(1)"), "-2")
    test(run("(def f () = 4 ;def g(x) = { val g = { x => (x + x) };f()}; def k(x) = 10; (g(1) + f()) - k(1))==-2"), "true")
    test(run("def f(x) = if (x < 1) 0 else x + g(x - 1);def g(x) = f(x) - 1;f(g(3))"), "1")



    //test-Exercise05
    test(run("{ val f = { (a, b) => (a + b) }; { val g = { x => (x - 5) }; { val x = f(2, 5); g(x) } } }"), "2")
    test(run("{ val f = { (a, b) => (a + b) }; { val g = { x => (x - 5) }; { val x = f(g(3), 5); g(x) } } }"), "-2")
    test(run("{ val f = { (x, y) => (x + y) }; f(1, 2) }"), "3")
    test(run("{ val f = { () => 5 }; (f() + f()) }"), "10")
    test(run("{ val h = { (x, y, z, w) => (x + w) }; h(1, 4, 5, 6) }"), "7")
    test(run("{ val f = { () => 4 }; { val g = { x => (x + x) }; { val x = 10; ((x + f()) - g(4)) } } }"), "6")
    test(run("{ val x = 3; { val y = 5; (x, y)._1} }"), "3")

    //testExc
    testExc(run("def f(x, y) = x*y - 1;def g(x) = 2*f(x, y) ; f(1, g(2))"), "error!")
    testExc(run("true + 2"), "error!")
    testExc(run("2 - false"), "error!")
    testExc(run("5/0"), "error!")
    testExc(run("13 % 0"), "error!")
    testExc(run("true == false"), "error!")
    testExc(run("(1, 2).isInstanceOf[List] == false"), "error!")
    testExc(run("1::2"), "error!")
    testExc(run("1::0"), "error!")
    testExc(run("1::(1, 2)"), "error!")
    testExc(run("true.isEmpty"), "error!")
    testExc(run("Nil.head"), "error!")
    testExc(run("Nil.tail"), "error!")
    testExc(run("(true :: 2 :: Nil).head.tail"), "error!")
    testExc(run("Nil.tail.head"), "error!")
    testExc(run("(1, 2).head"), "error!")
    testExc(run("(1::(1, 2)).head"), "error!")
    testExc(run("f(x, y)"), "error!")
    testExc(run("1 && true"), "error!")
    testExc(run("true >= 3"), "error!")
    testExc(run("1::Nil.nonEmpty"), "error!")
    testExc(run("def f(x, y) = x*y - 1;def g(x) = 2*f(x, y) ; f(1, g(2))"), "error!")
    testExc(run("def f(x, y) = x*y - 1;def g() = 2 ; f(4, g(2))"), "error!")
    testExc(run("def f(x) = x - 1;def g(x) = 2*f(x) ; f(1, g())"), "error!")
    testExc(run("t1 == (def f(x, y) = x - 1; f).isInstanceOf[Function]"), "error!")
    testExc(run("x"), "error!")
    testExc(run("def f () = 4 ;def g() = { val g = { x => (x + x) };g(x)}; def k(x) = 10; (g() + f()) - k(1)"), "error!")
    testExc(run("def k () = 4 ;def g(x) = { val g = { x => (x + x) };g(x)}; def f(x) = 10; (g(1) + f()) - f(1)"), "error!")
    testExc(run("def f () = 4 ;def g() = { val g = { x => (x + x) };g(x)}; def k(x) = 10; ((g() + f()) - k(1)) "), "error!")
    testExc(run("(1, 2)._3"), "error!")
    testExc(run("(20-{x=>(x+x)})(17)"), "error!")
    testExc(run("(3)._1"), "error!")
  }
}
