package cs320

package object proj02 extends Project02 {
  def lookup(x: String, env: Env): Value =
    env.getOrElse(x, error(s"lookup:$x"))

  def numop(op: (Int, Int) => Int): (Value, Value) => Value= (_, _) match{
    case(IntV(x), IntV(y)) => IntV(op(x, y))
    case(x, y) => error(s"numop1: $x, $y")
  }

  def numop2(op: (Int, Int) => Int): (Value, Value) => Value= (_, _) match{
    case(IntV(x), IntV(y)) =>
      if (y==0) error(s"numop2y0:$x")
      IntV(op(x, y))
    case(x, y) => error(s"numop2:$x, $y")
  }

  def relop(op: (Int, Int) => Boolean) : (Value, Value) => Value =(_, _) match{
    case(IntV(x), IntV(y)) => BooleanV(op(x, y))
    case(x, y) => error(s"relop: $x, $y")
  }


  val numVAdd = numop(_+_)
  val numVSub = numop(_-_)
  val numVMul = numop(_*_)
  val numVDiv = numop2(_/_)
  val numVMod = numop2(_%_)
  val numVEq = relop(_==_)
  val numVLt = relop(_<_)

  def interp(e: Expr, env: Env, k: Cont, ek: ECont): Value = e match{
    case Id(name: String) => k(lookup(name, env))
    case IntE(value: Int) => k(IntV(value))
    case BooleanE(value: Boolean) => k(BooleanV(value))
    case Add(left: Expr, right: Expr) =>
      interp(left, env, v1 =>interp(right, env, v2 =>k(numVAdd(v1, v2)), ek), ek)
    case Mul(left: Expr, right: Expr) =>
      interp(left, env, v1 =>interp(right, env, v2 =>k(numVMul(v1, v2)), ek), ek)
    case Div(left: Expr, right: Expr) =>
      interp(left, env, v1 =>interp(right, env, v2 =>k(numVDiv(v1, v2)), ek), ek)
    case Mod(left: Expr, right: Expr) =>
      interp(left, env, v1 =>interp(right, env, v2 =>k(numVMod(v1, v2)), ek), ek)
    case Eq(left: Expr, right: Expr) =>
      interp(left, env, v1 =>interp(right, env, v2 =>k(numVEq(v1, v2)), ek), ek)
    case Lt(left: Expr, right: Expr) =>
      interp(left, env, v1 =>interp(right, env, v2 =>k(numVLt(v1, v2)), ek), ek)
    case If(e1: Expr, e2: Expr, e3: Expr) =>
      interp(e1, env, v1 =>
        v1 match{
          case BooleanV(true) => interp(e2, env, v2 => k(v2), ek)
          case BooleanV(false) => interp(e3, env, v3 => k(v3), ek)
          case _ => error(s"If: $v1")
        }, ek)
    case TupleE(es: List[Expr]) =>
      k(interpMultiple(es, env, k, ek, v => TupleV(v), List[Value]()))
      //k(TupleV(es.map(interp(_, env, k, ek))))
    case Proj(e: Expr, i: Int) =>
      interp(e, env, v =>
        v match{
          case TupleV(vs) =>
            if (vs.length < i) error(s"projlength:$vs, $i")
            k(vs(i-1))
          case _ => error(s"proj: $v")
      }, ek)
    case NilE => k(NilV)
    case ConsE(head: Expr, tail: Expr) =>
      interp(head, env, v1 => interp(tail, env, v2 => v2 match{
        case NilV => k(ConsV(v1, NilV))
        case ConsV(h, t) => k(ConsV(v1, v2))
        case _ => error("error!")
      }, ek), ek)
    case Empty(e: Expr) =>
      interp(e, env, v =>
        v match{
          case NilV => k(BooleanV(true))
          case ConsV(h, t) => k(BooleanV(false))
          case _ => error("error!")
        }, ek)
    case Head(e: Expr) =>
      interp(e, env, v =>
        v match{
          case ConsV(h, t) => k(h)
          case _ => error(s"head: $v")
        }, ek)
    case Tail(e: Expr) =>
      interp(e, env, v =>
        v match{
          case ConsV(h, t) => k(t)
          case _ => error(s"tail: $v")
        }, ek)
    case Val(x: String, e1: Expr, e2: Expr) =>
      interp(e1, env, v1 => interp(e2, env + (x -> v1), v2 => k(v2), ek), ek)
    case Vcc(name: String, body: Expr) =>
      val t = ContV(k)
      val newenv = env + (name -> t)
      interp(body, newenv, v => k(v), ek)
      //interp(body, env + (name -> ContV(k)), v => k(v), ek)
    case Fun(parameters: List[String], body: Expr) => k(CloV(parameters, body, env))
    case RecFuns(ds: List[FunDef], body: Expr) =>
      val funcs = ds.map({case FunDef(n, ps, b) => CloV(ps, b, env)})
      val prs = ds.map({case FunDef(n, ps, b) => n})
      val newev = env ++ (prs zip funcs)
      funcs.foreach(x => x match{
        case CloV(ps, b, env) => x.env = newev
        case _ => error(s"Recfun: $x")
      })
      interp(body, newev, k, ek)
    case App(f: Expr, as: List[Expr]) =>
      interp(f, env, v => {
        interpMultiple(as, env, v => k(v), ek, v2 =>
          v match{
            case CloV(ps, b, fenv) =>
              val aval = v2
              if (as.length != ps.length) error("error!appclovlength")
              interp(b, fenv ++ (ps zip aval), v => k(v), ek)
            case ContV(v3) =>
              if(v2.length != 1) error("error appcontvlength")
              v3(v2(0))
            case _ => error(s"app: $v")
          }, List[Value]())
      }, ek)
    case Test(expression: Expr, t: Type) =>
      interp(expression, env, v =>
        v match{
          case IntV(n) => t match{
            case IntT => k(BooleanV(true))
            case _ => k(BooleanV(false))
          }
          case BooleanV(b) => t match{
            case BooleanT => k(BooleanV(true))
            case _ => k(BooleanV(false))
          }
          case TupleV(vs) => t match{
            case TupleT => k(BooleanV(true))
            case _ => k(BooleanV(false))
          }
          case NilV => t match{
            case ListT => k(BooleanV(true))
            case _ => k(BooleanV(false))
          }
          case ConsV(h, h2) => t match{
            case ListT => k(BooleanV(true))
            case _ => k(BooleanV(false))
          }
          case CloV(ps, b, env) => t match{
            case FunctionT => k(BooleanV(true))
            case _ => k(BooleanV(false))
          }
          case ContV(k) => t match{
            case FunctionT => k(BooleanV(true))
            case _ => k(BooleanV(false))
          }
          case _ => error("error!")
        }, ek)
    case Throw(e: Expr) => ek match{
      case None => interp(e, env, v => error(s"$v"), ek)//error(s"throw $e")
      case Some(n) =>
        interp(e, env, v => n(v), ek)
    }
    case Try(e1: Expr, e2: Expr) =>
      interp(e1, env, k, Option(t => interp(e2, env, v2 =>
          v2 match{
            case CloV(x, b, fenv) =>
              if(x.length != 1) error("trylength")
              interp(b, fenv + (x(0)->t), v => k(v), ek)
            case ContV(v3) =>
              v3(t)
            case _ => error(s"try:$v2")
          }, ek)))
  }

  def interpMultiple(es: List[Expr], env: Env, k: Cont, ek: ECont, es2: List[Value] => Value, es3: List[Value]): Value = {
    es match{
      case h :: t =>
        interp(h, env, v => interpMultiple(t, env, v => k(v), ek, es2, v :: es3), ek)
      case Nil => es2(es3.reverse)
    }
  }

  def tests: Unit = {
    // test-int
    test(run("42"), "42")
    // test-add
    test(run("1 + 2"), "3")
    // test-sub
    test(run("7 - 2"), "5")
    // test-mul
    test(run("2 * 4"), "8")
    // test-div
    test(run("5 / 2"), "2")
    // test-mod
    test(run("13 % 5"), "3")
    // test-neg
    test(run("1 - -1"), "2")

    // test-boolean
    test(run("true"), "true")
    // test-eq
    test(run("1 == 3 - 2"), "true")
    // test-lt
    test(run("1 < 3 - 2"), "false")

    // test-tuple1
    test(run("(1, 2 + 3, true)"), "(1, 5, true)")
    // test-tuple2
    test(run("((42, 3 * 2), false)"), "((42, 6), false)")
    // test-proj1
    test(run("(1, 2 + 3, true)._1"), "1")
    // test-proj2
    test(run("((42, 3 * 2), false)._1._2"), "6")

    // test-nil
    test(run("Nil"), "Nil")
    // test-cons
    test(run("1 :: 1 + 1 :: Nil"), "(1 :: (2 :: Nil))")
    // test-isempty1
    test(run("Nil.isEmpty"), "true")
    // test-isempty2
    test(run("(1 :: Nil).isEmpty"), "false")
    // test-head
    test(run("(1 :: Nil).head"), "1")
    // test-tail
    test(run("(1 :: Nil).tail"), "Nil")
    // test-tail-head
    test(run("(1 :: 2 :: Nil).tail.head"), "2")

    // test-val1
    test(run("""
      val x = 1 + 2;
      val y = x * 4 + 1;
      y / (x - 1)
    """), "6")
    //test-val2
    test(run("""
      val (x, y) = (1 + 2, 3 + 4);
      val z = x * y;
      val (a, b, c) = (z, z + z, z + z + z);
      c - b
    """), "21")
    test(run("val (x, y) = (3, 7); y - x"), "4")
    test(run("val (x, y) = (3, 7); (x, y)"), "(3, 7)")
    test(run("val (x, y) = (3, 7); y"), "7")

    // test-fun
    test(run("x => x + x"), "<function>")
    // test-app1
    test(run("(x => x + x)(1)"), "2")
    // test-app2
    test(run("(x => y => x + y)(1)(2)"), "3")
    // test-app3
    test(run("((x, y) => x + y)(1, 2)"), "3")

    // test-type1
    test(run("1.isInstanceOf[Int]"), "true")
    // test-type2
    test(run("1.isInstanceOf[Boolean]"), "false")
    // test-type3
    test(run("(1 :: Nil).isInstanceOf[List]"), "true")
    // test-type4
    test(run("(x => x + x).isInstanceOf[Function]"), "true")

    // test-if
    test(run("if (true) 1 else 2"), "1")
    // test-not
    test(run("!true"), "false")
    // test-and
    test(run("true && false"), "false")
    // test-or
    test(run("true || false"), "true")
    // test-neq
    test(run("1 != 2"), "true")
    test(run("1 == 2"), "false")
    // test-lte
    test(run("1 <= 1"), "true")
    test(run("val x1 = 1; val x2 = 1; x1 == x2"), "true")
    // test-gt
    test(run("1 > 1"), "false")
    // test-gte
    test(run("1 >= 1"), "true")
    // test-nonempty
    test(run("Nil.nonEmpty"), "false")

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
      def f(x) = if (x < 1) 0 else x + f(x - 1);
      f(1)
    """), "1")
    test(run("""
      def f(x) = 3;
      def g(x) = f(x) + x;
      g(1)
    """), "4")
    test(run("if (0 < 1) 0 else 3"), "0")
    test(run("""
      def f(x) = if (x < 1) 0 else f(x-1) + x;
      f(2)
    """), "3")
    // test-vcc1
    test(run("""
      vcc x;
      1 + x(1) + 1
    """), "1")
    // test-vcc2
    test(run("""
      (x => x * x)(
        1 + vcc x; 1 + x(2) + 3
      )
    """), "9")
    // test-return1
    test(run("(x => (return 1) + x)(2)"), "1")
    // test-return2
    test(run("""
      def div(x) = (x => 10 / x)(
        if (x == 0) return 0 else x
      );
      div(0) + div(10)
    """), "1")

    // test-throw1
    testExc(run("throw 1"), "")
    // test-throw2
    testExc(run("throw throw 1"), "")

    // test-try1
    test(run("""
      try {
        throw 1
      } catch (
        x => x + x
      )
    """), "2")
    // test-try2
    test(run("""
      1 + vcc x;
        try {
          throw 1
        } catch x
    """), "2")
    test(run("vcc x; {v => v + 1} + x(2) "), "2")
    test(run("vcc x; {v => v + 1} + x(2) "), "2")
    test(run("try {v => v + 1} + (throw 2)  catch x => x"), "2")
    test(run("vcc x; {v => v + 1} + x(2) "), "2")

    test(run("try 1::throw 4::throw 2 catch v=>v"), "2")
    test(run("try 1 :: (throw 4) :: (throw 2) catch x=>x"), "4")
    testExc(run("1::1"), "")
    testExc(run("1/0"), "")
    testExc(run("try{ throw 1 } catch ( 1 ) "), "")
    test(run("try{ 1} catch (1)"), "1")
    test(run("try { throw 1 } catch { x => x }"), "1")

    ///proj1///////////////////////////////////////////////////////////////
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
    testExc(run("def f(x, y) = x*y - 1;def g(x) = 2*f(x, y) ; f(1, g(2))"), "")
    testExc(run("true + 2"), "")
    testExc(run("2 - false"), "")
    testExc(run("5/0"), "")
    testExc(run("13 % 0"), "")
    testExc(run("true == false"), "")
    testExc(run("(1, 2).isInstanceOf[List] == false"), "")
    testExc(run("1::2"), "error!")
    testExc(run("1::0"), "error!")
    testExc(run("1::(1, 2)"), "error!")
    testExc(run("true.isEmpty"), "error!")
    testExc(run("Nil.head"), "")
    testExc(run("Nil.tail"), "")
    testExc(run("(true :: 2 :: Nil).head.tail"), "")
    testExc(run("Nil.tail.head"), "")
    testExc(run("(1, 2).head"), "")
    testExc(run("(1::(1, 2)).head"), "error!")
    testExc(run("f(x, y)"), "")
    testExc(run("1 && true"), "")
    testExc(run("true >= 3"), "")
    testExc(run("1::Nil.nonEmpty"), "error!")
    testExc(run("def f(x, y) = x*y - 1;def g(x) = 2*f(x, y) ; f(1, g(2))"), "")
    testExc(run("def f(x, y) = x*y - 1;def g() = 2 ; f(4, g(2))"), "error!")
    testExc(run("def f(x) = x - 1;def g(x) = 2*f(x) ; f(1, g())"), "error!")
    testExc(run("t1 == (def f(x, y) = x - 1; f).isInstanceOf[Function]"), "")
    testExc(run("x"), "")
    testExc(run("def f () = 4 ;def g() = { val g = { x => (x + x) };g(x)}; def k(x) = 10; (g() + f()) - k(1)"), "")
    testExc(run("def k () = 4 ;def g(x) = { val g = { x => (x + x) };g(x)}; def f(x) = 10; (g(1) + f()) - f(1)"), "")
    testExc(run("def f () = 4 ;def g() = { val g = { x => (x + x) };g(x)}; def k(x) = 10; ((g() + f()) - k(1)) "), "")
    testExc(run("(1, 2)._3"), "")
    testExc(run("(20-{x=>(x+x)})(17)"), "")
    testExc(run("(3)._1"), "")
  }
}
