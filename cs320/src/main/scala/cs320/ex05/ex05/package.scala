package cs320

package object ex05 extends Exercise05 {

  def numop(op:(Int, Int) => Int): (Value, Value) => Value = (_, _) match{
    case(NumV(x), NumV(y)) => NumV(op(x, y))
    case _ => error("error!")
  }

  val numAdd = numop(_+_)
  val numSub = numop(_-_)

  def interp(expr: Expr, env: Env): Value =  expr match{
    case Num(num) => NumV(num)
    case Add(left, right) => numAdd(interp(left, env), interp(right, env))
    case Sub(left, right) => numSub(interp(left, env), interp(right, env))
    case Val(name, value, body) => interp(body, env + (name -> interp(value, env)))
    case Id(name) => env.getOrElse(name, error("error!"))
    case App(func, args) => interp(func, env) match{
      case CloV(params, b, fenv) =>{
        val avals = args.map(interp(_, env))
        if(params.length != avals.length) error("wrong arity")
        interp(b, fenv ++ (params zip avals))
      }
      case _ => error("error!")
    }
    case Fun(params, body) => CloV(params, body, env)
    case Rec(rec) => RecV(rec.mapValues(interp(_ , env)))
    case Acc(e, n) => interp(e, env) match{
      case RecV(map) => map.getOrElse(n, error("no such field!"))
      case _ => error("error!")
    }

  }

  def tests: Unit = {
    test(run("{ (x, y) => (x + y) }(1, 2)"), "3")
    //testExc(run("{ (x, y) => (x + y) }(1, 2)"), "2")
    test(run("{ () => (3 + 4) }()"), "7")
    testExc(run("{ (x, y) => (x + y) }(1)"), "wrong arity")
    test(run("{ x = 1, y = 2 }.x"), "1")
    testExc(run("{ x = 1, y = 2 }.z"), "no such field")
    testExc(run("{ x = { y = 1 }.z }"), "no such field")
    test(run("42"), "42")
    test(run("{ x => x }"), "function")
    test(run("{ x = 1 }"), "record")
    test(run("{ a = 10, b = (1 + 2) }"), "record")
    test(run("{ a = 10, b = (1 + 2) }.b"), "3")
    test(run("{ val g = { r => r.c }; g({ a = 0, c = 12, b = 7 }) }"), "12")
    test(run("{ r = { z = 0 } }.r"), "record")
    test(run("{ r = { z = 0 } }.r.z"), "0")
    test(run("{ val f = { (a, b) => (a + b) }; { val g = { x => (x - 5) }; { val x = f(2, 5); g(x) } } }"), "2")
    test(run("{ val f = { (x, y) => (x + y) }; f(1, 2) }"), "3")
    test(run("{ val f = { () => 5 }; (f() + f()) }"), "10")
    test(run("{ val h = { (x, y, z, w) => (x + w) }; h(1, 4, 5, 6) }"), "7")
    test(run("{ val f = { () => 4 }; { val g = { x => (x + x) }; { val x = 10; ((x + f()) - g(4)) } } }"), "6")
    test(run("{ a = 10, b = (1 + 2) }"), "record")
    test(run("{ val x = 3; { val y = 5; { a = x, b = y }.a } }"), "3")
    test(run("{ val f = { (a, b) => (a.a + b) }; { val g = { x => (5 + x) }; { val x = f({ a = 10, b = 5 }, 2); g(x) } } }"), "17")
    test(run("{ val f = { (a, b, c, d, e) => { a = a, b = b, c = c, d = d, e = e } }; f(1, 2, 3, 4, 5).c }"), "3")
    test(run("{ val f = { (a, b, c) => { a = a, b = b, c = c } }; f(1, 2, 3).b }"), "2")
    test(run("{ val f = { (a, b, c) => { x = a, y = b, z = c, d = 2, e = 3 } }; f(1, 2, 3).y }"), "2")
    test(run("{ val f = { (a, b, c) => { x = a, y = b, z = c, d = 2, e = 3 } }; f(1, 2, 3).d }"), "2")
    test(run("{ val f = { x => (5 + x) }; f({ a = { a = 10, b = (5 - 2) }, b = { x = 50 }.x }.a.b) }"), "8")
    test(run("{ a = 10 }"), "record")
    test(run("{ a = 10 }.a"), "10")
    test(run("{ a = (1 + 2) }.a"), "3")
    test(run("{ x => x }"), "function")
    test(run("{ a = { b = 10 } }.a"), "record")
    test(run("{ a = { a = 10 } }.a.a"), "10")
    test(run("{ a = { a = 10, b = 20 } }.a.a"), "10")
    test(run("{ a = { a = 10, b = 20 } }.a.b"), "20")
    test(run("({ a = 10 }.a + { a = 20 }.a)"), "30")
    test(run("{ a = (2 - 1) }"), "record")
    test(run("{ a = (2 - 1) }.a"), "1")
    test(run("{ val y = { x = 1, y = 2, z = 3 }; y.y }"), "2")
    test(run("{ val y = { x = 1, y = 2, z = 3 }; y.z }"), "3")
    test(run("{ val g = { r => r.c }; g({ a = 0, c = 12, b = 7 }) }"), "12")
    testExc(run("{ a = 10 }.b"), "no such field")
    testExc(run("{ z = { z = 0 }.y }"), "no such field")

    /* Write your own tests */
  }
}
