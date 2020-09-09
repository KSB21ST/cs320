package cs320

package object ex06 extends Exercise06 {

  def interp(e: Expr, env: Env, sto: Sto): (Value, Sto) = ???

  def tests: Unit = {
    test(run("""{
                  b => {
                    b.set((2 + b.get));
                    b.set((3 + b.get));
                    b.set((4 + b.get));
                    b.get
                  }
                }(Box(1))"""), "10")
    testExc(run("{ x = 1 }.y"), "no such field")
    test(run("""{
                  r => {
                    { r.x = 5 };
                    r.x
                  }
                }({ x = 1 })"""), "5")
    test(run("42"), "42")
    test(run("{ x => x }"), "function")
    test(run("Box(1)"), "box")
    test(run("{}"), "record")

    /* Write your own tests */
  }
}
