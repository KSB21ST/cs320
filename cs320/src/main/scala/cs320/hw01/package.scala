package cs320

package object hw01 extends Homework01 {
  // 1. Primitives (20 pts)
  def volumeOfCuboid(a: Int, b: Int, c: Int) : Int = {a*b*c}
  def concat(x: String, y: String) : String = {x.concat(y)}

  // 2. Function Values (30 pts)
  def addN(n: Int): Int => Int =
    (a: Int) => a + n
  def twice(f: Int => Int): Int => Int =
    (n: Int) => f(f(n))
  def compose(f: Int => Int, g: Int => Int): Int => Int =
    (n: Int) => f(g(n))

  // 3. Data Structures (50 pts)
  // 3.1. Lists (20 pts)
  def double(l: List[Int]): List[Int] = {l.map(_*2)}
  def sum(l: List[Int]): Int =  {l.reduce((a: Int, b: Int)=>a+b)}

  // 3.2. Maps (10 pts)
  def getKey(m: Map[String, Int], s: String): Int = ???
  // 3.3. User-defined Structures (20 pts)
  def countLeaves(t: Tree): Int = ???
  def flatten(t: Tree): List[Int] = ???

  def tests: Unit = {
    test(concat("abc", "def"), "abcdef")
    test(addN(5)(3), 8)
    test(addN(5)(42), 47)
    test(twice(addN(3))(2), 8)
    test(twice(addN(3))(7), 13)
    test(compose(addN(3), addN(4))(5), 12)
    test(compose(addN(3), addN(4))(11), 18)

    val l: List[Int] = List(1, 2, 3)
    test(double(l), List(2, 4, 6))
    test(double(double(l)), List(4, 8, 12))

    test(sum(List(1,2,3)), 6)
    test(sum(List(4,2,3,7,5)), 21)

    val m: Map[String, Int] = Map("Ryu" -> 42, "PL" -> 37)
    test(getKey(m, "Ryu"), 42)
    test(getKey(m, "PL"), 37)
    testExc(getKey(m, "CS320"), "CS320")

    val tree: Tree = Branch(Leaf(1), 2, Branch(Leaf(3), 4, Leaf(5)))
    test(countLeaves(tree), 3)
    test(flatten(tree), List(1, 2, 3, 4, 5))

    /* Write your own tests */
  }
}
