package cs320

package object ex01 extends Exercise01 {

  def volumeOfCuboid(a: Int, b: Int, c: Int): Int = a*b*c
  def concat(x: String, y: String): String = x.concat(y)

  def addN(n: Int): Int => Int =
    (a : Int) => a + n
  def twice(f: Int => Int): Int => Int =
    (n : Int) => f(f(n))
  def compose(f: Int => Int, g: Int => Int): Int => Int =
    (n: Int) => f(g(n))

  def double(l: List[Int]): List[Int] = l.map(s=>s*2)
  def sum(l: List[Int]): Int = l.reduce((a: Int, b: Int)=>a+b)

  def getKey(m: Map[String, Int], s: String): Int = m.get(s) match{
    case Some(n) => n
    case None => error(s)
  }

  def countLeaves(t: Tree): Int = t match{
    case Leaf(n) => 1
    case Branch(a, b, c) => countLeaves(a) + countLeaves(c)
  }
  def flatten(t: Tree): List[Int] = t match{
    case Leaf(v) => List(v)
    case Branch(a, b, c) => flatten(a):::List(b):::flatten(c)
  }

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
