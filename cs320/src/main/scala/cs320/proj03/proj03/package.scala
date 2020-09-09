package cs320

package object proj03 extends Project03 {

  def typeCheck(e: Typed.Expr): Typed.Type = T.typeCheck(e)
  def interp(e: Untyped.Expr): Untyped.Value = U.interp(e)

  object T {
    import Typed._
    case class TEnv(
      tid: Map[String, ((List[String], Type), Boolean)] = Map(), //Boolean represents mutability tag
      tbinds: Map[String, RecDef] = Map(),
      tvar: Set[String] = Set() //type variables
    ){
      def +(t: String, a: ((List[String], Type), Boolean)) : TEnv =
        TEnv(tid + (t -> a), tbinds, tvar)
      def +(x: String, t: RecDef ) : TEnv =
        TEnv(tid, tbinds + (x -> t), tvar)
      def contains(x: String) : Boolean =
        tid.contains(x) || tbinds.contains(x) || tvar.contains(x)
    }

    def tcc(e1: TEnv, e2: TEnv): TEnv =
      TEnv(e1.tid.++(e2.tid), e1.tbinds.++(e2.tbinds), e1.tvar ++ e2.tvar)

    def subst(tbody: Type, as: List[String], ts: List[Type]) : Type = tbody match{ //t는 typebody, a는 alpha, t2는 argument for alpha
      case AppT(n: String, targs: List[Type]) => AppT(n, targs.map(subst(_, as, ts)))
      case VarT(n: String) =>
        val t = (as zip ts).toMap
        if(t.contains(n))
         t.getOrElse(n, error(s"subst, varT:$tbody"))
        else tbody
      case IntT => tbody
      case BooleanT => tbody
      case UnitT => tbody
      case ArrowT(p, r) => ArrowT(p.map(subst(_, as, ts)), subst(r, as, ts))
    }

    def valid(t: Type, env: TEnv): Type = t match{
      case AppT(n: String, tar: List[Type]) =>
        tar.foreach(valid(_, env))
        if(!env.tbinds.contains(n)) error(s"validtype, appt: $t")
        env.tbinds(n) match{
          case TypeDef(n, tpar, vars) =>
            if(tpar.length != tar.length) error(s"validtype, appt") else t
          case _ => error(s"validtype, appt: $t")
        }
      case VarT(n: String) =>
        if(env.tvar.contains(n)) t
        else error(s"validtype, vart: $t")
      case IntT => t
      case BooleanT => t
      case UnitT => t
      case ArrowT(p: List[Type], r: Type) =>
        p.foreach(valid(_, env))
        valid(r, env)
        t
      case _ => error(s"validtype, else: $t")
    }

    def validrec(t: RecDef, env: TEnv): RecDef = t match{
      case Lazy(n: String, t2: Type, e: Expr) =>
        valid(t2, env)
        thp(e, env)
        t
      case RecFun(n: String, tps: List[String],
        ps: List[(String, Type)], rt: Type, b: Expr) =>
        tps.foreach(x =>if(env.contains(x)) error(s"validrec, recfun: $t"))
        val newev = TEnv(env.tid, env.tbinds, env.tvar ++ tps)
        ps.foreach({case(x, x2) => valid(x2, newev)})
        valid(rt, newev)
        val newev2 = TEnv(newev.tid ++ ps.map({case(x, x2) => (x, ((List(), x2), true))}), newev.tbinds, newev.tvar)
        ms(rt, thp(b, newev2))
        t
      case TypeDef(n: String, ps: List[String], vars: List[Variant]) =>
        ps.foreach(x =>if(env.contains(x)) error(s"validrec, typdef: $t"))
        val newev = TEnv(env.tid, env.tbinds, env.tvar ++ ps)
        vars.foreach({case Variant(n, vps) => vps.foreach(valid(_, newev))})
        t
      case _ => error(s"validrec, else: $t")
    }

    def ms(t1: Type, t2: Type): Type = (t1, t2) match{
      case(AppT(n1, targ1), AppT(n2, targ2)) =>
        if(n1 != n2) error(s"ms, appT: $t1")
        val temp = targ1.zip(targ2)
        temp.foreach({case(x1, x2) => ms(x1, x2)})
        t1
      case(VarT(n1), VarT(n2)) =>
        if(n1 == n2) t1 else error(s"ms, varT: $t1")
      case(IntT, IntT) => t1
      case(BooleanT, BooleanT) => t1
      case(UnitT, UnitT) => t1
      case(ArrowT(p1, r1), ArrowT(p2, r2)) =>
        val temp = p1.zip(p2)
        temp.foreach({case (x1, x2) => ms(x1, x2)})
        ms(r1, r2)
        t1
      case _ => error(s"ms, else: $t1")
    }

    def addup(s: List[RecDef], env: TEnv): TEnv = s match{
      case h::t => addup(t, tcc(env, rec_env(h)))
      case Nil => env
    }

    def rec_env(d: RecDef): TEnv = d match{
      case TypeDef(n, ps, vs) =>
        val newev = TEnv() + (n, d)
        // hr_d2(vs, ps, n, newev)
        val temp = vs.map({
          case Variant(x, tous) =>
            if (tous.isEmpty){
              (x, ((ps, AppT(n, ps.map(x => VarT(x)))), true))
            }else{
              val tema = ps.map(x => VarT(x))
              (x, ((ps, ArrowT(tous, AppT(n, tema))), true))
            }
        })
        tcc(newev, TEnv(temp.toMap, Map(), Set()))
      case Lazy(n, t, e) =>
        TEnv() + (n, ((List(), t), true))
      case RecFun(n, tps, ps, rt, b) =>
        val tou = ps.map({case(x, t) => t})
        TEnv() + (n, ((tps, ArrowT(tou, rt)), true))
      case _ => error(s"rec_d, else: $d")
    }

    def addup2(s: List[(String, Type)], env: TEnv): TEnv = s match{
      case h::t =>
        addup2(t, env + (h._1, ((List(), h._2), true)))
      case Nil => env
    }

    def thpc(e: Case, w: List[Variant], a: List[String], t: List[Type], env: TEnv): Type = e match{
      case Case(v: String, n: List[String], b: Expr) =>
        if(a.length != t.length) error("thpc, len")
        val w2 = w.map({case Variant(n, ps) => n})
        val w3 = w.map({case Variant(n, ps) => ps})
        val w4 = (w2 zip w3).toMap
        val temp = w4.getOrElse(v, error("thpc, temp")) //t'1, t'2, ... t'h
        if(temp.length != n.length) error("thpc, len2")
        val t2 = temp.map(x => subst(x, a, t)) //types t''1, t''2, ...
        val temp2 = n.zip(t2)
        thp(b, addup2(temp2, env))
      case _ => error("thpc, else")
    }

    def thp(e: Expr, env:TEnv): Type = e match{
      case Id(n: String, t: List[Type]) =>
        t.foreach(valid(_, env))
        val temp = env.tid.getOrElse(n, error(s"thp, id: $n")) //((List[String], Type), Boolean)
        if(t.length != temp._1._1.length) error(s"thp, id2: $n")
        subst(temp._1._2, temp._1._1, t)
      case IntE(value: Int) => IntT
      case BooleanE(value: Boolean) => BooleanT
      case UnitE => UnitT
      case Add(l: Expr, r: Expr) =>
        ms(ms(thp(l, env), IntT), thp(r, env))
      case Mul(l: Expr, r: Expr) =>
        ms(ms(thp(l, env), IntT), thp(r, env))
      case Div(l: Expr, r: Expr) =>
        ms(ms(thp(l, env), IntT), thp(r, env))
      case Mod(l: Expr, r: Expr) =>
        ms(ms(thp(l, env), IntT), thp(r, env))
      case Eq(l: Expr, r: Expr) =>
        ms(ms(thp(l, env), IntT), thp(r, env))
        BooleanT
      case Lt(l: Expr, r: Expr) =>
        ms(ms(thp(l, env), IntT), thp(r, env))
        BooleanT
      case Sequence(l: Expr, r: Expr) =>
        valid(thp(l, env), env)
        thp(r, env)
      case If(c: Expr, t: Expr, f: Expr) =>
        ms(thp(c, env), BooleanT)
        ms(thp(t, env), thp(f, env))
      case Val(mut: Boolean, n: String, t: Option[Type], e: Expr, b: Expr) => t match{
        case Some(tp) =>
          valid(tp, env)
          val te = thp(e, env)
          ms(te, tp)
          thp(b, env + (n, ((List(), te), mut)))
        case None =>
          val te = thp(e, env)
          val newev = env + (n, ((List(), te), mut))
          thp(b, newev)
      }
      case RecBinds(ds: List[RecDef], b: Expr) =>
        val newev = addup(ds, env)
        ds.foreach(validrec(_, newev))
        val tou = thp(b, newev)
        valid(tou, env)
      case Fun(ps: List[(String, Type)], b: Expr) =>
        ps.foreach(x => valid(x._2, env))
        val newev = addup2(ps, env)
        ArrowT(ps.map({case(x, t) => t}), thp(b, newev))
      case Assign(n: String, e: Expr) =>
        if(!env.contains(n)) error(s"assign: $n")
        val temp = env.tid(n) // ((List[String], Type), Boolean)
        if(!temp._1._1.isEmpty) error(s"assign, paramlength: $n")
        if(!temp._2) error(s"assign,var: $n")
        ms(temp._1._2, thp(e, env))
        UnitT
      case App(f: Expr, as: List[Expr]) =>
        thp(f, env) match{
          case ArrowT(pts, rt) =>
            if(as.length != pts.length) error("app, difflen")
            val temp = as.zip(pts)
            temp.foreach({case(e, t) => ms(thp(e, env), t)})
            rt
          case _ => error(s"app, tf: $f")
        }
      case Match(e: Expr, c: List[Case]) => thp(e, env) match{
        case AppT(n, ts) => env.tbinds(n) match{
          case TypeDef(n, as, vs) =>
            if(ts.length != as.length) error("match, length")
            if(c.length != vs.length) error("match, length2")
            val touc = c.map(x => thpc(x, vs, as, ts, env)) //list of types t'
            touc.foreach(x => ms(x, touc.head))
            touc.head
          case _ => error("match")
        }
        case _ => error(s"match, else: $e")
        }
    }

    def typeCheck(expr: Expr): Type = thp(expr, TEnv())
  }

  object U {
    import Untyped._
    type Sto = Map[Addr, Value]

    def toSto(m: Map[Addr, Value]): Sto = m

    def malloc(env: Env, sto: Sto): Addr = {
      val t1 = env.map(_._2).toSet
      val t2 = sto.keySet
      val t3 = t1 ++ t2
      if(t3.isEmpty) 0 else t3.max + 1
    }

    def numVop(op: (Int, Int) => Int): (Value, Value) => IntV = (_, _) match {
      case (IntV(x), IntV(y)) => IntV(op(x, y))
      case (x, y) => error(s"not both numbers: $x, $y")
    }
    val numVAdd = numVop(_ + _)
    val numVSub = numVop(_ - _)
    val numVMul = numVop(_ * _)

    def numop2(op: (Int, Int) => Int): (Value, Value) => Value= (_, _) match{
      case(IntV(x), IntV(y)) =>
        if (y==0) error(s"numop2y0:$x")
        IntV(op(x, y))
      case(x, y) => error(s"numop2:$x, $y")
    }

    val numVDiv = numop2(_/_)
    val numVMod = numop2(_%_)


    def relop(op: (Int, Int) => Boolean) : (Value, Value) => BooleanV =(_, _) match{
      case(IntV(x), IntV(y)) => BooleanV(op(x, y))
      case(x, y) => error("error!")
    }
    val numVEq = relop(_==_)
    val numVLt = relop(_<_)

    def lookup(x: String, env: Env): Addr =
      env.getOrElse(x, error(s"lookup: $x, $env"))

    def storeLookup(a: Addr, sto: Sto): Value ={
      sto.toMap.getOrElse(a, error(s"storelookup: $a"))
    }
    def strict(v: (Value, Sto)): (Value, Sto) = v._1 match{
      case ExprV(e, eenv) =>
        strict(terph(e, eenv, v._2))
      case _ => v
    }

    def rec_env(d: RecDef, prevenv: Env, sto: Sto) : Env = d match{
      case Lazy(n: String, e: Expr) =>
        prevenv + (n -> malloc(prevenv, sto))
      case RecFun(n: String, ps: List[String], b: Expr) =>
        prevenv + (n -> malloc(prevenv, sto))
      case TypeDef(vs: List[Variant]) =>
        vs match{
          case h::t => h match{
              case Variant(n, e) =>
                val newenv = prevenv + (n -> malloc(prevenv, sto))
                rec_env(TypeDef(t), newenv, sto)
              case _ => error("rec_env, typedef")
            }
          case Nil => prevenv
        }
    }

    def rec_sto(d: RecDef, env: Env, prevsto: Sto) : Sto = d match{
      case Lazy(n: String, e: Expr) =>
        if(prevsto.contains(lookup(n, env))) error("rec_sto, lazy sto")
        prevsto + (lookup(n, env) -> ExprV(e, env))
      case RecFun(n: String, ps: List[String], b: Expr) =>
        if(prevsto.contains(lookup(n, env))) error("rec_sto, recfun sto")
        prevsto + (lookup(n, env) -> CloV(ps, b, env))
      case TypeDef(vs: List[Variant]) =>
        vs match{
          case h::t => h match{
              case Variant(n, e) =>
                if(!e){
                  if(prevsto.contains(lookup(n, env))) error("rec_sto, lazy sto")
                  val newsto = prevsto + (lookup(n, env) -> ConstructorV(n))
                  rec_sto(TypeDef(t), env, newsto)
                }else{
                  if(prevsto.contains(lookup(n, env))) error("rec_sto, lazy sto")
                  val newsto = toSto(prevsto.toMap + (lookup(n, env) -> VariantV(n, List())))
                  rec_sto(TypeDef(t), env, newsto)
                }
              case _ => error("rec_env, typedef")
            }
          case Nil => prevsto
        }
    }

    def addenv(d: List[RecDef], env: Env, sto: Sto): Env = d match{
      case h::t => addenv(t, rec_env(h, env, sto), sto)
      case Nil => env
    }

    def addsto(d: List[RecDef], env: Env, sto: Sto): Sto = d match{
      case h::t => addsto(t, env, rec_sto(h, env, sto))
      case Nil => sto
    }

    def conse(l: List[Expr], env: Env, sto: Sto, ans: List[Value]) : (List[Value], Sto) = l match{
      case h::t =>
        val (vs, newsto) = strict(terph(h, env, sto))
        conse(t, env, newsto, ans :+ vs)
      case Nil => (ans, sto)
    }

    def terph(e: Expr, env: Env, sto: Sto): (Value, Sto) = e match{
      case Id(x: String) =>
        val a = lookup(x, env)
        val v = (storeLookup(a, sto), sto) // M(a)
        val v1 = strict(v)
        v._1 match{
          case ExprV(ee, eee) => (v1._1, v1._2 + (a -> v1._1))
          case _ => v1
        }
      case IntE(v: Int) => (IntV(v), sto)
      case BooleanE(v: Boolean) => (BooleanV(v), sto)
      case UnitE => (UnitV, sto)
      case Add(l: Expr, r: Expr) =>
        val (v1, sto1) = strict(terph(l, env, sto))
        val (v2, sto2) = strict(terph(r, env, sto1))
        (numVAdd(v1, v2), sto2)
      case Mul(l: Expr, r: Expr) =>
        val (v1, sto1) = strict(terph(l, env, sto))
        val (v2, sto2) = strict(terph(r, env, sto1))
        (numVMul(v1, v2), sto2)
      case Div(l: Expr, r: Expr) =>
        val (v1, sto1) = strict(terph(l, env, sto))
        val (v2, sto2) = strict(terph(r, env, sto1))
        (numVDiv(v1, v2), sto2)
      case Mod(l: Expr, r: Expr) =>
        val (v1, sto1) = strict(terph(l, env, sto))
        val (v2, sto2) = strict(terph(r, env, sto1))
        (numVMod(v1, v2), sto2)
      case Eq(l: Expr, r: Expr) =>
        val (v1, sto1) = strict(terph(l, env, sto))
        val (v2, sto2) = strict(terph(r, env, sto1))
        (numVEq(v1, v2), sto2)
      case Lt(l: Expr, r: Expr) =>
        val (v1, sto1) = strict(terph(l, env, sto))
        val (v2, sto2) = strict(terph(r, env, sto1))
        (numVLt(v1, v2), sto2)
      case Sequence(l: Expr, r: Expr) =>
        val (v1, sto1) = strict(terph(l, env, sto))
        val (v2, sto2) = strict(terph(r, env, sto1))
        (v2, sto2)
      case If(c: Expr, t: Expr, f: Expr) =>
        val(v1, sto1) = strict(terph(c, env, sto))
        v1 match{
          case BooleanV(true) =>
            strict(terph(t, env, sto1))
          case BooleanV(false) =>
            strict(terph(f, env, sto1))
          case _ => error("if, else")
        }
      case Val(n: String, e: Expr, b: Expr) =>
        val (v1, sto1) = strict(terph(e, env, sto))
        val a = malloc(env, sto1)
        if(sto1.contains(a)) error("Val, sto1 contain a")
        strict(terph(b, env + (n -> a), sto1 + (a -> v1)))
      case RecBinds(ds: List[RecDef], b: Expr) =>
        val sign = addenv(ds, Map(), sto)
        val newev = env.++(sign)
        val ston = addsto(ds, newev, Map())
        val newsto = sto.++(ston)
        strict(terph(b, newev, newsto))
      case Fun(ps: List[String], b: Expr) => (CloV(ps, b, env), sto)
      case Assign(n: String, e: Expr) =>
        if(!env.contains(n)) error("assign, domain no n")
        val a = lookup(n, env)
        val (v, sto1) = strict(terph(e, env, sto))
        (UnitV, sto1 + (a -> v))
      case App(f: Expr, as: List[Expr]) =>
        val (v, sto1) = strict(terph(f, env, sto))
        val (evs, ston) = conse(as, env, sto1, List())
        v match{
          case CloV(ps, b, fenv) =>
            if(evs.length != ps.length) error("App, n m length")
            val as2 = (0 to evs.length-1).toList
            val as = as2.map(x=> x + malloc(env, ston))
            val newev = fenv ++ (ps zip as)
            val newsto = ston ++ (as zip evs)
            strict(terph(b, newev, newsto))
          case ConstructorV(n) =>
            (VariantV(n, evs), ston)
          case _ => error(s"app, v: $v")
        }
      case Match(e: Expr, cs: List[Case]) =>
        val (v, sto1) = strict(terph(e, env, sto))
        v match{
          case VariantV(n, vs) =>
            val csn = cs.map({case Case(x, n, b) => x})
            val csp = cs.map({case Case(x, n, b) => (n, b)})
            val ca = (csn zip csp).toMap
            val (xs, bp) = ca.getOrElse(n, error(s"Match, no x: $v, $cs"))
            if(vs.length != xs.length) error("Match, length")
            val as2 = (0 to vs.length-1).toList
            val as = as2.map(x=> x + malloc(env, sto1))
            val newev = env ++(xs zip as)
            val newsto = sto1 ++(as zip vs)
            strict(terph(bp, newev, newsto))
          case _ => error("match, e not variantV")
        }
    }
    def interp(expr: Expr): Value = terph(expr, Map(), Map())._1
  }

  def tests: Unit = {
    // test-int
    test(run("42"), "42")
    // test-boolean
    test(run("true"), "true")
    // test-unit
    test(run("()"), "()")

    // test-add
    test(run("1 + 2"), "3")
    // test-mul
    test(run("2 * 4"), "8")
    // test-div
    test(run("5 / 2"), "2")
    // test-mod
    test(run("13 % 5"), "3")
    // test-eq
    test(run("1 == 1"), "true")
    // test-lt
    test(run("1 < 1"), "false")
    // test-seq
    test(run("{1; 2}"), "2")

    // test-if
    test(run("if (true) 1 else 2"), "1")

    // test-val
    test(run("""
      val x = 1 + 2;
      val y: Int = x * 4 + 1;
      y / (x - 1)
    """), "6")
    // test-lazy
    test(run("""
      lazy val f: Int => Int = (x: Int) => if (x < 1) 0 else x + f(x - 1);
      f(10)
    """), "55")
    // test-rec
    test(run("""
      def f(x: Int): Int = if (x < 1) 0 else x + f(x - 1);
      f(10)
    """), "55")

    // test-fun
    test(run("(x: Int) => x + x"), "<function>")
    // test-app
    test(run("((x: Int, y: Int) => x + y)(1, 2)"), "3")

    // test-var-assign
    test(run("""
      var x = 1;
      var y: Int = x * 4 + 8;
      { x = 3; y / (x - 1) }
    """), "6")

    // test-type-match
    test(run("""
      type Fruit {
        case Apple
        case Banana(Int)
      }
      (Apple match {
        case Apple => 1
        case Banana(x) => 0
      }) + (Banana(1) match {
        case Apple => 0
        case Banana(x) => x
      })
    """), "2")

    // test-poly1
    test(run("""
      def f['T, 'S](t: 'T, s: 'S): 'T = t;
      f[Int, Boolean](1, true)
    """), "1")
    // test-poly2
    test(run("""
      type Fruit['T] {
        case Apple
        case Banana('T)
      }
      (Apple[Boolean] match {
        case Apple => 1
        case Banana(x) => 0
      }) + (Banana[Int](1) match {
        case Apple => 0
        case Banana(x) => x
      })
    """), "2")

    // test-primitive
    test(
      runWithStdLib(
"""var score = 0;
def check(b: Boolean): Unit =
  if (b) score = score + 1;

{
check(!intEquals(1, 2));
check(intEquals(3, 3));
check(intMax(3, 6) == 6);
check(intMin(3, 6) == 3);
check(!booleanEquals(true, false));
check(booleanEquals(true, true));
check(unitEquals((), ()));

score
}"""
      ),
      "7"
    )

    // test-pair
    test(
      runWithStdLib(
"""var score = 0;
def check(b: Boolean): Unit =
  if (b) score = score + 1;

val p1 = Pair[Int, Boolean](1, true);
val p2 = Pair[Int, Boolean](1, false);
val p3 = Pair[Int, Boolean](2, true);

val eq = pairEquals[Int, Boolean](intEquals, booleanEquals);

{
check(pairFst[Int, Boolean](p1) == 1);
check(pairSnd[Int, Boolean](p1));
check(pairFst[Int, Boolean](p2) == 1);
check(!pairSnd[Int, Boolean](p2));
check(pairFst[Int, Boolean](p3) == 2);
check(pairSnd[Int, Boolean](p3));
check(eq(p1, p1));
check(!eq(p1, p2));
check(!eq(p1, p3));

score
}"""
      ),
      "9"
    )

    // test-option
    test(
      runWithStdLib(
"""var score = 0;
def check(b: Boolean): Unit =
  if (b) score = score + 1;

val opt1 = Some[Int](1);
val opt2 = optionMap[Int, Int](opt1, (x: Int) => x + x);
val opt3 = optionFilter[Int](opt1, (x: Int) => x < 2);
val opt4 = optionFilter[Int](opt2, (x: Int) => x < 2);
val opt5 = optionFlatten[Int](Some[Option[Int]](opt1));
val opt6 = optionFlatten[Int](Some[Option[Int]](opt4));
val opt7 = optionFlatten[Int](None[Option[Int]]);

def aux(i: Int): Option[Int] =
  if (i == 1) Some[Int](i) else None[Int];

val opt8 = optionFlatMap[Int, Int](opt1, aux);
val opt9 = optionFlatMap[Int, Int](opt2, aux);
val opt10 = optionFlatMap[Int, Int](opt4, aux);
val opt11 = optionFilterNot[Int](opt1, (x: Int) => x < 2);
val opt12 = optionFilterNot[Int](opt2, (x: Int) => x < 2);

val eq = optionEquals[Int](intEquals);
val eql = listEquals[Int](intEquals);

{
check(eq(Some[Int](1), Some[Int](1)));
check(!eq(Some[Int](1), Some[Int](2)));
check(!eq(Some[Int](1), None[Int]));
check(eq(None[Int], None[Int]));
check(eq(opt1, Some[Int](1)));
check(eq(opt2, Some[Int](2)));
check(eq(opt3, Some[Int](1)));
check(eq(opt4, None[Int]));
check(eq(opt5, Some[Int](1)));
check(eq(opt6, None[Int]));
check(eq(opt7, None[Int]));
check(eq(opt8, Some[Int](1)));
check(eq(opt9, None[Int]));
check(eq(opt10, None[Int]));
check(eq(opt11, None[Int]));
check(eq(opt12, Some[Int](2)));
check(!optionIsEmpty[Int](opt1));
check(optionIsEmpty[Int](opt4));
check(optionNonEmpty[Int](opt1));
check(!optionNonEmpty[Int](opt4));
check(eql(optionToList[Int](opt1), List1[Int](1)));
check(eql(optionToList[Int](opt4), List0[Int]()));
check(optionGetOrElse[Int](opt1, 0) == 1);
check(optionGetOrElse[Int](opt4, 0) == 0);
optionForeach[Int](opt1, (i: Int) => check(i == 1));
optionForeach[Int](opt4, (i: Int) => check(true));

score
}"""
      ),
      "25"
    )

    // test-box
    test(
      runWithStdLib(
"""var score = 0;
def check(b: Boolean): Unit =
  if (b) score = score + 1;

val b = Box[Int](1);
val i1 = boxGet[Int](b);
val i2 = boxSet[Int](b, 2);
val i3 = boxGet[Int](b);
val i4 = boxSet[Int](b, 1);
val i5 = boxGet[Int](b);

{
check(i1 == 1);
check(i2 == 1);
check(i3 == 2);
check(i4 == 2);
check(i5 == 1);

score
}"""
      ),
      "5"
    )

    // test-list
    test(
      runWithStdLib(
"""var score = 0;
def check(b: Boolean): Unit =
  if (b) score = score + 1;

val l0 = List5[Int](1, 2, 3, 4, 5);
val l1 = List3[Int](1, 2, 3);
val l2 = List2[Int](4, 5);
val zipped0 = listZip[Int, Int](l0, l0);
val unzipped0 = listUnzip[Int, Int](zipped0);
val l3 = pairFst[List[Int], List[Int]](unzipped0);
val l4 = pairSnd[List[Int], List[Int]](unzipped0);
val zipped1 = listZip[Int, Int](l0, l1);
val unzipped1 = listUnzip[Int, Int](zipped1);
val l5 = pairFst[List[Int], List[Int]](unzipped1);
val l6 = pairSnd[List[Int], List[Int]](unzipped1);
val zipped2 = listZipWithIndex[Int](l0);
val unzipped2 = listUnzip[Int, Int](zipped2);
val l7 = pairFst[List[Int], List[Int]](unzipped2);
val l8 = pairSnd[List[Int], List[Int]](unzipped2);

val eq = listEquals[Int](intEquals);
val eqo = optionEquals[Int](intEquals);
def odd(n: Int): Boolean = n % 2 != 0;
def lt4(n: Int): Boolean = n < 4;

{
check(eq(l0, l0));
check(!eq(l0, l1));
check(!eq(l0, l2));
check(!eq(l1, l2));
check(!eq(l0, Nil[Int]));
check(eq(Nil[Int], Nil[Int]));
check(eq(listAppended[Int](listAppended[Int](l1, 4), 5), l0));
check(eq(listConcat[Int](l1, l2), l0));
check(listCount[Int](l0, odd) == 3);
check(eq(listDrop[Int](l0, 3), l2));
check(listExists[Int](l0, lt4));
check(!listExists[Int](l2, lt4));
check(eq(listFilter[Int](l0, lt4), l1));
check(eq(listFilterNot[Int](l0, lt4), l2));
check(eqo(listFind[Int](l0, lt4), Some[Int](1)));
check(eqo(listFind[Int](l2, lt4), None[Int]));
check(eq(listFlatMap[Int, Int](l1, (n: Int) => if (n == 1) l1 else if (n == 2) l2 else Nil[Int]), l0));
check(eq(listFlatten[Int](List2[List[Int]](l1, l2)), l0));
check(listFoldLeft[Int, Int](0, l0, (n: Int, m: Int) => n + m) == 15);
check(listFoldRight[Int, Int](l0, 0, (n: Int, m: Int) => n + m) == 15);
check(!listForall[Int](l0, lt4));
check(listForall[Int](l1, lt4));
listForeach[Int](l0, (n: Int) => check(odd(n)));
check(eqo(listGet[Int](l0, 4), Some[Int](5)));
check(eqo(listGet[Int](l0, 5), None[Int]));
check(!listIsEmpty[Int](l0));
check(listIsEmpty[Int](Nil[Int]));
check(listLength[Int](l0) == 5);
check(eq(listMap[Int, Int](l0, (n: Int) => n * n), List5[Int](1, 4, 9, 16, 25)));
check(listNonEmpty[Int](l0));
check(!listNonEmpty[Int](Nil[Int]));
check(eq(listPrepended[Int](listPrepended[Int](listPrepended[Int](l2, 3), 2), 1), l0));
check(eq(listReverse[Int](l0), List5[Int](5, 4, 3, 2, 1)));
check(eq(listTake[Int](l0, 3), l1));
check(eq(l0, l3));
check(eq(l0, l4));
check(eq(l1, l5));
check(eq(l1, l6));
check(eq(l0, l7));
check(eq(l0, listMap[Int, Int](l8, (n: Int) => n + 1)));

score
}"""
      ),
      "42"
    )

    // test-map
    test(
      runWithStdLib(
"""var score = 0;
def check(b: Boolean): Unit =
  if (b) score = score + 1;

val m0 = Map1[Int, Int](intEquals, 0, 0);
val m1 = mapUpdated[Int, Int](m0, 1, 2);
val m2 = mapUpdated[Int, Int](m1, 2, 4);
val m3 = mapUpdated[Int, Int](m2, 3, 6);
val m4 = mapRemoved[Int, Int](m3, 2);
val m5 = mapUpdated[Int, Int](m2, 3, 8);

val eqo = optionEquals[Int](intEquals);

{
check(eqo(mapGet[Int, Int](m0, 0), Some[Int](0)));
check(eqo(mapGet[Int, Int](m0, 1), None[Int]));
check(eqo(mapGet[Int, Int](m0, 2), None[Int]));
check(eqo(mapGet[Int, Int](m0, 3), None[Int]));
check(eqo(mapGet[Int, Int](m0, 4), None[Int]));

check(eqo(mapGet[Int, Int](m1, 0), Some[Int](0)));
check(eqo(mapGet[Int, Int](m1, 1), Some[Int](2)));
check(eqo(mapGet[Int, Int](m1, 2), None[Int]));
check(eqo(mapGet[Int, Int](m1, 3), None[Int]));
check(eqo(mapGet[Int, Int](m1, 4), None[Int]));

check(eqo(mapGet[Int, Int](m2, 0), Some[Int](0)));
check(eqo(mapGet[Int, Int](m2, 1), Some[Int](2)));
check(eqo(mapGet[Int, Int](m2, 2), Some[Int](4)));
check(eqo(mapGet[Int, Int](m2, 3), None[Int]));
check(eqo(mapGet[Int, Int](m2, 4), None[Int]));

check(eqo(mapGet[Int, Int](m3, 0), Some[Int](0)));
check(eqo(mapGet[Int, Int](m3, 1), Some[Int](2)));
check(eqo(mapGet[Int, Int](m3, 2), Some[Int](4)));
check(eqo(mapGet[Int, Int](m3, 3), Some[Int](6)));
check(eqo(mapGet[Int, Int](m3, 4), None[Int]));

check(eqo(mapGet[Int, Int](m4, 0), Some[Int](0)));
check(eqo(mapGet[Int, Int](m4, 1), Some[Int](2)));
check(eqo(mapGet[Int, Int](m4, 2), None[Int]));
check(eqo(mapGet[Int, Int](m4, 3), Some[Int](6)));
check(eqo(mapGet[Int, Int](m4, 4), None[Int]));

check(eqo(mapGet[Int, Int](m4, 0), Some[Int](0)));
check(eqo(mapGet[Int, Int](m4, 1), Some[Int](2)));
check(eqo(mapGet[Int, Int](m4, 2), None[Int]));
check(eqo(mapGet[Int, Int](m4, 3), Some[Int](6)));
check(eqo(mapGet[Int, Int](m4, 4), None[Int]));

score
}"""
      ),
      "30"
    )

    // test-string
    test(
      runWithStdLib(
"""var score = 0;
def check(b: Boolean): Unit =
  if (b) score = score + 1;

{
check(stringEquals("abc \n"<STRP, EOS>, List5[Int](97, 98, 99, 32, 10)));
check(stringEquals(substring("12abc \n"<STRP, EOS>, 2, 5), List3[Int](97, 98, 99)));
check("abc \n"<(n: Int, m: Int) => n + m, 0> == 336);

score
}"""
      ),
      "3"
    )
    // test-fae
    test(
      runWithStdLib(
"""
type Expr {
  case Num(Int)
  case Add(Expr, Expr)
  case Sub(Expr, Expr)
  case Id(Int)
  case Fun(Int, Expr)
  case App(Expr, Expr)
}

type Value {
  case NumV(Int)
  case CloV(Int, Expr, Map[Int, Value])
}

def interp(e: Expr, env: Map[Int, Value]): Option[Value] = e match {
  case Num(n) => Some[Value](NumV(n))
  case Add(l, r) => optionFlatMap[Value, Value](interp(l, env), (lv: Value) => lv match {
    case NumV(n) => optionFlatMap[Value, Value](interp(r, env),
      (rv: Value) => rv match {
        case NumV(m) => Some[Value](NumV(n + m))
        case CloV(x, e, fenv) => None[Value]
      }
    )
    case CloV(x, e, fenv) => None[Value]
  })
  case Sub(l, r) => optionFlatMap[Value, Value](interp(l, env), (lv: Value) => lv match {
    case NumV(n) => optionFlatMap[Value, Value](interp(r, env),
      (rv: Value) => rv match {
        case NumV(m) => Some[Value](NumV(n - m))
        case CloV(x, e, fenv) => None[Value]
      }
    )
    case CloV(x, e, fenv) => None[Value]
  })
  case Id(x) => mapGet[Int, Value](env, x)
  case Fun(x, e) => Some[Value](CloV(x, e, env))
  case App(f, a) => optionFlatMap[Value, Value](interp(f, env), (fv: Value) => fv match {
    case NumV(n) => None[Value]
    case CloV(x, e, fenv) => optionFlatMap[Value, Value](interp(a, env),
      (av: Value) => interp(e, mapUpdated[Int, Value](fenv, x, av))
    )
  })
};

lazy val digit: Parser[Expr] =
  parserMap[Int, Expr](
    () => parserCond((x: Int) => 48 <= x && x < 58),
    (x: Int) => Num(x - 48)
  );

lazy val add: Parser[Expr] =
  parserMap[Pair[Int, Pair[Expr, Expr]], Expr](
    () => parserThen[Int, Pair[Expr, Expr]](
      () => parserConst(43),
      () => parserThen[Expr, Expr](() => e, () => e)
    ),
    (p: Pair[Int, Pair[Expr, Expr]]) =>
      pairSnd[Int, Pair[Expr, Expr]](p) match {
        case Pair(l, r) => Add(l, r)
      }
  );

lazy val sub: Parser[Expr] =
  parserMap[Pair[Int, Pair[Expr, Expr]], Expr](
    () => parserThen[Int, Pair[Expr, Expr]](
      () => parserConst(45),
      () => parserThen[Expr, Expr](() => e, () => e)
    ),
    (p: Pair[Int, Pair[Expr, Expr]]) =>
      pairSnd[Int, Pair[Expr, Expr]](p) match {
        case Pair(l, r) => Sub(l, r)
      }
  );

lazy val id: Parser[Expr] =
  parserMap[Int, Expr](
    () => parserCond((x: Int) => 97 <= x && x <= 122),
    (x: Int) => Id(x)
  );

lazy val fun: Parser[Expr] =
  parserMap[Pair[Int, Pair[Int, Expr]], Expr](
    () => parserThen[Int, Pair[Int, Expr]](
      () => parserConst(47),
      () => parserThen[Int, Expr](
        () => parserCond((x: Int) => 97 <= x && x <= 122),
        () => e
      )
    ),
    (p: Pair[Int, Pair[Int, Expr]]) =>
      pairSnd[Int, Pair[Int, Expr]](p) match {
        case Pair(p, b) => Fun(p, b)
      }
  );

lazy val app: Parser[Expr] =
  parserMap[Pair[Int, Pair[Expr, Expr]], Expr](
    () => parserThen[Int, Pair[Expr, Expr]](
      () => parserConst(64),
      () => parserThen[Expr, Expr](() => e, () => e)
    ),
    (p: Pair[Int, Pair[Expr, Expr]]) =>
      pairSnd[Int, Pair[Expr, Expr]](p) match {
        case Pair(l, r) => App(l, r)
      }
  );

lazy val e: Parser[Expr] =
  parserOr[Expr](
    () => parserOr[Expr](
      () => parserOr[Expr](
        () => parserOr[Expr](
          () => parserOr[Expr](
            () => digit,
            () => add
          ),
          () => sub
        ),
        () => id
      ),
      () => fun
    ),
    () => app
  );

parseAll[Expr](e, "@@/x/y+xy23"<STRP, EOS>) match {
  case None => -1
  case Some(e) => interp(e, Map0[Int, Value](intEquals)) match {
    case None => -2
    case Some(v) => v match {
      case NumV(n) => if (n < 0) -3 else n
      case CloV(x, e, env) => -4
    }
  }
}
"""
      ),
      "5"
    )
  }

}
