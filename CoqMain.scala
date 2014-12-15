object CoqMain {
  sealed abstract class Bool
  case class True() extends Bool
  case class False() extends Bool
  sealed abstract class Nat
  case class O() extends Nat
  case class S(x1: Nat) extends Nat
  sealed abstract class Option[A]
  case class Some[A](x1: A) extends Option[A]
  case class None[A]() extends Option[A]
  sealed abstract class List[A]
  case class Nil[A]() extends List[A]
  case class Cons[A](x1: A, x2: List[A]) extends List[A]
  def app[A] : (List[A] => (List[A] => List[A])) = {
    (l:List[A]) => (m:List[A]) =>
      l match {
        case Nil() =>
          m
        case Cons(a, l1) =>
          Cons(a, app[A](l1)(m))
      }
  }
  sealed abstract class Comparison
  case class Eq() extends Comparison
  case class Lt() extends Comparison
  case class Gt() extends Comparison
  def nat_compare : (Nat => (Nat => Comparison)) = {
    (n:Nat) => (m:Nat) =>
      n match {
        case O() =>
          m match {
            case O() =>
              Eq()
            case S(n0) =>
              Lt()
          }
        case S(n$prime) =>
          m match {
            case O() =>
              Gt()
            case S(m$prime) =>
              nat_compare(n$prime)(m$prime)
          }
      }
  }
  sealed abstract class Color
  case class R() extends Color
  case class B() extends Color
  sealed abstract class Tree
  case class E() extends Tree
  case class T(x1: Color, x2: Tree, x3: Nat, x4: Tree) extends Tree
  def member : (Nat => (Tree => Bool)) = {
    (x:Nat) => (t:Tree) =>
      t match {
        case E() =>
          False()
        case T(c, a, y, b) =>
          nat_compare(x)(y) match {
            case Eq() =>
              True()
            case Lt() =>
              member(x)(a)
            case Gt() =>
              member(x)(b)
          }
      }
  }
  def balance : (Tree => Tree) = {
    (t:Tree) =>
      t match {
        case E() =>
          E()
        case T(color0, a, x, b) =>
          color0 match {
            case R() =>
              T(color0, a, x, b)
            case B() =>
              a match {
                case E() =>
                  b match {
                    case E() =>
                      T(color0, a, x, b)
                    case T(c0, b0, y, d) =>
                      c0 match {
                        case R() =>
                          b0 match {
                            case E() =>
                              d match {
                                case E() =>
                                  T(color0, a, x, b)
                                case T(c1, c, z, d0) =>
                                  c1 match {
                                    case R() =>
                                      T(R(), T(B(), a, x, b0), y, T(B(), c, z, d0))
                                    case B() =>
                                      T(color0, a, x, b)
                                  }
                              }
                            case T(c1, b1, y0, c) =>
                              c1 match {
                                case R() =>
                                  T(R(), T(B(), a, x, b1), y0, T(B(), c, y, d))
                                case B() =>
                                  d match {
                                    case E() =>
                                      T(color0, a, x, b)
                                    case T(c2, c3, z, d0) =>
                                      c2 match {
                                        case R() =>
                                          T(R(), T(B(), a, x, b0), y, T(B(), c3, z, d0))
                                        case B() =>
                                          T(color0, a, x, b)
                                      }
                                  }
                              }
                          }
                        case B() =>
                          T(color0, a, x, b)
                      }
                  }
                case T(c0, a0, x0, c) =>
                  c0 match {
                    case R() =>
                      a0 match {
                        case E() =>
                          c match {
                            case E() =>
                              b match {
                                case E() =>
                                  T(color0, a, x, b)
                                case T(c1, b0, y, d) =>
                                  c1 match {
                                    case R() =>
                                      b0 match {
                                        case E() =>
                                          d match {
                                            case E() =>
                                              T(color0, a, x, b)
                                            case T(c2, c3, z, d0) =>
                                              c2 match {
                                                case R() =>
                                                  T(R(), T(B(), a, x, b0), y, T(B(), c3, z, d0))
                                                case B() =>
                                                  T(color0, a, x, b)
                                              }
                                          }
                                        case T(c2, b1, y0, c3) =>
                                          c2 match {
                                            case R() =>
                                              T(R(), T(B(), a, x, b1), y0, T(B(), c3, y, d))
                                            case B() =>
                                              d match {
                                                case E() =>
                                                  T(color0, a, x, b)
                                                case T(c4, c5, z, d0) =>
                                                  c4 match {
                                                    case R() =>
                                                      T(R(), T(B(), a, x, b0), y, T(B(), c5, z, d0))
                                                    case B() =>
                                                      T(color0, a, x, b)
                                                  }
                                              }
                                          }
                                      }
                                    case B() =>
                                      T(color0, a, x, b)
                                  }
                              }
                            case T(c1, b0, y, c2) =>
                              c1 match {
                                case R() =>
                                  T(R(), T(B(), a0, x0, b0), y, T(B(), c2, x, b))
                                case B() =>
                                  b match {
                                    case E() =>
                                      T(color0, a, x, b)
                                    case T(c3, b1, y0, d) =>
                                      c3 match {
                                        case R() =>
                                          b1 match {
                                            case E() =>
                                              d match {
                                                case E() =>
                                                  T(color0, a, x, b)
                                                case T(c4, c5, z, d0) =>
                                                  c4 match {
                                                    case R() =>
                                                      T(R(), T(B(), a, x, b1), y0, T(B(), c5, z, d0))
                                                    case B() =>
                                                      T(color0, a, x, b)
                                                  }
                                              }
                                            case T(c4, b2, y1, c5) =>
                                              c4 match {
                                                case R() =>
                                                  T(R(), T(B(), a, x, b2), y1, T(B(), c5, y0, d))
                                                case B() =>
                                                  d match {
                                                    case E() =>
                                                      T(color0, a, x, b)
                                                    case T(c6, c7, z, d0) =>
                                                      c6 match {
                                                        case R() =>
                                                          T(R(), T(B(), a, x, b1), y0, T(B(), c7, z, d0))
                                                        case B() =>
                                                          T(color0, a, x, b)
                                                      }
                                                  }
                                              }
                                          }
                                        case B() =>
                                          T(color0, a, x, b)
                                      }
                                  }
                              }
                          }
                        case T(c1, a1, x1, b0) =>
                          c1 match {
                            case R() =>
                              T(R(), T(B(), a1, x1, b0), x0, T(B(), c, x, b))
                            case B() =>
                              c match {
                                case E() =>
                                  b match {
                                    case E() =>
                                      T(color0, a, x, b)
                                    case T(c2, b1, y, d) =>
                                      c2 match {
                                        case R() =>
                                          b1 match {
                                            case E() =>
                                              d match {
                                                case E() =>
                                                  T(color0, a, x, b)
                                                case T(c3, c4, z, d0) =>
                                                  c3 match {
                                                    case R() =>
                                                      T(R(), T(B(), a, x, b1), y, T(B(), c4, z, d0))
                                                    case B() =>
                                                      T(color0, a, x, b)
                                                  }
                                              }
                                            case T(c3, b2, y0, c4) =>
                                              c3 match {
                                                case R() =>
                                                  T(R(), T(B(), a, x, b2), y0, T(B(), c4, y, d))
                                                case B() =>
                                                  d match {
                                                    case E() =>
                                                      T(color0, a, x, b)
                                                    case T(c5, c6, z, d0) =>
                                                      c5 match {
                                                        case R() =>
                                                          T(R(), T(B(), a, x, b1), y, T(B(), c6, z, d0))
                                                        case B() =>
                                                          T(color0, a, x, b)
                                                      }
                                                  }
                                              }
                                          }
                                        case B() =>
                                          T(color0, a, x, b)
                                      }
                                  }
                                case T(c2, b1, y, c3) =>
                                  c2 match {
                                    case R() =>
                                      T(R(), T(B(), a0, x0, b1), y, T(B(), c3, x, b))
                                    case B() =>
                                      b match {
                                        case E() =>
                                          T(color0, a, x, b)
                                        case T(c4, b2, y0, d) =>
                                          c4 match {
                                            case R() =>
                                              b2 match {
                                                case E() =>
                                                  d match {
                                                    case E() =>
                                                      T(color0, a, x, b)
                                                    case T(c5, c6, z, d0) =>
                                                      c5 match {
                                                        case R() =>
                                                          T(R(), T(B(), a, x, b2), y0, T(B(), c6, z, d0))
                                                        case B() =>
                                                          T(color0, a, x, b)
                                                      }
                                                  }
                                                case T(c5, b3, y1, c6) =>
                                                  c5 match {
                                                    case R() =>
                                                      T(R(), T(B(), a, x, b3), y1, T(B(), c6, y0, d))
                                                    case B() =>
                                                      d match {
                                                        case E() =>
                                                          T(color0, a, x, b)
                                                        case T(c7, c8, z, d0) =>
                                                          c7 match {
                                                            case R() =>
                                                              T(R(), T(B(), a, x, b2), y0, T(B(), c8, z, d0))
                                                            case B() =>
                                                              T(color0, a, x, b)
                                                          }
                                                      }
                                                  }
                                              }
                                            case B() =>
                                              T(color0, a, x, b)
                                          }
                                      }
                                  }
                              }
                          }
                      }
                    case B() =>
                      b match {
                        case E() =>
                          T(color0, a, x, b)
                        case T(c1, b0, y, d) =>
                          c1 match {
                            case R() =>
                              b0 match {
                                case E() =>
                                  d match {
                                    case E() =>
                                      T(color0, a, x, b)
                                    case T(c2, c3, z, d0) =>
                                      c2 match {
                                        case R() =>
                                          T(R(), T(B(), a, x, b0), y, T(B(), c3, z, d0))
                                        case B() =>
                                          T(color0, a, x, b)
                                      }
                                  }
                                case T(c2, b1, y0, c3) =>
                                  c2 match {
                                    case R() =>
                                      T(R(), T(B(), a, x, b1), y0, T(B(), c3, y, d))
                                    case B() =>
                                      d match {
                                        case E() =>
                                          T(color0, a, x, b)
                                        case T(c4, c5, z, d0) =>
                                          c4 match {
                                            case R() =>
                                              T(R(), T(B(), a, x, b0), y, T(B(), c5, z, d0))
                                            case B() =>
                                              T(color0, a, x, b)
                                          }
                                      }
                                  }
                              }
                            case B() =>
                              T(color0, a, x, b)
                          }
                      }
                  }
              }
          }
      }
  }
  def ins : (Nat => (Tree => Tree)) = {
    (x:Nat) => (t:Tree) =>
      t match {
        case E() =>
          T(R(), E(), x, E())
        case T(color0, a, y, b) =>
          nat_compare(x)(y) match {
            case Eq() =>
              T(color0, a, y, b)
            case Lt() =>
              balance(T(color0, ins(x)(a), y, b))
            case Gt() =>
              balance(T(color0, a, y, ins(x)(b)))
          }
      }
  }
  def make_black : (Tree => Tree) = {
    (t:Tree) =>
      t match {
        case E() =>
          E()
        case T(c, a, y, b) =>
          T(B(), a, y, b)
      }
  }
  def insert : (Nat => (Tree => Tree)) = {
    (x:Nat) => (t:Tree) =>
      make_black(ins(x)(t))
  }
  def left : (Tree => Tree) = {
    (t:Tree) =>
      t match {
        case E() =>
          E()
        case T(c, a, n, t0) =>
          a
      }
  }
  def right : (Tree => Tree) = {
    (t:Tree) =>
      t match {
        case E() =>
          E()
        case T(c, t0, n, b) =>
          b
      }
  }
  def color : (Tree => Option[Color]) = {
    (t:Tree) =>
      t match {
        case E() =>
          None()
        case T(c, t0, n, t1) =>
          Some(c)
      }
  }
  def value : (Tree => Option[Nat]) = {
    (t:Tree) =>
      t match {
        case E() =>
          None()
        case T(c, a, x, b) =>
          Some(x)
      }
  }
  def snoc[A] : (List[A] => (A => List[A])) = {
    (l:List[A]) => (v:A) =>
      l match {
        case Nil() =>
          Cons(v, Nil())
        case Cons(h, t) =>
          Cons(h, snoc[A](t)(v))
      }
  }
  def traversal : (Tree => List[Nat]) = {
    (t:Tree) =>
      t match {
        case E() =>
          Nil()
        case T(c, a, x, b) =>
          a match {
            case E() =>
              b match {
                case E() =>
                  Cons(x, Nil())
                case T(c0, t0, n, t1) =>
                  Cons(x, traversal(b))
              }
            case T(c0, t0, n, t1) =>
              b match {
                case E() =>
                  snoc[Nat](traversal(a))(x)
                case T(c1, t2, n0, t3) =>
                  app[Nat](snoc[Nat](traversal(a))(x))(traversal(b))
              }
          }
      }
  }
}