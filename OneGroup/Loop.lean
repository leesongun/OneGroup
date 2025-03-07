import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Opposites

/--
A more computable version of bijective.
-/
structure HasInverse (f : α → β) where
  inv : β → α
  right : Function.LeftInverse f inv
  left : Function.LeftInverse inv f

/--
A quasigroup is a set with a binary operation such that left and right mulision are always possible.
-/
class QuasiGroup (G : Type*) extends Mul G where
  right_quotient (a : G) : HasInverse (a * ·)
  left_quotient (a : G) : HasInverse (· * a)

/--
A loop is a set with a binary operation that has a two-sided identity element,
and for which left and right mulision are always possible.
-/
class Loop (G : Type*) extends MulOneClass G, QuasiGroup G

class LeftBolLoop (G : Type*) extends Loop G where
  left_bol (x y z : G) : x * (y * (x * z)) = ((x * y) * x) * z

class RightBolLoop (G : Type*) extends LeftBolLoop (Gᵐᵒᵖ) where

/--
A Moufang loop is a loop that is both left and right Bol loop.
-/
class MoufangLoop (G : Type*) extends Loop G where
  left_bol (x y z : G) : x * (y * (x * z)) = ((x * y) * x) * z
  right_bol (x y z : G) : ((z * x) * y) * z = z * (x * (y * x))
