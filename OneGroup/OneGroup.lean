import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Tactic.Group

/--
A `OneGroup` is a type equipped with a division operation `/` satisfying the single axiom
`a / ((a / a / b / c) / (a / a / a / c)) = b`.  This axiom is sufficient to define inverses
and multiplication, and to prove that the type forms a group.

This class is named `OneGroup` because there is only one defining axiom.
-/
class OneGroup (G : Type) extends Div G where
  /-- The defining axiom for a `OneGroup`. -/
  one_axiom (a b c : G) : a / ((a / a / b / c) / (a / a / a / c)) = b

namespace OneGroup

instance [Group G] : OneGroup G where
  one_axiom a b c := by simp

variable [OneGroup G]

/-- Surjectivity of the map `λ c, a / c`. -/
theorem div_surjective (a b : G) : ∃ (c : G), a / c = b :=
  ⟨(a / a / b / b) / (a / a / a / b), OneGroup.one_axiom _ _ _⟩

@[simp] theorem div_cancel_right (a b : G) : a / (b / b) = a := by
  have ⟨x, _⟩ := div_surjective (a / a / a) b
  have := OneGroup.one_axiom a a x
  simp_all

/-- `a / a` is independent of `a`. -/
theorem div_self_eq_div_self (a b : G) : a / a = b / b := by
  have := OneGroup.one_axiom a (a / a) a
  have := OneGroup.one_axiom a (b / b) a
  simp_all [div_cancel_right]

/-- Define the inverse `x⁻¹` of `x` to be `(x / x) / x`. -/
@[simps] instance : Inv G where
  inv x := (x / x) / x

@[simp] theorem inv_inv (a : G) : a⁻¹⁻¹ = a := by
  have := OneGroup.one_axiom (a / a) a (a / a)
  simp_all [div_self_eq_div_self _ a]

@[simp] theorem div_div_inv (a b : G) : a / b / b⁻¹ = a := by
  suffices _⁻¹⁻¹ = a by simpa only [inv_inv]
  have := OneGroup.one_axiom (a / a) a⁻¹ b
  have := inv_inv a
  have := (div_self_eq_div_self · a)
  simp_all

@[simp] theorem inv_div (a b : G) : (b / a)⁻¹ = a / b := by
  rw [← OneGroup.one_axiom a (b / a)⁻¹ (a / a)]
  have : a / a / (b / a)⁻¹ = b / a := by
    rw [div_self_eq_div_self]
    exact inv_inv _
  have := div_div_inv b
  simp_all

@[simp] theorem div_div (a b c : G) : (a / c) / (b / c) = a / b := by
  rw [← OneGroup.one_axiom _ (a / b) a⁻¹]
  congr
  all_goals
  rw [div_self_eq_div_self]
  change _ = (_ / _)⁻¹ / _
  rw [inv_div, div_div_inv]

/-- Define multiplication `x * y` to be `x / y⁻¹`. -/
@[simps] instance : Mul G where
  mul x y := x / y⁻¹

/-- The multiplication is associative. -/
theorem mul_assoc (a b c : G) : a * b * c = a * (b * c) := by
  convert_to a / b⁻¹ / c⁻¹ = a / (b / c⁻¹)⁻¹
  rw [← div_div_inv (_ / c⁻¹) (b / c⁻¹)]
  have := div_div_inv a b⁻¹
  simp_all

variable [Inhabited G]

/-- Define `1` to be `default / default`. -/
@[simps]
instance : One G where
  one := default / default

/-- Construct a `Group` instance from a `OneGroup` instance. -/
def instGroup G [OneGroup G] [Inhabited G] := @Group.ofLeftAxioms
  G _ _ _ mul_assoc
  (by intro; simp; rw [div_self_eq_div_self]; exact inv_inv _)
  (fun _ => div_self_eq_div_self _ _)

/--
The division operation defined in the `OneGroup` class agrees with the division operation
defined in the `Group` instance constructed from the `OneGroup` instance.
-/
theorem div_eq_div : (inferInstanceAs $ OneGroup G).div = (instGroup G).div := by
  funext _ a
  change _ / _ = _ / a⁻¹⁻¹
  simp

end OneGroup
