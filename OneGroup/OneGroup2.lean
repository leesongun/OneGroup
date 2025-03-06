import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Tactic.Group

/--
A `OneGroup2` is a type equipped with a division operation `/` satisfying the single axiom
`a / a / (a / (b / (a / a / a / c))) / c = b`.  This axiom is sufficient to define inverses
and multiplication, and to prove that the type forms a group.

This class is named `OneGroup2` because there is only one defining axiom.
-/
class OneGroup2 (G : Type) extends Div G where
  /-- The defining axiom for a `OneGroup2`. -/
  one_axiom (a b c : G) : a / a / (a / (b / (a / a / a / c))) / c = b

namespace OneGroup2

instance [Group G] : OneGroup2 G where
  one_axiom a b c := by
    have := @div_eq_mul_one_div G _
    simp_all
    group

variable [OneGroup2 G]

/-- Left surjectivity of division in a `OneGroup2`. -/
theorem div_left_surj (a b : G) : ∃ (c : G), c / a = b := by
  exists a / a / (a / (b / (a / a / a / a)))
  exact OneGroup2.one_axiom _ _ _

/-- Right injectivity of division in a `OneGroup2`. -/
theorem div_right_inj (a b c : G) : (a / b = a / c) → b = c := by
  intro
  have ⟨x, _⟩ := div_left_surj (a / a / a / a) b
  have ⟨y, _⟩ := div_left_surj (a / a / a / a) c
  have := OneGroup2.one_axiom a x a
  have := OneGroup2.one_axiom a y a
  simp_all

theorem aux_one_group (a b c : G) : (∀ (x y : G), (x / c = y / c → x = y)) →
  a / ((a / a / b / c) / (a / a / a / c)) = b := by
  intro h
  have h₁ := OneGroup2.one_axiom a (a / a / b / c) c
  exact (div_right_inj _ _ _) ((h _ _) h₁)

theorem div_left_inj_special (a b c d : G) : c / (a / a / a / b) = d / (a / a / a / b) → c = d := by
  intro
  have := OneGroup2.one_axiom a c b
  have := OneGroup2.one_axiom a d b
  simp_all

/-- Right surjectivity of division in a `OneGroup2`. -/
theorem div_right_surj (a b : G) : ∃ (c : G), a / c = b := by
  let c := a / a / a / a
  exists ((a / a / b / c) / (a / a / a / c))
  exact aux_one_group _ _ _ (div_left_inj_special a a · · )

/-- Left injectivity of division in a `OneGroup2`. -/
theorem div_left_inj (a b c : G) : b / a = c / a → b = c := by
  have ⟨x, _⟩ := div_right_surj (a / a / a) a
  have := div_left_inj_special a x b c
  simp_all

end OneGroup2
