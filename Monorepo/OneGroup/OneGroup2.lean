import OneGroup.OneGroup

/--
A `OneGroup2` is a type equipped with a division operation `/` satisfying the single axiom
`a / a / (a / (b / (a / a / a / c))) / c = b`.  This axiom is sufficient to define inverses
and multiplication, and to prove that the type forms a group.

This class is named `OneGroup2` because there is only one defining axiom.
-/
class OneGroup2 (G : Type*) extends Div G where
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
def div_left_surj (a b : G) : {c : G // c / a = b} :=
  ⟨a / a / (a / (b / (a / a / a / a))), OneGroup2.one_axiom _ _ _⟩

/-- Right injectivity of division in a `OneGroup2`. -/
theorem div_right_inj (a b c : G) (_ : a / b = a / c) : b = c := by
  have ⟨x, _⟩ := div_left_surj (a / a / a / a) b
  have ⟨y, _⟩ := div_left_surj (a / a / a / a) c
  have := OneGroup2.one_axiom a x a
  have := OneGroup2.one_axiom a y a
  simp_all

theorem aux_one_group (a b c : G) (h : ∀ (x y : G), (x / c = y / c → x = y)) :
  a / ((a / a / b / c) / (a / a / a / c)) = b :=
  div_right_inj _ _ _ $ h _ _ $ OneGroup2.one_axiom _ _ _

/-- Left injectivity of division by `a / a / a / b` in a `OneGroup2`. -/
theorem div_left_inj_special (a b c d : G) (_ : c / (a / a / a / b) = d / (a / a / a / b)) : c = d := by
  have := OneGroup2.one_axiom a c b
  have := OneGroup2.one_axiom a d b
  simp_all

/-- Right surjectivity of division in a `OneGroup2`. -/
def div_right_surj (a b : G) : {c : G // a / c = b} :=
  let c := a / a / a / a
  ⟨(a / a / b / c) / (a / a / a / c), aux_one_group _ _ _ $ div_left_inj_special _ _⟩

/-- Left injectivity of division in a `OneGroup2`. -/
theorem div_left_inj (a b c : G) : b / a = c / a → b = c := by
  have ⟨x, _⟩ := div_right_surj (a / a / a) a
  have := div_left_inj_special a x b c
  simp_all

instance : OneGroup G where
  one_axiom _ _ _ := aux_one_group _ _ _ $ div_left_inj _

def instGroup G [OneGroup2 G] [Inhabited G] := OneGroup.instGroup G

end OneGroup2
