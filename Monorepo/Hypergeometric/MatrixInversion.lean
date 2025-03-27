import OneGroup.Hypergeometric.UnitTriangular

abbrev range (x : UpperIndex) := Finset.Ico x.1.1 x.1.2

/-- https://doi.org/10.1090/S0002-9939-05-07912-8 -/

structure Data (R : Type*) where
  f : ℕ → ℕ → R
  g : ℕ → ℕ → R

namespace Data

variable {R : Type*} [CommSemiring R] (a : Data R)

def matF : UT(R) :=
  ⟨fun x => (range x).prod fun k => a.f (k + 1) x.1.1 * a.g x.1.1 k, by simp⟩

def matG : UT(R) :=
  ⟨fun x => (range x).prod fun k => a.f k x.1.2 *
    if k + 1 ≠ x.1.2 then a.g x.1.2 (k + 1) else a.g x.1.1 x.1.1, by simp⟩

def lagrange (n : ℕ) (arg_f : Fin (n + 2) → ℕ) (arg_g : Fin n → ℕ)
  := (∑ i, ∏ j with j ≠ i, a.f (arg_f i) (arg_f j) * ∏ j, a.g (arg_f i) (arg_g j))

end Data

structure Assumptions (R : Type*) [CommSemiring R] extends Data R where
  lagrange_0 a_f a_g : Data.lagrange toData 0 a_f a_g = 0
  lagrange_1 a_f a_g : Data.lagrange toData 1 a_f a_g = 0

namespace Assumptions

variable {R : Type*} [CommSemiring R] (a : Assumptions R)

theorem antisymm x y : a.f x y + a.f y x = 0 := by
  let f (a : Fin 2) : Nat := if a = 0 then x else y
  have h := a.lagrange_0 f default
  unfold Data.lagrange at h
  let univ : Finset $ Fin 2 := Finset.univ
  have : univ.filter (fun j ↦ ¬j = 0) = {1} ∧ univ.filter (fun j ↦ ¬j = 1) = {0}
    := by native_decide
  aesop

theorem lagrange (n : ℕ) (arg_f : Fin (n + 2) → ℕ) (arg_g : Fin n → ℕ) :
  Data.lagrange a.toData n arg_f arg_g = 0 := by
  induction n using Nat.twoStepInduction
  · exact a.lagrange_0 arg_f arg_g
  · exact a.lagrange_1 arg_f arg_g
  sorry

end Assumptions

theorem matrix_inverse {R : Type*} [CommRing R] (a : Assumptions R)
  : Data.matF a.toData * Data.matG a.toData = 1 := sorry
