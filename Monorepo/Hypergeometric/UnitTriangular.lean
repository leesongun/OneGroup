import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Tactic

abbrev UpperIndex := {s : ℕ × ℕ // s.1 ≤ s.2}
abbrev UpperTriangularMatrix (R : Type*) := UpperIndex → R

namespace UpperTriangularMatrix

variable {F : Type*}

@[simps] instance [Zero F] [One F] : One (UpperTriangularMatrix F) where
  one x := if x.1.1 = x.1.2 then 1 else 0

@[simps] instance [Ring F] : Mul (UpperTriangularMatrix F) where
  mul A B x := ∑ k ∈ (Finset.Icc x.1.1 x.1.2).attach,
    A ⟨⟨x.1.1, k⟩, by aesop⟩ * B ⟨⟨k, x.1.2⟩, by aesop⟩

def one_apply := @instOneOfZero_one
def mul_apply := @instMulOfRing_mul

lemma one_mul [Ring F] (A : UpperTriangularMatrix F) : 1 * A = A := by
  -- Finset.sum_boole_mul
  funext ⟨⟨fst, _⟩, _⟩
  simp only [mul_apply, one_apply]
  rw [Finset.sum_eq_single_of_mem ⟨fst, by aesop⟩]
  repeat aesop

lemma mul_assoc [r : Ring F] (A B C : UpperTriangularMatrix F) :
  A * B * C = A * (B * C) := by
  funext
  simp only [mul_apply]
  conv =>
    congr
    · enter [2, x]
      rw[Finset.sum_mul]
    · enter [2, x]
      rw[Finset.mul_sum]
      enter [2, x]
      rw[← r.mul_assoc]
  rw[Finset.sum_sigma']
  rw[Finset.sum_sigma']
  apply Finset.sum_bij'
    (fun ⟨⟨a, _⟩, ⟨b, _⟩ ⟩ _ => ⟨⟨b, by aesop; linarith⟩, ⟨a, by aesop⟩⟩)
    (fun ⟨⟨a, _⟩, ⟨b, _⟩ ⟩ _ => ⟨⟨b, by aesop; linarith⟩, ⟨a, by aesop⟩⟩)
  repeat aesop

end UpperTriangularMatrix

abbrev UnitUpperTriangularMatrix F [One F] :=
  {m : UpperTriangularMatrix F // ∀ x : ℕ, m ⟨⟨x, x⟩, le_refl _⟩ = 1}

notation "UT(" F ")" => UnitUpperTriangularMatrix F

-- Coercion to the underlying function type
instance [One F] : Coe (UnitUpperTriangularMatrix F) (UpperTriangularMatrix F) where
  coe := (·.1)

namespace UnitUpperTriangularMatrix

/-- The identity matrix is unit upper triangular. -/
@[simps] instance [Zero F] [One F] : One (UT(F)) where
  one := ⟨1, by simp⟩

@[simps] instance [Ring F] : Mul (UT(F)) where
  mul A B := ⟨↑A * ↑B, by
    intro n
    have : (Finset.Icc n n).attach = {⟨n, by simp⟩} := by aesop
    simp_all [A.2, B.2]
  ⟩

section Inverse

variable [Ring F] (A : UT(F))

def inv_rec (i j : ℕ) : i ≤ j → F := fun _ =>
  if i = j then 1
  else - (Finset.Ico i j).attach.sum fun k =>
    inv_rec i k (by aesop) * A.1 ⟨⟨k, j⟩, Nat.le_of_lt (by aesop)⟩
decreasing_by aesop

private lemma attach_sum_eq [AddCommMonoid β]
  {x y : Finset α} {f : {t : α // t ∈ x} → β} (h : y = x)
  : x.attach.sum f = y.attach.sum (fun ⟨a, h⟩ => f ⟨a, by simp_all⟩)
  := by aesop

private lemma inv_sum_aux (i j : ℕ) : i < j → 0 =
  (Finset.Icc i j).attach.sum fun k =>
    inv_rec A i k (by aesop) * A.1 ⟨⟨k, j⟩, by aesop⟩ := by
  intro h
  simp [attach_sum_eq $ Finset.Ico_insert_right $ Nat.le_of_succ_le h,
    Finset.attach_insert, Finset.sum_insert, A.2]
  rw [inv_rec]
  simp [Nat.ne_of_lt h]

instance : Inv (UT(F)) where
  inv A := ⟨fun x => inv_rec A x.1.1 x.1.2 x.2, by simp [inv_rec]⟩

lemma inv_mul_cancel : (Inv.inv A * A) = 1 := by
  ext ⟨⟨a, b⟩, h⟩
  simp [Nat.le_iff_lt_or_eq] at h
  cases h
  · have := inv_sum_aux A a b (by assumption)
    aesop
  · have := (Inv.inv A * A).2 a
    simp_all

end Inverse

def instGroup [Ring F] :=
  @Group.ofLeftAxioms UT(F) _ _ _
  (by intros; ext : 1; exact UpperTriangularMatrix.mul_assoc _ _ _)
  (by intros; ext : 1; exact UpperTriangularMatrix.one_mul _)
  inv_mul_cancel
