import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

variable [Group G] (f : G → ℝ)

-- The axioms:
axiom norm_mul x y : f (x * y) ≤ f x + f y
axiom norm_sq x    : f (x ^ 2) ≥ 2 * f x - 1

-- should we remove n - 0 and use Nat.twoStepInduction?
lemma pow_upper x (k : ℕ) : f (x ^ k) ≤ k * f x + f 1:= by
  induction k with
  | zero => simp
  | succ n ih =>
    calc f (x ^ (n + 1)) = f (x ^ n * x) := by rw[pow_succ]
      _ ≤ f (x ^ n) + f x := by exact norm_mul _ _ _
      _ ≤ (n * f x + f 1) + f x := by simp_all
      _ = (n + 1) * f x + f 1 := by ring
    simp

lemma pow_lower x k : f (x^(2^k)) ≥ (2^k) * f x + 1 - (2^k) := by
  induction k with
  | zero => simp
  | succ n ih =>
    calc f (x ^ (2 ^ (n + 1))) = f ((x ^ (2 ^ n)) ^ 2) := by simp_all[pow_succ, pow_mul]
      _ ≥ 2 * f (x ^ (2 ^ n)) - 1 := norm_sq _ _
      _ ≥ 2 * ((2 ^ n) * f x + 1 - 2 ^ n) - 1 := by simp_all
      _ = (2 ^ (n + 1)) * f x + 1 - (2 ^ (n + 1)) := by ring

lemma rearrange x k : f x ≤ f (x ^ (2 ^ k))/(2 ^ k) + 1 := by
  suffices 0 ≤ (f (x ^ (2 ^ k)) + 2^k - 2^k * f x)/(2^k) by
    ring_nf at *
    simp_all
    linarith
  apply div_nonneg
  · linarith[pow_lower f x k]
  · simp

@[simp] lemma conj_pow (x y : G) (n : ℕ) : (y * x * y⁻¹)^n = y * (x^n) * y⁻¹ := by
  induction n with
  | zero      => simp
  | succ _ ih => rw [pow_succ, ih]; group

lemma aux_lemma_real_bound (x y : ℝ) : (∀(n:ℕ), (2^n) * x ≤ y) → x ≤ 0 := by
  intro hv
  by_contra h
  simp_all
  have ⟨n, hn⟩ := exists_lt_nsmul h y
  have _ : y < y := by
    calc
    y < n • x := hn
    _ < 2^n • x := nsmul_lt_nsmul_left h Nat.lt_two_pow_self
    _ = 2^n * x := by simp
    _ ≤ y := hv n
  simp_all

lemma approx_conjugation (x y : G) : f (y * x * y⁻¹) ≤ f x + 1 := by
  suffices f (y * x * y⁻¹) - 1 - f x ≤ 0 by simp_all
  apply aux_lemma_real_bound _ (f 1 + f y + f y⁻¹ - 1)
  intro k
  suffices 2^k * f (y * x * y⁻¹) - 2^k + 1 ≤ f y + (2^k * f x + f 1) + f y⁻¹ by ring_nf at *; linarith
  calc
    2^k * f (y * x * y⁻¹) - 2^k + 1
      ≤ f ((y * x * y⁻¹)^(2^k)) := by linarith[pow_lower f (y * x * y⁻¹) k]
    _ = f (y * (x^(2^k)) * y⁻¹) := by rw[conj_pow]
    _ ≤ f (y * x^(2^k)) + f y⁻¹ := norm_mul _ _ _
    _ ≤ f y + f (x^(2^k)) + f y⁻¹  := by simp[norm_mul]
    _ ≤ f y + (2^k * f x + f 1) + f y⁻¹ := by
      have := pow_upper f x (2^k)
      simpa

section splitting_lemma
variable (n : ℕ)

lemma aux_lemma_ind s t w y z : f ((w * y)^n * s⁻¹ * t * (z * w⁻¹)^n) ≤ f (s⁻¹ * t) + n * (f y + f z + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
  calc
    f ((w * y)^(k + 1) * s⁻¹ * t * (z * w⁻¹)^(k + 1))
    _ = f ((w * y)^(1 + k) * s⁻¹ * t * (z * w⁻¹)^(k + 1)) := by ring_nf
    _ = f (((w * y) * (w * y)^k) * s⁻¹ * t * ((z * w⁻¹)^k * (z * w⁻¹))) := by simp [pow_add]
    _ = f (w * (y * ((w * y)^k * s⁻¹ * t * (z * w⁻¹)^k) * z) * w⁻¹) := by group
    _ ≤ f (y * ((w * y)^k * s⁻¹ * t * (z * w⁻¹)^k) * z) + 1 := approx_conjugation _ _ _
    _ ≤ f (y * ((w * y)^k * s⁻¹ * t * (z * w⁻¹)^k)) + f z + 1 := by simp[norm_mul]
    _ ≤ f y + f ((w * y)^k * s⁻¹ * t * (z * w⁻¹)^k) + f z + 1 := by simp[norm_mul]
    _ ≤ f y + (f (s⁻¹ * t) + k * (f y + f z + 1)) + f z + 1 := by linarith[ih]
    _ = f (s⁻¹ * t) + (k + 1) * (f y + f z + 1) := by ring
  simp

lemma aux_lemma_bound_fx : (x = s * w * y * s⁻¹) → (x = t * z * w⁻¹ * t⁻¹) →
  2 ^ (n + 1) * f x - 2 ^ (n + 1) ≤ (2 ^ n) * (f y + f z + 1) + (f s + f t⁻¹ + f (s⁻¹ * t)) := by
  intros
  calc
    2 ^ (n + 1) * f x - 2 ^ (n + 1)
    _ ≤ f (x ^ 2 ^ (n + 1)) := by linarith[pow_lower f x (n+1)]
    _ = f (x ^ 2 ^ n * x ^ 2 ^ n) := by simp [pow_add, pow_mul, pow_two]
    _ = f ((s * w * y * s⁻¹) ^ 2 ^ n * (t * z * w⁻¹ * t⁻¹) ^ 2 ^ n)  := by simp_all
    _ = f ((s * (w * y) * s⁻¹) ^ 2 ^ n * (t * (z * w⁻¹) * t⁻¹) ^ 2 ^ n) := by group
    _ = f ((s * (w * y) ^ (2 ^ n) * s⁻¹)  * (t * (z * w⁻¹) ^ (2 ^ n) * t⁻¹)) := by simp_all[conj_pow]
    _ = f (s * ((w * y) ^ (2 ^ n) * s⁻¹ * t * (z * w⁻¹) ^ (2 ^ n)) * t⁻¹) := by group
    _ ≤ f (s * ((w * y) ^ (2 ^ n) * s⁻¹ * t * (z * w⁻¹) ^ (2 ^ n))) + f t⁻¹ := by simp[norm_mul]
    _ ≤ f s + f ((w * y) ^ (2 ^ n) * s⁻¹ * t * (z * w⁻¹) ^ (2 ^ n)) + f t⁻¹ := by simp[norm_mul]
    _ ≤ f s + (f (s⁻¹ * t) + (2 ^ n) * (f y + f z + 1)) + f t⁻¹ := by
      have := aux_lemma_ind f (2^n) s t w y z
      simp_all
    _ = (2 ^ n) * (f y + f z + 1) + (f s + f t⁻¹ + f (s⁻¹ * t)) := by ring

end splitting_lemma

lemma splitting_lemma x y z w s t
  (h₁ : x = s * w * y * s⁻¹)
  (h₂ : x = t * z * w⁻¹ * t⁻¹) :
  2 * f x ≤ f y + f z + 3 := by
  suffices 2 * f x - f y - f z - 3 ≤ 0 by linarith
  apply aux_lemma_real_bound _ (f s + f t⁻¹ + f (s⁻¹ * t))
  intro n
  have := aux_lemma_bound_fx f n h₁ h₂
  simp_all[pow_add]
  linarith

-- don't do this yet!
theorem polymath14 x y : f (x * y * x⁻¹ * y⁻¹) ≤ 5 :=
sorry
