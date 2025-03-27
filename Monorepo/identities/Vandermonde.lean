import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

open Finset Nat

theorem Vandermonde (a b t : ℕ) :
    ∑ k ∈ range (t + 1), (a.choose k) * (b.choose (t - k)) = (a + b).choose t := by

  let α := Fin a
  let β := Fin b

  let RHS := powersetCard t (univ : Finset (α ⊕ β))
  let LHS := (range (t + 1)).sigma fun k =>
    (powersetCard k (univ : Finset α)) ×ˢ (powersetCard (t - k) (univ : Finset β))

  suffices LHS.card = RHS.card by aesop

  apply card_nbij'
    (fun ⟨_, x, y⟩ => disjSum x y)
    (fun x => ⟨#(toLeft x), toLeft x, toRight x⟩)
  · intro ⟨_, x, _⟩
    suffices #x < t + 1 → #x + (t - #x) = t by aesop
    exact add_sub_of_le ∘ le_of_lt_succ
  · intro x
    have : #x.toLeft < #x + 1 :=
      lt_add_one_of_le card_toLeft_le
    have : #x.toRight = #x - #x.toLeft :=
      Nat.eq_sub_of_add_eq' card_toLeft_add_card_toRight
    aesop
  · aesop
  · aesop
