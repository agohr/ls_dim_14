import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-! Top powers of sums of commuting cubic-nilpotent elements.

This supplies the multinomial step for two-forms supported on separate
four-dimensional blocks. No exterior identity is assumed in this file.
-/

namespace QuaternionicSymmetry.CubicNilpotentSum

open scoped BigOperators

variable {ι R : Type*} [CommSemiring R]

def topCoefficient : ℕ → ℕ
  | 0 => 1
  | n + 1 => (2 * n + 2).choose 2 * topCoefficient n

theorem sum_pow_vanishes (s : Finset ι) (x : ι → R) (hx : ∀ i ∈ s, x i ^ 3 = 0) :
    (∑ i ∈ s, x i) ^ (2 * s.card + 1) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
      exact (Commute.all _ _).add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero
        (hx a (by simp)) (ih (fun i hi => hx i (by simp [hi]))) (by omega)

theorem top_power (s : Finset ι) (x : ι → R) (hx : ∀ i ∈ s, x i ^ 3 = 0) :
    (∑ i ∈ s, x i) ^ (2 * s.card) = (topCoefficient s.card : R) * ∏ i ∈ s, x i ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [topCoefficient]
  | @insert a s ha ih =>
      have hxs : ∀ i ∈ s, x i ^ 3 = 0 := fun i hi => hx i (by simp [hi])
      have hxa : x a ^ 3 = 0 := hx a (by simp)
      have hz := sum_pow_vanishes s x hxs
      rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, Finset.prod_insert ha]
      rw [show 2 * (s.card + 1) = 2 * s.card + 2 by omega, add_pow]
      rw [Finset.sum_eq_single 2]
      · rw [show 2 * s.card + 2 - 2 = 2 * s.card by omega, ih hxs]
        simp only [topCoefficient, Nat.cast_mul]
        ring
      · intro i _ hi
        by_cases hlarge : 3 ≤ i
        · rw [pow_eq_zero_of_le hlarge hxa, zero_mul, zero_mul]
        · have hsmall : i ≤ 1 := by omega
          rw [pow_eq_zero_of_le (by omega : 2 * s.card + 1 ≤ 2 * s.card + 2 - i) hz,
            mul_zero, zero_mul]
      · intro h
        exact (h (by simp)).elim

end QuaternionicSymmetry.CubicNilpotentSum
