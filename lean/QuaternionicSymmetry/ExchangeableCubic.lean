import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! A finite algebra identity for a permutation-invariant cubic moment tensor. -/

namespace QuaternionicSymmetry.ExchangeableCubic

open scoped BigOperators

variable {κ S : Type*} [Fintype κ] [DecidableEq κ] [CommRing S]

omit [DecidableEq κ] in
theorem cube_sum (y x : κ → S) :
    (∑ i, y i * x i) ^ 3 =
      ∑ i, ∑ j, ∑ k, y i * y j * y k * (x i * x j * x k) := by
  simp only [pow_succ, pow_zero, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem sum_pattern (y : κ → S) (a b c : S) :
    (∑ i, ∑ j, ∑ k, y i * y j * y k *
      (c + (if i = j then b - c else 0) + (if i = k then b - c else 0) +
        (if j = k then b - c else 0) +
        (if i = j ∧ j = k then a - 3 * b + 2 * c else 0))) =
      c * (∑ i, y i) ^ 3 + 3 * (b - c) * (∑ i, y i) * (∑ i, y i ^ 2) +
        (a - 3 * b + 2 * c) * ∑ i, y i ^ 3 := by
  simp only [ite_and, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
  ring_nf
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring

end QuaternionicSymmetry.ExchangeableCubic
