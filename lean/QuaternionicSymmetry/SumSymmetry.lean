import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

namespace QuaternionicSymmetry

/-- Symmetrizing a bilinear coefficient does not change its quadratic sum. -/
theorem sum_symmetrized {α : Type*} (s : Finset α) (x : α → ℝ)
    (f : α → α → ℝ) :
    (∑ a ∈ s, ∑ b ∈ s, x a * ((f a b + f b a) / 2) * x b) =
      ∑ a ∈ s, ∑ b ∈ s, x a * f a b * x b := by
  have hswap :
      (∑ a ∈ s, ∑ b ∈ s, x a * f b a * x b) =
        ∑ a ∈ s, ∑ b ∈ s, x a * f a b * x b := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  calc
    _ = ((∑ a ∈ s, ∑ b ∈ s, x a * f a b * x b) +
        (∑ a ∈ s, ∑ b ∈ s, x a * f b a * x b)) / 2 := by
      simp only [← Finset.sum_add_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := by rw [hswap]; ring

end QuaternionicSymmetry
