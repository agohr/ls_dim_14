import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! A bounded global C∞ real curve with the identity germ at zero. It
allows straight coordinate lines near a manifold point to be extended to
global smooth curves staying inside one prescribed chart ball. -/

namespace QuaternionicSymmetry.BoundedSmoothCurveGerm

open Metric Filter
open scoped ContDiff Topology
noncomputable section

theorem exists_bounded_identity_germ (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧
      φ =ᶠ[𝓝 (0 : ℝ)] id ∧
      ∀ t : ℝ, |φ t| < ε := by
  let b : ContDiffBump (0 : ℝ) :=
    ⟨ε / 4, ε / 2, by positivity, by nlinarith⟩
  let φ : ℝ → ℝ := fun t => b t * t
  refine ⟨φ, b.contDiff.mul contDiff_id, ?_, ?_⟩
  · filter_upwards [b.eventuallyEq_one] with t ht
    simp [φ, ht]
  · intro t
    by_cases ht : ε / 2 ≤ dist t (0 : ℝ)
    · have hb : b t = 0 := b.zero_of_le_dist ht
      simp [φ, hb, hε]
    · have hb0 : 0 ≤ b t := b.nonneg
      have hb1 : b t ≤ 1 := b.le_one
      have hbound : |b t * t| ≤ |t| := by
        rw [abs_mul, abs_of_nonneg hb0]
        exact mul_le_of_le_one_left (abs_nonneg t) hb1
      have hsmall : |t| < ε / 2 := by
        simpa [Real.dist_eq] using lt_of_not_ge ht
      exact lt_of_le_of_lt hbound (lt_trans hsmall (by linarith))

end
end QuaternionicSymmetry.BoundedSmoothCurveGerm
