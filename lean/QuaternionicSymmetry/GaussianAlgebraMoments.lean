import QuaternionicSymmetry.GaussianAlgebraFourthMoment
import QuaternionicSymmetry.GaussianMomentPolynomials

/-! Algebra-valued Gaussian moments presently established by the finite-product proof. -/

namespace QuaternionicSymmetry.GaussianAlgebraMoments

open MeasureTheory
open scoped BigOperators NNReal

noncomputable section

variable {ι S : Type*} [Fintype ι] [DecidableEq ι]
  [NormedCommRing S] [NormedAlgebra ℝ S] [CompleteSpace S]

abbrev standardMeasure : Measure (ι → ℝ) := GaussianAlgebra.standardMeasure

def variance (θ : ι → S) : S := ∑ i, θ i ^ 2

omit [DecidableEq ι] in
theorem combination_moment_zero (θ : ι → S) :
    (∫ ω : ι → ℝ, GaussianAlgebra.combination θ ω ^ 0 ∂standardMeasure) =
      GaussianMomentPolynomials.moment 0 (variance θ) := by
  letI : IsProbabilityMeasure (standardMeasure (ι := ι)) := by
    dsimp [standardMeasure, GaussianAlgebra.standardMeasure]
    infer_instance
  simp [GaussianMomentPolynomials.moment, variance]

theorem combination_moment_two (θ : ι → S) :
    (∫ ω : ι → ℝ, GaussianAlgebra.combination θ ω ^ 2 ∂standardMeasure) =
      GaussianMomentPolynomials.moment 2 (variance θ) := by
  rw [GaussianAlgebra.integral_combination_square]
  simp [variance]

theorem combination_moment_four (θ : ι → S) :
    (∫ ω : ι → ℝ, GaussianAlgebra.combination θ ω ^ 4 ∂standardMeasure) =
      GaussianMomentPolynomials.moment 4 (variance θ) := by
  rw [GaussianAlgebraFourthMoment.integral_combination_fourth]
  simp [variance]

end
end QuaternionicSymmetry.GaussianAlgebraMoments
