import QuaternionicSymmetry.ComplexGaussianRecurrence

/-! The fourth factorial complex-radial moment of a weighted linear statistic. -/

namespace QuaternionicSymmetry.ComplexGaussianFourthMoment

open scoped BigOperators
open MvPolynomial ComplexGaussianPolynomial ComplexGaussianRadialMoments
open QuaternionicSymmetry.ComplexGaussianLinearMoments
open QuaternionicSymmetry.ComplexGaussianRecurrence

noncomputable section

variable {β S : Type*} [Fintype β] [DecidableEq β] [CommRing S] [Algebra ℝ S]

/-- The fourth moment of a complex-radial linear statistic. -/
theorem expectation_linear_fourth (θ : β → S) :
    expectation (linearPolynomial θ ^ 4) =
      (∑ i, θ i) ^ 4 + 6 * (∑ i, θ i) ^ 2 * (∑ i, θ i ^ 2) +
        3 * (∑ i, θ i ^ 2) ^ 2 + 8 * (∑ i, θ i) * (∑ i, θ i ^ 3) +
          6 * ∑ i, θ i ^ 4 := by
  let θ2 : β → S := fun i => θ i ^ 2
  let θ3 : β → S := fun i => θ i ^ 3
  let θ4 : β → S := fun i => θ i ^ 4
  have hθ2 : pointwiseProduct θ θ = θ2 := by
    funext i
    simp only [pointwiseProduct, θ2]
    ring
  have hθ3 : pointwiseProduct θ2 θ = θ3 := by
    funext i
    simp only [pointwiseProduct, θ2, θ3]
    ring
  have hθ4 : pointwiseProduct θ3 θ = θ4 := by
    funext i
    simp only [pointwiseProduct, θ3, θ4]
    ring
  have h1 := expectation_linear_mul_pow_succ θ θ 2
  have h2 := expectation_linear_mul_pow_succ θ2 θ 1
  have h3 := expectation_linear_mul_pow_succ θ3 θ 0
  rw [hθ2] at h1
  rw [hθ3] at h2
  rw [hθ4] at h3
  norm_num [nsmul_eq_mul] at h1 h2 h3
  change expectation (linearPolynomial θ ^ 4) = _
  calc
    expectation (linearPolynomial θ ^ 4) =
        expectation (linearPolynomial θ * linearPolynomial θ ^ 3) := by
      congr 1
      ring
    _ = (∑ i, θ i) * expectation (linearPolynomial θ ^ 3) +
        3 * expectation (linearPolynomial θ2 * linearPolynomial θ ^ 2) := by
      exact h1
    _ = (∑ i, θ i) * expectation (linearPolynomial θ ^ 3) +
        3 * ((∑ i, θ2 i) * expectation (linearPolynomial θ ^ 2) +
          2 * expectation (linearPolynomial θ3 * linearPolynomial θ)) := by rw [h2]
    _ = (∑ i, θ i) * expectation (linearPolynomial θ ^ 3) +
        3 * ((∑ i, θ2 i) * expectation (linearPolynomial θ ^ 2) +
          2 * ((∑ i, θ3 i) * expectation (linearPolynomial θ) +
            expectation (linearPolynomial θ4))) := by rw [h3]
    _ = _ := by
      rw [expectation_linear_cube, expectation_linear_sq, expectation_linear]
      rw [expectation_linear θ4]
      simp only [θ2, θ3, θ4]
      ring

end
end QuaternionicSymmetry.ComplexGaussianFourthMoment
