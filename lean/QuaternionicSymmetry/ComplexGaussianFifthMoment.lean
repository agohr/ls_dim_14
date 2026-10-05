import QuaternionicSymmetry.ComplexGaussianFourthMoment

/-! The fifth factorial complex-radial moment of a weighted linear statistic. -/

namespace QuaternionicSymmetry.ComplexGaussianFifthMoment

open scoped BigOperators
open MvPolynomial ComplexGaussianPolynomial ComplexGaussianRadialMoments
open QuaternionicSymmetry.ComplexGaussianLinearMoments
open QuaternionicSymmetry.ComplexGaussianRecurrence

noncomputable section

variable {β S : Type*} [Fintype β] [DecidableEq β] [CommRing S] [Algebra ℝ S]

/-- The actual fifth factorial complex-radial moment, valid even for nilpotent
coefficient algebras. -/
theorem expectation_linear_fifth (θ : β → S) :
    expectation (linearPolynomial θ ^ 5) =
      (∑ i, θ i) ^ 5 + 10 * (∑ i, θ i) ^ 3 * (∑ i, θ i ^ 2) +
        15 * (∑ i, θ i) * (∑ i, θ i ^ 2) ^ 2 +
        20 * (∑ i, θ i) ^ 2 * (∑ i, θ i ^ 3) +
        20 * (∑ i, θ i ^ 2) * (∑ i, θ i ^ 3) +
        30 * (∑ i, θ i) * (∑ i, θ i ^ 4) +
        24 * ∑ i, θ i ^ 5 := by
  let θ2 : β → S := fun i => θ i ^ 2
  let θ3 : β → S := fun i => θ i ^ 3
  let θ4 : β → S := fun i => θ i ^ 4
  let θ5 : β → S := fun i => θ i ^ 5
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
  have hθ5 : pointwiseProduct θ4 θ = θ5 := by
    funext i
    simp only [pointwiseProduct, θ4, θ5]
    ring
  have h1 := expectation_linear_mul_pow_succ θ θ 3
  have h2 := expectation_linear_mul_pow_succ θ2 θ 2
  have h3 := expectation_linear_mul_pow_succ θ3 θ 1
  have h4 := expectation_linear_mul_pow_succ θ4 θ 0
  rw [hθ2] at h1
  rw [hθ3] at h2
  rw [hθ4] at h3
  rw [hθ5] at h4
  norm_num [nsmul_eq_mul] at h1 h2 h3 h4
  change expectation (linearPolynomial θ ^ 5) = _
  calc
    expectation (linearPolynomial θ ^ 5) =
        expectation (linearPolynomial θ * linearPolynomial θ ^ 4) := by
      congr 1
      ring
    _ = (∑ i, θ i) * expectation (linearPolynomial θ ^ 4) +
        4 * expectation (linearPolynomial θ2 * linearPolynomial θ ^ 3) := h1
    _ = (∑ i, θ i) * expectation (linearPolynomial θ ^ 4) +
        4 * ((∑ i, θ2 i) * expectation (linearPolynomial θ ^ 3) +
          3 * expectation (linearPolynomial θ3 * linearPolynomial θ ^ 2)) := by rw [h2]
    _ = (∑ i, θ i) * expectation (linearPolynomial θ ^ 4) +
        4 * ((∑ i, θ2 i) * expectation (linearPolynomial θ ^ 3) +
          3 * ((∑ i, θ3 i) * expectation (linearPolynomial θ ^ 2) +
            2 * expectation (linearPolynomial θ4 * linearPolynomial θ))) := by rw [h3]
    _ = (∑ i, θ i) * expectation (linearPolynomial θ ^ 4) +
        4 * ((∑ i, θ2 i) * expectation (linearPolynomial θ ^ 3) +
          3 * ((∑ i, θ3 i) * expectation (linearPolynomial θ ^ 2) +
            2 * ((∑ i, θ4 i) * expectation (linearPolynomial θ) +
              expectation (linearPolynomial θ5)))) := by rw [h4]
    _ = _ := by
      rw [ComplexGaussianFourthMoment.expectation_linear_fourth,
        expectation_linear_cube, expectation_linear_sq, expectation_linear,
        expectation_linear θ5]
      simp only [θ2, θ3, θ4, θ5]
      ring

end
end QuaternionicSymmetry.ComplexGaussianFifthMoment
