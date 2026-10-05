import QuaternionicSymmetry.PositiveRay
import QuaternionicSymmetry.GaussianFunctionalPolynomial
import QuaternionicSymmetry.ComplexGaussianFunctional

/-! Polynomial averaging preserves a nonnegative ray when every scalar
evaluation lies in that ray.  The hypotheses below are pointwise sign
conditions; no order or positivity structure is imposed on the coefficient
algebra. -/

namespace QuaternionicSymmetry.GaussianPositiveRay

open MeasureTheory
open GaussianPolynomialExpectation
open PositiveRay

noncomputable section

variable {β S : Type*} [Fintype β] [CommRing S] [Algebra ℝ S]

theorem expectation_contains
    {v : S} (hv : v ≠ 0) (p : MvPolynomial β S)
    (hp : ∀ ω : β → ℝ,
      PositiveRay.Contains v
        (p.eval (fun i => algebraMap ℝ S (ω i)))) :
    PositiveRay.Contains v (expectation p) := by
  apply (PositiveRay.contains_iff_functional_nonneg hv).mpr
  intro L hLv
  rw [← GaussianFunctionalPolynomial.integral_polynomial L p]
  apply integral_nonneg
  intro ω
  exact PositiveRay.functional_nonneg (hp ω) L hLv

theorem complex_expectation_contains
    {v : S} (hv : v ≠ 0) (p : MvPolynomial β S)
    (hp : ∀ ω : β → Fin 2 → ℝ,
      PositiveRay.Contains v
        (p.eval (fun i => algebraMap ℝ S
          (‖ComplexGaussianProduct.vector ω i‖ ^ 2)))) :
    PositiveRay.Contains v (ComplexGaussianPolynomial.expectation p) := by
  apply (PositiveRay.contains_iff_functional_nonneg hv).mpr
  intro L hLv
  apply ComplexGaussianFunctional.expectation_nonneg L p
  intro ω
  exact PositiveRay.functional_nonneg (hp ω) L hLv

end
end QuaternionicSymmetry.GaussianPositiveRay
