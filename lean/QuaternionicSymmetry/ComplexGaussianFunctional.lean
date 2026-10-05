import QuaternionicSymmetry.ComplexGaussianPolynomial

/-! Actual complex Gaussian integration after a real-linear functional on
an arbitrary commutative real coefficient algebra. -/

namespace QuaternionicSymmetry.ComplexGaussianFunctional

open MeasureTheory
open ComplexGaussianPolynomial ComplexGaussianProduct
open scoped BigOperators

noncomputable section

variable {β S : Type*} [Fintype β] [CommRing S] [Algebra ℝ S]

private theorem apply_scalar (L : S →ₗ[ℝ] ℝ) (c : S) (r : ℝ) :
    L (c * algebraMap ℝ S r) = L c * r := by
  rw [mul_comm c, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm r]

private theorem eval_monomial (L : S →ₗ[ℝ] ℝ) (d : β →₀ ℕ) (c : S)
    (ω : β → Fin 2 → ℝ) :
    L (MvPolynomial.eval (fun i => algebraMap ℝ S (‖vector ω i‖ ^ 2))
      (MvPolynomial.monomial d c)) =
      MvPolynomial.eval (fun i => ‖vector ω i‖ ^ 2) (MvPolynomial.monomial d (L c)) := by
  simp only [MvPolynomial.eval_monomial, Finsupp.prod_pow]
  simp only [← map_pow, ← map_prod]
  exact apply_scalar L c _

theorem polynomial_integrable (L : S →ₗ[ℝ] ℝ) (p : MvPolynomial β S) :
    Integrable (fun ω : β → Fin 2 → ℝ =>
      L (p.eval (fun i => algebraMap ℝ S (‖vector ω i‖ ^ 2)))) standardProductMeasure := by
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
      simp_rw [eval_monomial]
      exact ComplexGaussianPolynomial.monomial_integrable d (L c)
  | add p q hp hq =>
      simp only [map_add]
      exact hp.add hq

theorem integral_polynomial (L : S →ₗ[ℝ] ℝ) (p : MvPolynomial β S) :
    (∫ ω : β → Fin 2 → ℝ,
      L (p.eval (fun i => algebraMap ℝ S (‖vector ω i‖ ^ 2))) ∂standardProductMeasure) =
      L (expectation p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
      simp_rw [eval_monomial]
      rw [ComplexGaussianPolynomial.integral_monomial, expectation_monomial, apply_scalar]
      simp only [monomialMoment, Nat.cast_prod]
  | add p q hp hq =>
      simp only [map_add]
      rw [integral_add (polynomial_integrable L p) (polynomial_integrable L q), hp, hq]

theorem expectation_nonneg (L : S →ₗ[ℝ] ℝ) (p : MvPolynomial β S)
    (hp : ∀ ω : β → Fin 2 → ℝ,
      0 ≤ L (p.eval (fun i => algebraMap ℝ S (‖vector ω i‖ ^ 2)))) :
    0 ≤ L (expectation p) := by
  rw [← integral_polynomial]
  exact integral_nonneg hp

end
end QuaternionicSymmetry.ComplexGaussianFunctional
