import QuaternionicSymmetry.ComplexGaussianProduct
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.MvPolynomial.Funext

/-! Factorial coefficientwise moments for the concrete finite complex Gaussian product. -/

namespace QuaternionicSymmetry.ComplexGaussianPolynomial

open scoped BigOperators
open MeasureTheory
open MvPolynomial

noncomputable section

variable {β S T : Type*} [Fintype β] [CommRing S] [Algebra ℝ S]
  [CommRing T] [Algebra ℝ T]

def monomialMoment (d : β →₀ ℕ) : ℝ :=
  ∏ i, (d i).factorial

def expectation : MvPolynomial β S →ₗ[S] S :=
  Finsupp.linearCombination S (fun d => algebraMap ℝ S (monomialMoment d))

@[simp] theorem expectation_monomial (d : β →₀ ℕ) (a : S) :
    expectation (MvPolynomial.monomial d a) =
      a * algebraMap ℝ S (monomialMoment d) := by
  exact Finsupp.linearCombination_single _ _ _

theorem expectation_map (f : S →ₐ[ℝ] T) (p : MvPolynomial β S) :
    f (expectation p) = expectation (MvPolynomial.map f.toRingHom p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial d a => simp
  | add p q hp hq => simp [hp, hq]

private theorem normSq_pow_eq_norm_even (z : ℂ) (n : ℕ) :
    (‖z‖ ^ 2) ^ n = ‖z‖ ^ (2 * n) := by
  rw [← pow_mul]

private theorem eval_monomial_integrand (d : β →₀ ℕ) (c : ℝ) :
    (fun ω : β → Fin 2 → ℝ =>
      (MvPolynomial.monomial d c).eval
        (fun j => ‖ComplexGaussianProduct.vector ω j‖ ^ 2)) =
      (fun ω => c * ∏ j, ‖ComplexGaussianProduct.vector ω j‖ ^ (2 * d j)) := by
  funext ω
  simp only [MvPolynomial.eval_monomial, Finsupp.prod_pow]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  exact normSq_pow_eq_norm_even _ _

theorem monomial_integrable (d : β →₀ ℕ) (c : ℝ) :
    Integrable (fun ω : β → Fin 2 → ℝ =>
      (MvPolynomial.monomial d c).eval
        (fun j => ‖ComplexGaussianProduct.vector ω j‖ ^ 2))
      ComplexGaussianProduct.standardProductMeasure := by
  rw [eval_monomial_integrand]
  exact (ComplexGaussianProduct.norm_moment_integrable d).const_mul c

theorem integral_monomial (d : β →₀ ℕ) (c : ℝ) :
    (∫ ω : β → Fin 2 → ℝ,
      (MvPolynomial.monomial d c).eval
        (fun j => ‖ComplexGaussianProduct.vector ω j‖ ^ 2)
      ∂ComplexGaussianProduct.standardProductMeasure) =
      c * ∏ i, (d i).factorial := by
  rw [eval_monomial_integrand, integral_const_mul,
    ComplexGaussianProduct.integral_norm_moment]

theorem polynomial_integrable (p : MvPolynomial β ℝ) :
    Integrable (fun ω : β → Fin 2 → ℝ =>
      p.eval (fun j => ‖ComplexGaussianProduct.vector ω j‖ ^ 2))
      ComplexGaussianProduct.standardProductMeasure := by
  induction p using MvPolynomial.induction_on' with
  | monomial d c => exact monomial_integrable d c
  | add p q hp hq => simpa only [MvPolynomial.eval_add] using hp.add hq

theorem integral_polynomial (p : MvPolynomial β ℝ) :
    (∫ ω : β → Fin 2 → ℝ,
      p.eval (fun j => ‖ComplexGaussianProduct.vector ω j‖ ^ 2)
      ∂ComplexGaussianProduct.standardProductMeasure) =
      expectation p := by
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
      simpa [monomialMoment] using integral_monomial d c
  | add p q hp hq =>
      simp only [map_add]
      rw [integral_add (polynomial_integrable p) (polynomial_integrable q), hp, hq]

end
end QuaternionicSymmetry.ComplexGaussianPolynomial
