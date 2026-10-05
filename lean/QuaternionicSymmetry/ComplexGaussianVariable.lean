import QuaternionicSymmetry.ComplexGaussianMoments
import Mathlib.Analysis.Complex.Norm

/-! A concrete complex Gaussian variable built from two real coordinates. -/

namespace QuaternionicSymmetry.ComplexGaussianVariable

open scoped BigOperators
open MeasureTheory

noncomputable section

def standardComplex (x : Fin 2 → ℝ) : ℂ :=
  (⟨x 0, x 1⟩ : ℂ) / (Real.sqrt 2 : ℂ)

@[simp] theorem normSq_standard (x : Fin 2 → ℝ) :
    Complex.normSq (standardComplex x) = (∑ i, x i ^ 2) / 2 := by
  rw [standardComplex, Complex.normSq_div, Complex.normSq_mk,
    Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num)]
  rw [Fin.sum_univ_two]
  ring

private theorem norm_pow_eq_radial (k : ℕ) (x : Fin 2 → ℝ) :
    ‖standardComplex x‖ ^ (2 * k) =
      ((∑ i, x i ^ 2) / 2) ^ k := by
  rw [pow_mul, Complex.sq_norm, normSq_standard]

theorem standardComplex_norm_pow_integrable (k : ℕ) :
    Integrable (fun x : Fin 2 → ℝ => ‖standardComplex x‖ ^ (2 * k))
      GaussianPolynomialIntegration.standardMeasure := by
  have hrad := GaussianRadialMoments.radial_pow_integrable (ι := Fin 2) k
  have hscaled := hrad.const_mul ((1 / (2 : ℝ)) ^ k)
  apply hscaled.congr
  filter_upwards [] with x
  rw [norm_pow_eq_radial]
  ring

theorem integral_standardComplex_norm_pow (k : ℕ) :
    (∫ x : Fin 2 → ℝ, ‖standardComplex x‖ ^ (2 * k)
      ∂GaussianPolynomialIntegration.standardMeasure) = (k.factorial : ℝ) := by
  rw [show (fun x : Fin 2 → ℝ => ‖standardComplex x‖ ^ (2 * k)) =
      (fun x => ((∑ i, x i ^ 2) / 2) ^ k) by
        funext x
        exact norm_pow_eq_radial k x]
  exact ComplexGaussianMoments.integral_radial_two (k := k)

theorem integral_standardComplex_norm_sq :
    (∫ x : Fin 2 → ℝ, ‖standardComplex x‖ ^ 2
      ∂GaussianPolynomialIntegration.standardMeasure) = 1 := by
  simpa using integral_standardComplex_norm_pow 1

end
end QuaternionicSymmetry.ComplexGaussianVariable
