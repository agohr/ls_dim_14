import QuaternionicSymmetry.ComplexGaussianVariable

/-! Independent finite products of the concrete two-dimensional complex variable. -/

namespace QuaternionicSymmetry.ComplexGaussianProduct

open scoped BigOperators
open MeasureTheory

noncomputable section

variable {β : Type*} [Fintype β]

abbrev standardProductMeasure : Measure (β → Fin 2 → ℝ) :=
  Measure.pi (fun _ : β => GaussianPolynomialIntegration.standardMeasure)

def vector (ω : β → Fin 2 → ℝ) (j : β) : ℂ :=
  ComplexGaussianVariable.standardComplex (ω j)

theorem norm_moment_integrable (a : β → ℕ) :
    Integrable (fun ω : β → Fin 2 → ℝ =>
      ∏ j, ‖vector ω j‖ ^ (2 * a j)) standardProductMeasure := by
  letI : IsProbabilityMeasure
      (GaussianPolynomialIntegration.standardMeasure (ι := Fin 2)) := by
    unfold GaussianPolynomialIntegration.standardMeasure GaussianAlgebra.standardMeasure
    infer_instance
  letI : SigmaFinite
      (GaussianPolynomialIntegration.standardMeasure (ι := Fin 2)) := by
    unfold GaussianPolynomialIntegration.standardMeasure GaussianAlgebra.standardMeasure
    infer_instance
  change Integrable (fun ω : β → Fin 2 → ℝ =>
      ∏ j, ‖ComplexGaussianVariable.standardComplex (ω j)‖ ^ (2 * a j))
    (Measure.pi (fun _ : β => GaussianPolynomialIntegration.standardMeasure))
  refine Integrable.fintype_prod
    (f := fun (_ : β) (x : Fin 2 → ℝ) =>
      ‖ComplexGaussianVariable.standardComplex x‖ ^ (2 * a _) )
    (μ := fun _ : β => GaussianPolynomialIntegration.standardMeasure) ?_
  intro j
  exact ComplexGaussianVariable.standardComplex_norm_pow_integrable (a j)

theorem integral_norm_moment (a : β → ℕ) :
    (∫ ω : β → Fin 2 → ℝ,
      ∏ j, ‖vector ω j‖ ^ (2 * a j) ∂standardProductMeasure) =
      ∏ j, (a j).factorial := by
  letI : SigmaFinite
      (GaussianPolynomialIntegration.standardMeasure (ι := Fin 2)) := by
    unfold GaussianPolynomialIntegration.standardMeasure GaussianAlgebra.standardMeasure
    infer_instance
  change (∫ ω : β → Fin 2 → ℝ,
      ∏ j, ‖ComplexGaussianVariable.standardComplex (ω j)‖ ^ (2 * a j)
        ∂Measure.pi (fun _ : β => GaussianPolynomialIntegration.standardMeasure)) =
    ∏ j, (a j).factorial
  rw [MeasureTheory.integral_fintype_prod_eq_prod
    (fun (_ : β) (x : Fin 2 → ℝ) =>
      ‖ComplexGaussianVariable.standardComplex x‖ ^ (2 * a _))]
  simp_rw [ComplexGaussianVariable.integral_standardComplex_norm_pow]
  norm_num [Nat.cast_prod]

end
end QuaternionicSymmetry.ComplexGaussianProduct
