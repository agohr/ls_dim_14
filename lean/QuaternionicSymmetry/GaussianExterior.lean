import QuaternionicSymmetry.GaussianFunctional
import QuaternionicSymmetry.GaussianWick
import QuaternionicSymmetry.EvenForms

/-! Actual scalar Gaussian integrals of exterior expressions.

The linear functional may, for example, extract an oriented top-degree
coefficient after multiplication by a fixed form. No norm on the exterior
algebra, and no order on differential forms, is assumed.
-/

namespace QuaternionicSymmetry.GaussianExterior

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module ℝ V]

abbrev standardMeasure : Measure (ι → ℝ) := GaussianAlgebra.standardMeasure

def combination (θ : ι → ExteriorAlgebra.exteriorPower ℝ 2 V) (ω : ι → ℝ) :
    ExteriorAlgebra ℝ V := ∑ i, ω i • (θ i : ExteriorAlgebra ℝ V)

private def restrict (L : ExteriorAlgebra ℝ V →ₗ[ℝ] ℝ) :
    EvenForms.evenSubalgebra ℝ V →ₗ[ℝ] ℝ :=
  L.comp (EvenForms.evenSubalgebra ℝ V).val.toLinearMap

omit [DecidableEq ι] in
private theorem combination_coe (θ : ι → ExteriorAlgebra.exteriorPower ℝ 2 V)
    (ω : ι → ℝ) :
    (GaussianFunctional.combination (S := EvenForms.evenSubalgebra ℝ V)
      (fun i => EvenForms.ofTwoForm (θ i)) ω :
      ExteriorAlgebra ℝ V) = combination θ ω := by
  simp [GaussianFunctional.combination, combination]

theorem integral_square (L : ExteriorAlgebra ℝ V →ₗ[ℝ] ℝ)
    (θ : ι → ExteriorAlgebra.exteriorPower ℝ 2 V) :
    (∫ ω : ι → ℝ, L (combination θ ω ^ 2) ∂standardMeasure) =
      L (∑ i, (θ i : ExteriorAlgebra ℝ V) ^ 2) := by
  have h := GaussianFunctional.integral_square (restrict L)
    (fun i => EvenForms.ofTwoForm (θ i))
  simpa [restrict, LinearMap.comp_apply, ← combination_coe] using h

theorem integral_fourth (L : ExteriorAlgebra ℝ V →ₗ[ℝ] ℝ)
    (θ : ι → ExteriorAlgebra.exteriorPower ℝ 2 V) :
    (∫ ω : ι → ℝ, L (combination θ ω ^ 4) ∂standardMeasure) =
      L (3 * (∑ i, (θ i : ExteriorAlgebra ℝ V) ^ 2) ^ 2) := by
  have h := GaussianFunctional.integral_fourth (restrict L)
    (fun i => EvenForms.ofTwoForm (θ i))
  simpa [restrict, LinearMap.comp_apply, ← combination_coe] using h

omit [DecidableEq ι] in
theorem combination_power_integrable (L : ExteriorAlgebra ℝ V →ₗ[ℝ] ℝ)
    (θ : ι → ExteriorAlgebra.exteriorPower ℝ 2 V) (n : ℕ) :
    Integrable (fun ω : ι → ℝ => L (combination θ ω ^ n)) standardMeasure := by
  have h := GaussianWick.combination_power_integrable (restrict L)
    (fun i => EvenForms.ofTwoForm (θ i)) n
  simpa [restrict, LinearMap.comp_apply, ← combination_coe] using h

/-- Wick's identity for actual exterior two-forms, tested by any real-linear functional. -/
theorem integral_even (L : ExteriorAlgebra ℝ V →ₗ[ℝ] ℝ)
    (θ : ι → ExteriorAlgebra.exteriorPower ℝ 2 V) (k : ℕ) :
    (∫ ω : ι → ℝ, L (combination θ ω ^ (2 * k)) ∂standardMeasure) =
      (Nat.doubleFactorial (2 * k - 1) : ℝ) *
        L ((∑ i, (θ i : ExteriorAlgebra ℝ V) ^ 2) ^ k) := by
  have h := GaussianWick.integral_combination_even (restrict L)
    (fun i => EvenForms.ofTwoForm (θ i)) k
  simpa [restrict, LinearMap.comp_apply, ← combination_coe] using h

theorem sum_squares_power_nonneg (L : ExteriorAlgebra ℝ V →ₗ[ℝ] ℝ)
    (θ : ι → ExteriorAlgebra.exteriorPower ℝ 2 V) (k : ℕ)
    (h : ∀ t : ι → ℝ, 0 ≤ L (combination θ t ^ (2 * k))) :
    0 ≤ L ((∑ i, (θ i : ExteriorAlgebra ℝ V) ^ 2) ^ k) := by
  have hi := GaussianWick.sum_squares_power_nonneg (restrict L)
    (fun i => EvenForms.ofTwoForm (θ i)) k
  have h' : ∀ t : ι → ℝ, 0 ≤ (restrict L)
      (GaussianFunctional.combination (fun i => EvenForms.ofTwoForm (θ i)) t ^ (2 * k)) := by
    intro t
    simpa [restrict, LinearMap.comp_apply, ← combination_coe] using h t
  simpa [restrict, LinearMap.comp_apply, ← combination_coe] using hi h'

end
end QuaternionicSymmetry.GaussianExterior
