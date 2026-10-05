import QuaternionicSymmetry.ComplexGaussianProduct
import QuaternionicSymmetry.ComplexMatrixRealification
import QuaternionicSymmetry.ComplexGaussianUnitaryInvariant
import Mathlib.MeasureTheory.Function.SpecialFunctions.RCLike

/-! Reindexing the finite product Gaussian law between curried and flat coordinates. -/

namespace QuaternionicSymmetry.GaussianProductCurry

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

variable {κ : Type*} [Fintype κ]

/-- Flatten a family of two-real-coordinate samples. -/
def uncurry (ω : κ → Fin 2 → ℝ) : κ × Fin 2 → ℝ :=
  fun p => ω p.1 p.2

omit [Fintype κ] in
private theorem measurable_uncurry :
    Measurable (uncurry : (κ → Fin 2 → ℝ) → κ × Fin 2 → ℝ) := by
  rw [measurable_pi_iff]
  intro p
  exact (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)

/-- Flattening a product of two-dimensional standard Gaussian laws gives the flat standard law. -/
theorem map_uncurry_standardProductMeasure :
    Measure.map uncurry (ComplexGaussianProduct.standardProductMeasure (β := κ)) =
      GaussianAlgebra.standardMeasure (ι := κ × Fin 2) := by
  letI : SigmaFinite (GaussianPolynomialIntegration.standardMeasure (ι := Fin 2)) := by
    unfold GaussianPolynomialIntegration.standardMeasure GaussianAlgebra.standardMeasure
    infer_instance
  apply (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply measurable_uncurry (MeasurableSet.univ_pi hs)]
  change Measure.pi (fun _ : κ => GaussianPolynomialIntegration.standardMeasure)
      (uncurry ⁻¹' Set.univ.pi s) =
    ∏ p, gaussianReal 0 1 (s p)
  have hpre : uncurry ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi, uncurry]
    constructor
    · intro h i _ j _
      exact h (i, j) (by simp)
    · intro h p _
      exact h p.1 (by simp) p.2 (by simp)
  rw [hpre]
  rw [Measure.pi_pi]
  simp only [GaussianPolynomialIntegration.standardMeasure, GaussianAlgebra.standardMeasure]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

omit [Fintype κ] in
private theorem measurable_flat_gaussianVector :
    Measurable (ComplexMatrixRealification.gaussianVector : (κ × Fin 2 → ℝ) → κ → ℂ) := by
  rw [measurable_pi_iff]
  intro i
  change Measurable (fun x : κ × Fin 2 → ℝ =>
    ComplexGaussianVariable.standardComplex (fun k => x (i, k)))
  have heq : (fun x : κ × Fin 2 → ℝ =>
      ComplexGaussianVariable.standardComplex (fun k => x (i, k))) =
      (fun x => ((x (i, 0) : ℂ) + (x (i, 1) : ℂ) * Complex.I) /
        (Real.sqrt 2 : ℂ)) := by
    funext x
    rw [ComplexGaussianVariable.standardComplex, Complex.mk_eq_add_mul_I]
  rw [heq]
  fun_prop

/-- The flat and curried constructions induce the same complex Gaussian vector law. -/
theorem map_flat_gaussianVector_standardMeasure :
    Measure.map ComplexMatrixRealification.gaussianVector
        (GaussianAlgebra.standardMeasure (ι := κ × Fin 2)) =
      Measure.map (fun ω i => ComplexGaussianProduct.vector ω i)
        (ComplexGaussianProduct.standardProductMeasure (β := κ)) := by
  rw [← map_uncurry_standardProductMeasure]
  rw [Measure.map_map measurable_flat_gaussianVector measurable_uncurry]
  congr 1

omit [Fintype κ] in
/-- The curried complex Gaussian vector map is measurable. -/
theorem measurable_vector :
    Measurable (fun ω : κ → Fin 2 → ℝ => fun i => ComplexGaussianProduct.vector ω i) := by
  convert measurable_flat_gaussianVector.comp measurable_uncurry using 1

/-- The unitary-invariant law is the pushforward of the curried product Gaussian law. -/
theorem unitary_standardMeasure_eq_map_vector :
    ComplexGaussianUnitaryInvariant.standardMeasure (κ := κ) =
      Measure.map (fun ω i => ComplexGaussianProduct.vector ω i)
        (ComplexGaussianProduct.standardProductMeasure (β := κ)) := by
  unfold ComplexGaussianUnitaryInvariant.standardMeasure
  exact map_flat_gaussianVector_standardMeasure

/-- The curried product variables have the finite unitary-invariant complex Gaussian law. -/
theorem vector_hasLaw :
    HasLaw (fun ω : κ → Fin 2 → ℝ => fun i => ComplexGaussianProduct.vector ω i)
      (ComplexGaussianUnitaryInvariant.standardMeasure (κ := κ))
      (ComplexGaussianProduct.standardProductMeasure (β := κ)) :=
  ⟨measurable_vector.aemeasurable, unitary_standardMeasure_eq_map_vector.symm⟩

end
end QuaternionicSymmetry.GaussianProductCurry
