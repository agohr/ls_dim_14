import QuaternionicSymmetry.ComplexMatrixRealification
import QuaternionicSymmetry.GaussianOrthogonalInvariant

/-!
  The normalized finite complex Gaussian vector law is invariant under unitary
  matrices, proved by realification and real orthogonal invariance.
-/

namespace QuaternionicSymmetry.ComplexGaussianUnitaryInvariant

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The finite normalized complex Gaussian-vector law. -/
def standardMeasure : Measure (κ → ℂ) :=
  Measure.map ComplexMatrixRealification.gaussianVector
    (GaussianAlgebra.standardMeasure (ι := κ × Fin 2))

omit [Fintype κ] [DecidableEq κ] in
private theorem measurable_gaussianVector :
    Measurable (ComplexMatrixRealification.gaussianVector : (κ × Fin 2 → ℝ) → κ → ℂ) := by
  rw [measurable_pi_iff]
  intro i
  unfold ComplexMatrixRealification.gaussianVector ComplexGaussianVariable.standardComplex
  change Measurable (fun x : κ × Fin 2 → ℝ =>
    (⟨x (i, 0), x (i, 1)⟩ : ℂ) / (Real.sqrt 2 : ℂ))
  have hp : Measurable (fun x : κ × Fin 2 → ℝ => (x (i, 0), x (i, 1))) :=
    (measurable_pi_apply (i, 0)).prodMk (measurable_pi_apply (i, 1))
  have hc : Measurable (fun x : κ × Fin 2 → ℝ =>
      Complex.measurableEquivRealProd.symm (x (i, 0), x (i, 1))) :=
    Complex.measurableEquivRealProd.symm.measurable.comp hp
  exact hc.div measurable_const

omit [DecidableEq κ] in
private theorem measurable_mulVec (U : Matrix κ κ ℂ) :
    Measurable (Matrix.mulVec U : (κ → ℂ) → κ → ℂ) := by
  rw [measurable_pi_iff]
  intro i
  simp only [Matrix.mulVec, dotProduct]
  fun_prop

omit [DecidableEq κ] in
private theorem measurable_transform (U : Matrix (κ × Fin 2) (κ × Fin 2) ℝ) :
    Measurable (GaussianOrthogonalInvariant.transform U :
      (κ × Fin 2 → ℝ) → κ × Fin 2 → ℝ) := by
  rw [measurable_pi_iff]
  intro i
  unfold GaussianOrthogonalInvariant.transform
  fun_prop

/-- A unitary complex matrix preserves the normalized finite complex Gaussian-vector law. -/
theorem map_mulVec_standardMeasure (U : Matrix κ κ ℂ)
    (hU : U * U.conjTranspose = 1) :
    Measure.map (Matrix.mulVec U) standardMeasure = standardMeasure := by
  let R := ComplexMatrixRealification.realify U
  have hR : ∀ i j, ∑ k, R i k * R j k = if i = j then 1 else 0 := by
    intro i j
    exact ComplexMatrixRealification.realify_rows U hU i j
  calc
    Measure.map (Matrix.mulVec U) standardMeasure =
        Measure.map ((Matrix.mulVec U) ∘ ComplexMatrixRealification.gaussianVector)
          (GaussianAlgebra.standardMeasure (ι := κ × Fin 2)) := by
      rw [standardMeasure, Measure.map_map (measurable_mulVec U) measurable_gaussianVector]
    _ = Measure.map (ComplexMatrixRealification.gaussianVector ∘
        GaussianOrthogonalInvariant.transform R)
          (GaussianAlgebra.standardMeasure (ι := κ × Fin 2)) := by
      congr 1
      funext x
      simpa [R, GaussianOrthogonalInvariant.transform, Matrix.mulVec, dotProduct] using
        (ComplexMatrixRealification.gaussianVector_mulVec U x).symm
    _ = Measure.map ComplexMatrixRealification.gaussianVector
        (Measure.map (GaussianOrthogonalInvariant.transform R)
          (GaussianAlgebra.standardMeasure (ι := κ × Fin 2))) := by
      rw [Measure.map_map measurable_gaussianVector (measurable_transform R)]
    _ = standardMeasure := by
      rw [GaussianOrthogonalInvariant.map_transform_standardMeasure R hR]
      rfl

/-- Integrals against the complex Gaussian-vector law are invariant under a unitary change
of variables. -/
theorem integral_mulVec_standardMeasure (U : Matrix κ κ ℂ)
    (hU : U * U.conjTranspose = 1) (f : (κ → ℂ) → ℝ)
    (hf : AEStronglyMeasurable f standardMeasure) :
    (∫ z, f (Matrix.mulVec U z) ∂standardMeasure) =
      ∫ z, f z ∂standardMeasure := by
  have hmap := map_mulVec_standardMeasure U hU
  have hfmap : AEStronglyMeasurable f (Measure.map (Matrix.mulVec U) standardMeasure) := by
    rwa [hmap]
  calc
    (∫ z, f (Matrix.mulVec U z) ∂standardMeasure) =
        ∫ z, f z ∂Measure.map (Matrix.mulVec U) standardMeasure := by
      exact (integral_map (measurable_mulVec U).aemeasurable hfmap).symm
    _ = ∫ z, f z ∂standardMeasure := by rw [hmap]

end
end QuaternionicSymmetry.ComplexGaussianUnitaryInvariant
