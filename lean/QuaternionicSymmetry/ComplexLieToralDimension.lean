import QuaternionicSymmetry.ComplexLieToralDifferentialSubalgebra
import QuaternionicSymmetry.RealComplexifiedMapRange
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! The complex span of a torus differential has dimension no greater than
the dimension of its real source. -/
namespace QuaternionicSymmetry.ComplexLieToralDimension
open RealToComplexTangentComplexification RealComplexifiedMapRange
open ComplexLieToralDifferentialSubalgebra
open scoped Manifold ContDiff TensorProduct
noncomputable section

theorem finrank_span_range_le {E V : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] [AddCommGroup V] [Module ℂ V]
    (f : E →ₗ[ℝ] V) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range f)) ≤ Module.finrank ℝ E := by
  rw [← range_complexifiedMapComplex]
  exact (LinearMap.finrank_range_le (complexifiedMapComplex f)).trans_eq
    Module.finrank_baseChange

variable {V K : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V]
  [Group K] [TopologicalSpace K] [ChartedSpace V K]
  [IsManifold 𝓘(ℂ,V) ∞ K] [LieGroup 𝓘(ℂ,V) ∞ K]
  {r d : ℕ} (ρ : (Fin r → Circle) →* K)
  (hChart : ChartedSpace (Fin d → ℝ) (Fin r → Circle))
  (hManifold : letI := hChart
    IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Fin r → Circle))
  (hLie : letI := hChart
    LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (Fin r → Circle))
  (hSmooth : letI := hChart
    ContMDiff 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,V) ∞ ρ)

theorem toral_finrank_le :
    Module.finrank ℂ (toralLieSubalgebra ρ hChart hManifold hLie hSmooth) ≤ d := by
  letI := hChart
  let f : (Fin d → ℝ) →ₗ[ℝ] V := (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,V) ρ 1).toLinearMap
  change Module.finrank ℂ (Submodule.span ℂ (Set.range f)) ≤ d
  simpa using finrank_span_range_le f

end
end QuaternionicSymmetry.ComplexLieToralDimension
