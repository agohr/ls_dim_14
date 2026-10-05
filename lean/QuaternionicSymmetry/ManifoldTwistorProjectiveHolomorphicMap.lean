import QuaternionicSymmetry.ManifoldTwistorProjectiveHolomorphicCoefficients
import QuaternionicSymmetry.ManifoldTwistorLinearSystemTopology
import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-! Holomorphicity of actual complete-linear-system evaluation into the
checked complex projective manifold, away from its genuine base locus. -/

namespace QuaternionicSymmetry.ManifoldTwistorProjectiveHolomorphicMap

open ManifoldTwistorProjectiveBasisCoordinates
open ManifoldTwistorProjectiveHolomorphicCoefficients
open ManifoldTwistorLinearSystem
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldQuaternionicMetric ManifoldQuaternionicConnection
open ComplexProjectiveTopology
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)
variable {n : ℕ} {A : CompatibleComplexAtlas Q D n}
  (L : HolomorphicContactLine Q D n A) (r : ℤ)
variable (d : ℕ)
  (b : Module.Basis (Fin (d + 1)) ℂ (GlobalSections Q D L r))

private def localProjectiveDomain (i : L.Index) : Set (SphereBundleTotal Q) :=
  {x | x ∉ baseLocus Q D L r} ∩ (L.integerTwistCore Q D r).baseSet i

private theorem localProjectiveDomain_subset_chart (i : L.Index) :
    localProjectiveDomain Q D L r i ⊆
      (L.integerTwistCore Q D r).baseSet i := Set.inter_subset_right

private theorem localChartVector_ne_zero (i : L.Index) :
    Set.MapsTo (basisChartEvaluation Q D L r d b i)
      (localProjectiveDomain Q D L r i) {v : Coord d | v ≠ 0} := by
  intro x hx
  exact basisChartEvaluation_ne_zero Q D L r d b i x hx.1 hx.2

private theorem localProjectiveEvaluation_contMDiffOn (i : L.Index) :
    letI := A.charts
    ContMDiffOn 𝓘(ℂ, ComplexTwistorModel n) 𝓘(ℂ, Fin d → ℂ) ∞
      (basisProjectiveEvaluationTotal Q D L r d b)
      (localProjectiveDomain Q D L r i) := by
  letI := A.charts
  have hcoeff := (contMDiffOn_basisChartEvaluation Q D L r d b i).mono
    (localProjectiveDomain_subset_chart Q D L r i)
  have hcomp := (contMDiffOn_projectivize_nonzero d).comp hcoeff
    (localChartVector_ne_zero Q D L r d b i)
  apply hcomp.congr
  intro x hx
  have hchart := basisProjectiveEvaluation_eq_chart Q D L r d b
    ⟨x, hx.1⟩ i hx.2
  change basisProjectiveEvaluationTotal Q D L r d b x =
    projectivize d (basisChartEvaluation Q D L r d b i x)
  rw [basisProjectiveEvaluationTotal_eq Q D L r d b x hx.1]
  rw [projectivize_of_ne_zero d _
    (basisChartEvaluation_ne_zero Q D L r d b i x hx.1 hx.2)]
  exact hchart

/-- The actual complete-linear-system evaluation is holomorphic on its
genuine base-locus complement, after expressing the dual in a chosen finite
basis. The target carries the checked standard complex projective manifold
structure. -/
theorem basisProjectiveEvaluationTotal_contMDiffOn :
    letI := A.charts
    ContMDiffOn 𝓘(ℂ, ComplexTwistorModel n) 𝓘(ℂ, Fin d → ℂ) ∞
      (basisProjectiveEvaluationTotal Q D L r d b)
      {x : SphereBundleTotal Q | x ∉ baseLocus Q D L r} := by
  letI := A.charts
  let Z := L.integerTwistCore Q D r
  apply contMDiffOn_of_locally_contMDiffOn
  intro x hx
  let i := Z.indexAt x
  refine ⟨Z.baseSet i, Z.isOpen_baseSet i, Z.mem_baseSet_at x, ?_⟩
  exact localProjectiveEvaluation_contMDiffOn Q D L r d b i

end
end QuaternionicSymmetry.ManifoldTwistorProjectiveHolomorphicMap
