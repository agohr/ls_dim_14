import QuaternionicSymmetry.QuaternionicManifoldStandardTraceSquare

/-! Exact degree-four normalization of the actual projective-standard
curvature trace. The coefficient agrees with `X = iF/(2π)` and the printed
`(1/2) trℂ(-X²)` convention. -/
namespace QuaternionicSymmetry.QuaternionicManifoldStandardP1Normalization

open QuaternionicManifoldStandardTraceSquare
  ManifoldQuaternionicScalarTraceComparison
  ManifoldQuaternionicConnection
  ManifoldQuaternionicConnectionSplitting
  ManifoldQuaternionicAdjointConnection
  LocalEndomorphismTrace
  LocalChernWeilQuadratic
open scoped ContDiff Manifold Quaternion
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

def standardP1Local (p : M) (y : E) :
    E [⋀^Fin 4]→L[ℝ] ℝ :=
  (1 / (16 * Real.pi ^ 2) : ℝ) •
    traceSquareForm traceCLM
      (QuaternionicManifoldProjectiveStandardConnection.standardConnection S Q D p) y

def tangentHalfP1Local (p : M) (y : E) :
    E [⋀^Fin 4]→L[ℝ] ℝ :=
  (1 / (16 * Real.pi ^ 2) : ℝ) •
    traceSquareForm traceCLM (D.form p) y

def rankThreeQuarterPontryaginLocal (p : M) (y : E) :
    E [⋀^Fin 4]→L[ℝ] ℝ :=
  (-(1 / (32 * Real.pi ^ 2)) : ℝ) •
    traceSquareForm traceCLM (inducedForm Q D p) y

set_option maxHeartbeats 800000 in
theorem standardP1Local_eq_tangent_plus_rankThree (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    standardP1Local S Q D p y = tangentHalfP1Local Q D p y +
      ((S.quaternionicDimension : ℝ) - 1) •
        rankThreeQuarterPontryaginLocal Q D p y := by
  ext w
  have hs := congrArg (fun F : E [⋀^Fin 4]→L[ℝ] ℝ => F w)
    (standard_traceSquareForm S Q D p y hy)
  have ht := congrArg (fun F : E [⋀^Fin 4]→L[ℝ] ℝ => F w)
    (tangent_traceSquareForm Q D p y hy)
  simp only [ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply] at hs ht ⊢
  simp only [smul_eq_mul] at hs ht
  unfold standardP1Local tangentHalfP1Local
    rankThreeQuarterPontryaginLocal
  simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  rw [hs, ht]
  have hn : (Module.finrank ℝ E : ℝ) =
      4 * (S.quaternionicDimension : ℝ) := by
    exact_mod_cast S.real_finrank
  rw [hn]
  ring

end
end QuaternionicSymmetry.QuaternionicManifoldStandardP1Normalization
