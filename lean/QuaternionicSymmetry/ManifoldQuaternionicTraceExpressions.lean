import QuaternionicSymmetry.ManifoldCharacteristicExpression
import QuaternionicSymmetry.ManifoldQuaternionicAdjointChernWeilIndependence

/-!
Characteristic expressions evaluated on the actual tangent and induced
rank-three curvature trace classes. These are raw trace powers, without a
Pontryagin or Chern-class normalization.
-/

namespace QuaternionicSymmetry.ManifoldQuaternionicTraceExpressions

open QuaternionicSymmetry.ManifoldCharacteristicExpression
  QuaternionicSymmetry.ManifoldQuaternionicAdjointChernWeil
  QuaternionicSymmetry.ManifoldQuaternionicAdjointChernWeilIndependence
  QuaternionicSymmetry.ManifoldDeRhamAllDegrees
open scoped Manifold ContDiff Topology

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Nontrivial E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable (Q : QuaternionicSymmetry.ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

/-- Evaluation on the induced rank-three curvature trace-square class and
three even tangent curvature trace-power classes. -/
noncomputable def evaluateCurvatureTraces
    (D : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (P : CharacteristicExpr n) :
    CohomologyByDegree (E := E) (M := M) n :=
  evaluateTangent Q D (traceCurvatureSquareClass Q D) P

theorem evaluateCurvatureTraces_connection_independent
    (D₀ D₁ : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (P : CharacteristicExpr n) :
    evaluateCurvatureTraces Q D₁ P = evaluateCurvatureTraces Q D₀ P := by
  exact evaluateTangent_connection_independent_of_u_eq Q D₀ D₁
    (traceCurvatureSquareClass Q D₀) (traceCurvatureSquareClass Q D₁)
    (traceCurvatureSquareClass_eq Q D₀ D₁) P

end QuaternionicSymmetry.ManifoldQuaternionicTraceExpressions
