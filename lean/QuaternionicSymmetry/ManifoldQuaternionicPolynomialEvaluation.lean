import QuaternionicSymmetry.ManifoldCharacteristicPolynomialSoundness
import QuaternionicSymmetry.ManifoldQuaternionicTraceExpressions

/-!
Sound polynomial evaluation on actual quaternionic and tangent curvature trace
classes. The four generators are raw trace classes; no topological Chern or
Pontryagin normalization is asserted.
-/

namespace QuaternionicSymmetry.ManifoldQuaternionicPolynomialEvaluation

open QuaternionicSymmetry.ManifoldEvenCharacteristicAlgebra
  QuaternionicSymmetry.ManifoldCharacteristicPolynomialSoundness
  QuaternionicSymmetry.ManifoldCharacteristicExpression
  QuaternionicSymmetry.ManifoldQuaternionicAdjointChernWeil
  QuaternionicSymmetry.ManifoldQuaternionicAdjointChernWeilIndependence
open scoped Manifold ContDiff Topology

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable (Q : QuaternionicSymmetry.ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

/-- A finite rational characteristic expression evaluated on the global
rank-three trace-square and three even tangent trace-power classes. -/
noncomputable def evaluateCurvaturePolynomial
    (D : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (P : EvenExpr n) : Grade (E := E) (M := M) n :=
  EvenExpr.evaluate (traceCurvatureSquareClass Q D)
    (tangentTraceClass Q D 1) (tangentTraceClass Q D 3)
    (tangentTraceClass Q D 5) P

/-- Equality of the underlying checked rational polynomials implies equality
of their genuine homogeneous cohomology evaluations. -/
theorem evaluate_eq_of_polynomial_eq
    (D : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (P R : EvenExpr n)
    (h : P.polynomial = R.polynomial) :
    evaluateCurvaturePolynomial Q D P = evaluateCurvaturePolynomial Q D R :=
  EvenExpr.evaluate_eq_of_polynomial_eq _ _ _ _ P R h

/-- Every such polynomial evaluation is independent of the chosen smooth
compatible tangent connection. -/
theorem evaluate_connection_independent
    (D₀ D₁ : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (P : EvenExpr n) :
    evaluateCurvaturePolynomial Q D₁ P = evaluateCurvaturePolynomial Q D₀ P := by
  exact EvenExpr.evaluate_congr
    (traceCurvatureSquareClass_eq Q D₀ D₁)
    (tangentTraceClass_connection_independent Q D₀ D₁ 1)
    (tangentTraceClass_connection_independent Q D₀ D₁ 3)
    (tangentTraceClass_connection_independent Q D₀ D₁ 5) P

end QuaternionicSymmetry.ManifoldQuaternionicPolynomialEvaluation
