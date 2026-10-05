import QuaternionicSymmetry.QuaternionicScalarLineTracePowerForm
import QuaternionicSymmetry.QuaternionicActualExteriorTraceRatio

/-! The exact all-positive-even-power scalar-line/rank-three trace ratio
for the actual compatible tangent connection. -/
namespace QuaternionicSymmetry.QuaternionicActualScalarAdjointTracePowers
open QuaternionicScalarLineTracePowerForm
  QuaternionicActualExteriorTraceRatio
  ContinuousAlgebraWedgePowers LocalChernWeilTracePowers
  ManifoldQuaternionicAdjointConnection
open scoped Quaternion ContDiff Manifold
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

/-- For every positive j, the actual scalar-line curvature trace form at
power 2j is 2/4^j times the actual induced rank-three trace form. -/
theorem scalarLine_induced_tracePower_ratio (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target)
    (j : ℕ) (hj : 0 < j) :
    (4 : ℝ) ^ j •
      LocalEndomorphismTrace.traceCLM.compContinuousAlternatingMap
        (power (scalarLineCurvatureForm Q D p y) (2 * j - 1)) =
    (2 : ℝ) • tracePowerForm LocalEndomorphismTrace.traceCLM
      (inducedForm Q D p) (2 * j - 1) y := by
  rw [scalarLine_tracePower_eq_exterior Q D p y (2 * j - 1)]
  exact scalar_exterior_eq_induced_tracePowerForm Q D p y hy j hj

end
end QuaternionicSymmetry.QuaternionicActualScalarAdjointTracePowers
