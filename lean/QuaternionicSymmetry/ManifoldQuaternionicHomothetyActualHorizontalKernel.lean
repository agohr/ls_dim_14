import QuaternionicSymmetry.ManifoldQuaternionicHomothetyActualHorizontalCoefficient

/-! The actual contact-distribution candidate, defined as the connection
horizontal plane on the real twistor tangent bundle, is homothety invariant. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyActualHorizontalKernel
open ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyConnection
open ManifoldQuaternionicHomothetyTwistorSmooth
open ManifoldQuaternionicHomothetyActualHorizontalCoefficient
open ManifoldTwistorGlobalAlmostComplex
open ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem horizontal_mem_iff_rescale (s : ℝ) (hs : s ≠ 0)
    (z : SphereBundleTotal (rescaleMetric Q s hs))
    (v : E × EuclideanSpace ℝ (Fin 2)) :
    v ∈ horizontalTangentSubmodule (rescaleMetric Q s hs)
        (rescaleConnection Q D s hs) z ↔
      v ∈ horizontalTangentSubmodule Q D (sphereTotalDiffeomorph Q s hs z) := by
  change (connectionTangentEquiv (rescaleMetric Q s hs)
      (rescaleConnection Q D s hs) z v).2 = 0 ↔
    (connectionTangentEquiv Q D (sphereTotalDiffeomorph Q s hs z) v).2 = 0
  rw [connectionTangentEquiv_second_rescale Q D s hs z v]

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyActualHorizontalKernel
