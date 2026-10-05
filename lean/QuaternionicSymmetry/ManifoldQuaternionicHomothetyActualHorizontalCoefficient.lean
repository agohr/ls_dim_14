import QuaternionicSymmetry.ManifoldQuaternionicHomothetyRawHorizontal
import QuaternionicSymmetry.ManifoldQuaternionicHomothetyTwistorSmooth

/-! Equality of the actual connection-horizontal coefficient at the two
endpoints of the homothety twistor diffeomorphism. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyActualHorizontalCoefficient
open ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyConnection
open ManifoldQuaternionicHomothetyRawHorizontal
open ManifoldQuaternionicHomothetyTwistorSmooth
open ManifoldTwistorRawHorizontalCoefficient
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

theorem connectionTangentEquiv_second_rescale (s : ℝ) (hs : s ≠ 0)
    (z : SphereBundleTotal (rescaleMetric Q s hs))
    (v : E × EuclideanSpace ℝ (Fin 2)) :
    (connectionTangentEquiv (rescaleMetric Q s hs)
      (rescaleConnection Q D s hs) z v).2 =
        (connectionTangentEquiv Q D (sphereTotalDiffeomorph Q s hs z) v).2 := by
  rw [connectionTangentEquiv_second_raw,
    connectionTangentEquiv_second_raw]
  simp only [sphereTotalDiffeomorph_apply]
  exact congrArg
    (fun L => L v)
    (rawHorizontalCoefficient_rescale Q D s hs z.1
      (extChartAt 𝓘(ℝ,E) z.1 z.1)
      ((extChartAt 𝓘(ℝ,E) z.1).map_source (mem_extChartAt_source z.1)) z.2)

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyActualHorizontalCoefficient
