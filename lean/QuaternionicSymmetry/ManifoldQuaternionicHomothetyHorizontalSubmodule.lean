import QuaternionicSymmetry.ManifoldQuaternionicHomothetyActualHorizontalKernel

/-! Equality of literal horizontal tangent submodules at corresponding
twistor points under constant homothety. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyHorizontalSubmodule
open ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyConnection
open ManifoldQuaternionicHomothetyTwistorSmooth
open ManifoldQuaternionicHomothetyActualHorizontalKernel
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

theorem horizontalSubmodule_rescale (s : ℝ) (hs : s ≠ 0)
    (z : SphereBundleTotal (rescaleMetric Q s hs)) :
    horizontalTangentSubmodule (rescaleMetric Q s hs)
      (rescaleConnection Q D s hs) z =
        horizontalTangentSubmodule Q D (sphereTotalDiffeomorph Q s hs z) := by
  ext v
  exact horizontal_mem_iff_rescale Q D s hs z v

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyHorizontalSubmodule
