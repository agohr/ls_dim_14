import QuaternionicSymmetry.ManifoldQuaternionicHomothetyAbstractCoreTransport
import QuaternionicSymmetry.ManifoldQuaternionicHomothetyTwistorCore

/-! Explicit topology identity for the actual twistor sphere cores under
constant metric homothety. No inferred-instance comparison is elaborated. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyConcreteCoreTopology
open ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyTwistorCore
open ManifoldQuaternionicHomothetyAbstractCoreTransport
open ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem sphereCoreTopology_rescale (s : ℝ) (hs : s ≠ 0) :
    (sphereCore (rescaleMetric Q s hs)).toTopologicalSpace =
      (sphereCore Q).toTopologicalSpace :=
  core_topology_transport _ _ (sphereCore_rescale Q s hs)

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyConcreteCoreTopology
