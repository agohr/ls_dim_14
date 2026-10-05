import QuaternionicSymmetry.ManifoldQuaternionicHomothetyAbstractCoreTransport
import QuaternionicSymmetry.ManifoldQuaternionicHomothetyTwistorCore

/-! The actual smooth charted structures of the rescaled and original
twistor sphere cores agree after transport along their checked core
equality. The formula uses named core structures, not inferred instances. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyConcreteCoreCharts
open ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyTwistorCore
open ManifoldQuaternionicHomothetyAbstractCoreTransport
open ManifoldQuaternionicHomothetyExplicitDerivative
open ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem sphereCoreCharts_rescale (s : ℝ) (hs : s ≠ 0) :
    (sphereCore_rescale Q s hs) ▸
      coreCharts (sphereCore (rescaleMetric Q s hs)) =
        coreCharts (sphereCore Q) :=
  core_charts_transport _ _ (sphereCore_rescale Q s hs)

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyConcreteCoreCharts
