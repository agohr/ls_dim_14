import QuaternionicSymmetry.ManifoldQuaternionicHomothetyExplicitDerivative

/-! Equality transport for two abstract twistor sphere cores. Both
statements are proved before specializing to a metric homothety, so Lean
does not unfold the concrete quaternionic frame-transition records. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyAbstractCoreTransport
open ManifoldQuaternionicHomothetyExplicitDerivative
open ManifoldTwistorCoefficientSphere
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

theorem core_topology_transport
    (Z W : FiberBundleCore (atlas E M) M geometricSphere) (h : Z = W) :
    Z.toTopologicalSpace = W.toTopologicalSpace := by
  cases h
  rfl

theorem core_charts_transport
    (Z W : FiberBundleCore (atlas E M) M geometricSphere) (h : Z = W) :
    h ▸ coreCharts Z = coreCharts W := by
  cases h
  rfl

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyAbstractCoreTransport
