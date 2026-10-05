import QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereAssociatedChart

/-! Preferred chart compatibility of the independently smooth Hodge sphere
with the associated twistor sphere. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativeSpherePreferredChart

open ManifoldQuaternionicMetric
open ManifoldQuaternionicFourNativeSmoothCore
open ManifoldQuaternionicFourNativeSphereBundleEquiv
open ManifoldQuaternionicFourNativeSphereBundleSmoothCoordinate
open ManifoldQuaternionicFourNativeSphereAssociatedChart
open ManifoldQuaternionicFourNativeSphereCharted
open ManifoldQuaternionicFourNativeSpherePartialChart
open ManifoldTwistorSphereCore
open ManifoldTwistorSphereManifold
open ManifoldTwistorCoefficientSphere
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (hdim : Module.finrank ℝ E = 4)

local instance : NormedAddCommGroup (E [⋀^Fin 2]→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 2]→L[ℝ] ℝ) := inferInstance
local instance : TopologicalSpace (nativeTwoFormVectorCore Q).TotalSpace :=
  (nativeTwoFormVectorCore Q).toTopologicalSpace
local instance : TopologicalSpace (NativeSphereBundleTotal Q) := by
  unfold NativeSphereBundleTotal
  infer_instance
theorem preferred_chart_compatible (z w : SphereBundleTotal Q)
    (hw : w ∈ (chartAt (M × geometricSphere) z).source) :
    letI := nativeSphereChartedSpace Q hdim
    (chartAt (M × geometricSphere) (associatedToNativeHomeomorph Q hdim z))
      (associatedToNativeHomeomorph Q hdim w) =
        (chartAt (M × geometricSphere) z) w := by
  letI := nativeSphereChartedSpace Q hdim
  let i := Q.frames.adaptedCore.indexAt z.1
  have hi : w.1 ∈ (sphereCore Q).baseSet i := by
    simpa [i, FiberBundle.chartedSpace'_chartAt] using hw
  change nativeSpherePartialChart Q hdim i
      ⟨associatedToNativeHomeomorph Q hdim z,
        Q.frames.adaptedCore.mem_baseSet_at _⟩
      (associatedToNativeHomeomorph Q hdim w) =
    (sphereCore Q).localTriv i w
  exact associated_native_chart_coordinate Q hdim i _ w hi

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativeSpherePreferredChart
