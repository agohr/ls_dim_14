import QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereTwistorCoordinate

/-! The native Hodge-sphere chart is exactly the associated twistor-sphere
bundle chart after the checked pointwise two-form identification. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereAssociatedChart

open ManifoldQuaternionicMetric
open ManifoldQuaternionicFourNativeSmoothCore
open ManifoldQuaternionicFourNativeSphereBundleEquiv
open ManifoldQuaternionicFourNativeSphereLocalTrivialization
open ManifoldQuaternionicFourNativeSpherePartialChart
open ManifoldQuaternionicFourNativeSphereChartOverlap
open ManifoldQuaternionicFourNativeSphereTwistorCoordinate
open ManifoldQuaternionicFourNativeSphereBundleSmoothCoordinate
open ManifoldTwistorSphereCore
open ManifoldTwistorSphereBundle
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
local instance (i : atlas E M) : TopologicalSpace (nativeLocalSphereTotal Q i) := by
  unfold nativeLocalSphereTotal
  infer_instance

theorem associated_native_chart_coordinate (i : atlas E M)
    (p₀ : nativeLocalSphereTotal Q i) (z : SphereBundleTotal Q)
    (hi : z.1 ∈ (sphereCore Q).baseSet i) :
    nativeSpherePartialChart Q hdim i p₀
      (twistorToNativeSphere Q (toOriginalSphere Q z)) =
        (sphereCore Q).localTriv i z := by
  have hnative : (twistorToNativeSphere Q (toOriginalSphere Q z)).1.1 ∈
      Q.frames.adaptedCore.baseSet i := hi
  rw [nativeSpherePartialChart_apply Q hdim i p₀
    (twistorToNativeSphere Q (toOriginalSphere Q z)) hnative]
  apply Prod.ext
  · rfl
  · change coefficientSphereHomeomorph
      (nativeLocalToCoefficient Q hdim i
        ⟨twistorToNativeSphere Q (toOriginalSphere Q z),hi⟩).1.2 =
      ((sphereCore Q).localTriv i z).2
    rw [nativeCoefficient_of_twistor Q hdim i (toOriginalSphere Q z) hi]
    exact associated_local_coordinate Q i z hi

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereAssociatedChart
