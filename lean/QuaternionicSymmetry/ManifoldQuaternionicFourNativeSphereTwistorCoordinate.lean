import QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereBundleSmoothCoordinate

/-! Small coefficient-level comparison, isolated to keep dependent chart
equalities away from large bundle-homeomorphism unfoldings. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereTwistorCoordinate

open ManifoldQuaternionicMetric
open ManifoldQuaternionicFourNativeSmoothCore
open ManifoldQuaternionicFourNativeSphereBundleEquiv
open ManifoldQuaternionicFourNativeSphereLocalTrivialization
open ManifoldQuaternionicFourNativeSphereChartOverlap
open ManifoldTwistorSphereBundle
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

theorem nativeCoefficient_of_twistor (i : atlas E M) (z : TwistorSphere Q)
    (hi : projection Q z ∈ Q.frames.adaptedCore.baseSet i) :
    (nativeLocalToCoefficient Q hdim i ⟨twistorToNativeSphere Q z,hi⟩).1.2 =
      localCoordinate Q i z hi := by
  have h := nativeLocalToCoefficient_eq_localCoordinate Q hdim i
    (twistorToNativeSphere Q z) hi
  simpa only [nativeSphereToTwistor_left Q hdim z] using h

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereTwistorCoordinate
