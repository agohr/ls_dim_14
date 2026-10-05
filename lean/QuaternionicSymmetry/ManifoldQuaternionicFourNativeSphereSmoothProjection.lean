import QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereDiffeomorphPackage

/-! The negative-Hodge unit sphere's literal base projection is smooth in
the independently constructed native-form atlas. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereSmoothProjection

open ManifoldQuaternionicMetric
open ManifoldQuaternionicFourNativeSmoothCore
open ManifoldQuaternionicFourNativeSphereBundleEquiv
open ManifoldQuaternionicFourNativeSphereBundleSmoothCoordinate
open ManifoldQuaternionicFourNativeSphereDiffeomorphism
open ManifoldQuaternionicFourNativeSphereDiffeomorphPackage
open ManifoldQuaternionicFourNativeSphereCharted
open ManifoldQuaternionicFourNativeSphereSmoothAtlas
open ManifoldTwistorSphereCore
open ManifoldTwistorSphereManifold
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

private abbrev productModel := (𝓘(ℝ,E)).prod (𝓡 2)

theorem nativeSphereProjection_smooth :
    letI := nativeSphereModelChartedSpace Q hdim
    ContMDiff (productModel (E := E)) 𝓘(ℝ,E) ∞
      (fun p : NativeSphereBundleTotal Q => p.1.1) := by
  letI := nativeSphereModelChartedSpace Q hdim
  letI : IsManifold (productModel (E := E)) ∞
      (NativeSphereBundleTotal Q) := nativeSphere_isManifold Q hdim
  have h := (sphereProjection_smooth Q).comp
    (associatedToNative_symm_contMDiff Q hdim)
  apply h.congr
  intro p
  have hp := associatedToNativeHomeomorph_projection Q hdim
    ((associatedToNativeHomeomorph Q hdim).symm p)
  have hright := (associatedToNativeHomeomorph Q hdim).apply_symm_apply p
  exact (congrArg (fun q : NativeSphereBundleTotal Q => q.1.1) hright).symm.trans hp

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereSmoothProjection
