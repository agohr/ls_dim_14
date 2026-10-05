import QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereDiffeomorphism
import Mathlib.Geometry.Manifold.Diffeomorph

/-! The actual smooth bundle equivalence to the independently constructed
native negative-Hodge two-form sphere, with literal projection and fiber map. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereDiffeomorphPackage

open ManifoldQuaternionicMetric
open ManifoldQuaternionicFourNativeSmoothCore
open ManifoldQuaternionicFourNativeSphereFormSmooth
open ManifoldQuaternionicFourNativeSphereBundleEquiv
open ManifoldQuaternionicFourNativeSphereBundleSmoothCoordinate
open ManifoldQuaternionicFourNativeSphereDiffeomorphism
open ManifoldQuaternionicFourNativeSphereCharted
open ManifoldQuaternionicFourNativeSphereSmoothAtlas
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

private abbrev productModel := (𝓘(ℝ,E)).prod (𝓡 2)

def associatedNativeDiffeomorph :
    letI := nativeSphereModelChartedSpace Q hdim
    Diffeomorph (productModel (E := E)) (productModel (E := E))
      (SphereBundleTotal Q) (NativeSphereBundleTotal Q) ∞ := by
  letI := nativeSphereModelChartedSpace Q hdim
  exact {
    toEquiv := (associatedToNativeHomeomorph Q hdim).toEquiv
    contMDiff_toFun := associatedToNative_contMDiff Q hdim
    contMDiff_invFun := associatedToNative_symm_contMDiff Q hdim }

theorem associatedNativeDiffeomorph_projection (z : SphereBundleTotal Q) :
    (associatedNativeDiffeomorph Q hdim z).1.1 = z.1 := rfl

theorem associatedNativeDiffeomorph_fiber (z : SphereBundleTotal Q) :
    (associatedNativeDiffeomorph Q hdim z).1.2 =
      nativeSphereForm Q (Q.frames.adaptedCore.indexAt z.1)
        (z.1, coefficientSphereHomeomorph
          (localCoordinate Q (Q.frames.adaptedCore.indexAt z.1)
            (toOriginalSphere Q z)
            (Q.frames.adaptedCore.mem_baseSet_at _))) := rfl

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereDiffeomorphPackage
