import QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereSmoothAtlas
import QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereBundleHomeomorphism
import QuaternionicSymmetry.ManifoldTwistorSphereHomeomorph

/-! Coordinate comparison between the genuine smooth associated twistor
sphere bundle and the independently smooth native Hodge sphere bundle. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereBundleSmoothCoordinate

open ManifoldQuaternionicMetric
open ManifoldQuaternionicFourNativeSmoothCore
open ManifoldQuaternionicFourNativeSphereBundleEquiv
open ManifoldQuaternionicFourNativeSphereBundleHomeomorphism
open ManifoldQuaternionicFourNativeSphereLocalTrivialization
open ManifoldQuaternionicFourNativeSpherePartialChart
open ManifoldQuaternionicFourNativeSphereChartOverlap
open ManifoldQuaternionicFourNativeSphereInverseLocal
open ManifoldTwistorSphereCore
open ManifoldTwistorSphereBundle
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
local instance (i : atlas E M) : TopologicalSpace (nativeLocalSphereTotal Q i) := by
  unfold nativeLocalSphereTotal
  infer_instance

def associatedToNativeHomeomorph :
    SphereBundleTotal Q ≃ₜ NativeSphereBundleTotal Q :=
  (sphereTotalHomeomorph Q).trans (twistorNativeSphereHomeomorph Q hdim)

theorem associatedToNativeHomeomorph_projection (z : SphereBundleTotal Q) :
    (associatedToNativeHomeomorph Q hdim z).1.1 = z.1 := rfl

theorem associated_local_coordinate (i : atlas E M)
    (z : SphereBundleTotal Q)
    (hi : z.1 ∈ (sphereCore Q).baseSet i) :
    coefficientSphereHomeomorph
      (localCoordinate Q i (toOriginalSphere Q z) hi) =
        ((sphereCore Q).localTriv i z).2 := by
  let Z := Q.quaternionicRankThreeCore
  have hidx : z.1 ∈ Z.baseSet (Z.indexAt z.1) := Z.mem_baseSet_at _
  have hco : localCoordinate Q i (toOriginalSphere Q z) hi =
      sphereTransition Q (Z.indexAt z.1) i z.1 hidx hi
        (coefficientSphereHomeomorph.symm z.2) := by
    apply Subtype.ext
    change Z.coordChange (Z.indexAt z.1) i z.1
      (Z.coordChange (Z.indexAt z.1) (Z.indexAt z.1) z.1
        (coefficientSphereHomeomorph.symm z.2).1) =
      Z.coordChange (Z.indexAt z.1) i z.1
        (coefficientSphereHomeomorph.symm z.2).1
    rw [Z.coordChange_self _ _ hidx]
  rw [hco, (sphereCore Q).localTriv_apply]
  change coefficientSphereHomeomorph
      (sphereTransition Q (Z.indexAt z.1) i z.1 hidx hi
        (coefficientSphereHomeomorph.symm z.2)) =
    euclideanSphereCoordChange Q (Z.indexAt z.1) i z.1 z.2
  dsimp [euclideanSphereCoordChange]
  rw [dif_pos ⟨hidx,hi⟩]

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereBundleSmoothCoordinate
