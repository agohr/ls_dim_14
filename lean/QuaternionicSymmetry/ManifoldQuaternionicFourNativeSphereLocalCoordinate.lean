import QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereBundleEquiv

/-! The global native-Hodge sphere equivalence has the explicit normalized
two-form formula in every actual adapted local trivialization. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereLocalCoordinate

open ManifoldQuaternionicMetric
open ManifoldQuaternionicFourNativeSmoothCore
open ManifoldQuaternionicFourNativeTwoFormCore
open ManifoldQuaternionicFourNativeNegativeSphereSet
open ManifoldQuaternionicFourNativeSphereFormSmooth
open ManifoldQuaternionicFourNativeSphereBundleEquiv
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

include hdim in
theorem twistorToNative_local (i : atlas E M) (z : TwistorSphere Q)
    (hi : projection Q z ∈ Q.frames.adaptedCore.baseSet i) :
    ((nativeTwoFormVectorCore Q).localTriv i
      (twistorToNativeSphere Q z).1).2 =
      nativeSphereForm Q i
        (projection Q z,
          coefficientSphereHomeomorph (localCoordinate Q i z hi)) := by
  let x := projection Q z
  let k := Q.frames.adaptedCore.indexAt x
  have hk : x ∈ Q.frames.adaptedCore.baseSet k :=
    Q.frames.adaptedCore.mem_baseSet_at x
  change nativeCoordChange (E := E) (M := M) k i x
      (nativeSphereForm Q k
        (x,coefficientSphereHomeomorph (localCoordinate Q k z hk))) = _
  rw [nativeSphereForm_transition Q hdim k i x hk hi]
  rw [localTrivialization_transition Q k i z hk hi]

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereLocalCoordinate
