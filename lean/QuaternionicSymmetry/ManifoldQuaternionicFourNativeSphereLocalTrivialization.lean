import QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereBundleHomeomorphism
import QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereInverseLocal

/-! Direct local product trivialization of the native negative-Hodge sphere
subset, built from the actual native vector-bundle chart and the proved
coefficient extraction homeomorphism. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereLocalTrivialization

open ManifoldQuaternionicMetric
open ManifoldQuaternionicFourNativeSmoothCore
open ManifoldQuaternionicFourNativeNegativeSphereSet
open ManifoldQuaternionicFourNativeSphereLocalCharts
open ManifoldQuaternionicFourNativeSphereInverseLocal
open ManifoldQuaternionicFourNativeSphereBundleEquiv
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
local instance (i : atlas E M) : TopologicalSpace (coefficientLocalDomain Q i) := by
  unfold coefficientLocalDomain
  infer_instance
local instance (i : atlas E M) : TopologicalSpace (nativeLocalDomain Q i) := by
  unfold nativeLocalDomain
  infer_instance

def nativeLocalSphereTotal (i : atlas E M) :=
  {p : NativeSphereBundleTotal Q //
    p.1.1 ∈ Q.frames.adaptedCore.baseSet i}

local instance (i : atlas E M) : TopologicalSpace (nativeLocalSphereTotal Q i) := by
  unfold nativeLocalSphereTotal
  infer_instance

def nativeLocalToCoefficient (i : atlas E M) :
    nativeLocalSphereTotal Q i → coefficientLocalDomain Q i :=
  fun p => (localNativeHomeomorph Q hdim i).symm
    (nativeLocalCoordinate Q hdim i p.1 p.2)

def coefficientToNativeLocal (i : atlas E M)
    (q : coefficientLocalDomain Q i) : nativeLocalSphereTotal Q i := by
  let Z := nativeTwoFormVectorCore Q
  let r := localNativeHomeomorph Q hdim i q
  let t : Z.TotalSpace := (Z.localTriv i).toOpenPartialHomeomorph.symm r.1
  have htbase : t.1 = q.1.1 := rfl
  have hi : t.1 ∈ Z.baseSet i := by simpa [htbase] using q.2
  have hcoord : (Z.localTriv i t).2 = r.1.2 := by
    have hright := (Z.localTriv i).toOpenPartialHomeomorph.right_inv
      (by exact ⟨q.2,Set.mem_univ _⟩ : r.1 ∈ (Z.localTriv i).target)
    exact congrArg Prod.snd hright
  have hmem : t ∈ nativeNegativeSphereTotal Q := by
    apply (nativeNegativeSphereTotal_iff_chart Q hdim t i hi).mpr
    change (Z.localTriv i t).2 ∈ nativeLocalSphereSet Q i t.1
    rw [hcoord]
    simpa only [htbase] using r.2.2
  exact ⟨⟨t,hmem⟩,hi⟩

theorem nativeLocalToCoefficient_left (i : atlas E M)
    (q : coefficientLocalDomain Q i) :
    nativeLocalToCoefficient Q hdim i
      (coefficientToNativeLocal Q hdim i q) = q := by
  apply (localNativeHomeomorph Q hdim i).injective
  unfold nativeLocalToCoefficient
  rw [(localNativeHomeomorph Q hdim i).apply_symm_apply]
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change ((nativeTwoFormVectorCore Q).localTriv i
      (coefficientToNativeLocal Q hdim i q).1.1).2 =
        (localNativeHomeomorph Q hdim i q).1.2
    change ((nativeTwoFormVectorCore Q).localTriv i
      (((nativeTwoFormVectorCore Q).localTriv i).toOpenPartialHomeomorph.symm
        (localNativeHomeomorph Q hdim i q).1)).2 = _
    have hright := ((nativeTwoFormVectorCore Q).localTriv i).toOpenPartialHomeomorph.right_inv
      (by exact ⟨q.2, Set.mem_univ _⟩ :
        (localNativeHomeomorph Q hdim i q).1 ∈
          ((nativeTwoFormVectorCore Q).localTriv i).target)
    exact congrArg Prod.snd hright

theorem coefficientToNativeLocal_right (i : atlas E M)
    (p : nativeLocalSphereTotal Q i) :
    coefficientToNativeLocal Q hdim i
      (nativeLocalToCoefficient Q hdim i p) = p := by
  apply Subtype.ext
  apply Subtype.ext
  let Z := nativeTwoFormVectorCore Q
  have hp : p.1.1.1 ∈ Z.baseSet i := p.2
  have hcoord : Z.localTriv i
      (coefficientToNativeLocal Q hdim i
        (nativeLocalToCoefficient Q hdim i p)).1.1 = Z.localTriv i p.1.1 := by
    have h := (localNativeHomeomorph Q hdim i).apply_symm_apply
      (nativeLocalCoordinate Q hdim i p.1 p.2)
    have h' := congrArg Subtype.val h
    have hright := (Z.localTriv i).toOpenPartialHomeomorph.right_inv
      (by exact ⟨(nativeLocalToCoefficient Q hdim i p).2, Set.mem_univ _⟩ :
        (localNativeHomeomorph Q hdim i
          (nativeLocalToCoefficient Q hdim i p)).1 ∈ (Z.localTriv i).target)
    exact hright.trans h'
  have hleft := (Z.localTriv i).toOpenPartialHomeomorph.left_inv
    (by simpa using hp : p.1.1 ∈ (Z.localTriv i).source)
  have hleft' := (Z.localTriv i).toOpenPartialHomeomorph.left_inv
    (by simpa using (coefficientToNativeLocal Q hdim i
      (nativeLocalToCoefficient Q hdim i p)).2 :
      (coefficientToNativeLocal Q hdim i
        (nativeLocalToCoefficient Q hdim i p)).1.1 ∈ (Z.localTriv i).source)
  calc
    (coefficientToNativeLocal Q hdim i
      (nativeLocalToCoefficient Q hdim i p)).1.1 =
        (Z.localTriv i).toOpenPartialHomeomorph.symm
          (Z.localTriv i
            (coefficientToNativeLocal Q hdim i
              (nativeLocalToCoefficient Q hdim i p)).1.1) := hleft'.symm
    _ = (Z.localTriv i).toOpenPartialHomeomorph.symm
          (Z.localTriv i p.1.1) := congrArg _ hcoord
    _ = p.1.1 := hleft

theorem nativeLocalToCoefficient_continuous (i : atlas E M) :
    Continuous (nativeLocalToCoefficient Q hdim i) := by
  let Z := nativeTwoFormVectorCore Q
  have htotal : Continuous (fun p : nativeLocalSphereTotal Q i =>
      (p.1.1 : Z.TotalSpace)) :=
    continuous_subtype_val.comp continuous_subtype_val
  have htriv : Continuous (fun p : nativeLocalSphereTotal Q i =>
      Z.localTriv i p.1.1) :=
    (Z.localTriv i).continuousOn.comp_continuous htotal
      (by intro p; exact p.2)
  have hnative : Continuous (fun p : nativeLocalSphereTotal Q i =>
      nativeLocalCoordinate Q hdim i p.1 p.2) :=
    htriv.subtype_mk _
  exact (localNativeHomeomorph Q hdim i).symm.continuous.comp hnative

theorem coefficientToNativeLocal_continuous (i : atlas E M) :
    Continuous (coefficientToNativeLocal Q hdim i) := by
  let Z := nativeTwoFormVectorCore Q
  have hlocal : Continuous (fun q : coefficientLocalDomain Q i =>
      (localNativeHomeomorph Q hdim i q).1) :=
    continuous_subtype_val.comp (localNativeHomeomorph Q hdim i).continuous
  have htotal : Continuous (fun q : coefficientLocalDomain Q i =>
      (Z.localTriv i).toOpenPartialHomeomorph.symm
        (localNativeHomeomorph Q hdim i q).1) :=
    (Z.localTriv i).toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
      hlocal (by intro q; exact ⟨q.2,Set.mem_univ _⟩)
  apply continuous_induced_rng.mpr
  apply continuous_induced_rng.mpr
  exact htotal

/-- The independent native Hodge sphere's local chart, constructed directly
from native bundle coordinates and the explicit normalized form map. -/
def nativeLocalTrivializationHomeomorph (i : atlas E M) :
    nativeLocalSphereTotal Q i ≃ₜ coefficientLocalDomain Q i where
  toFun := nativeLocalToCoefficient Q hdim i
  invFun := coefficientToNativeLocal Q hdim i
  left_inv := coefficientToNativeLocal_right Q hdim i
  right_inv := nativeLocalToCoefficient_left Q hdim i
  continuous_toFun := nativeLocalToCoefficient_continuous Q hdim i
  continuous_invFun := coefficientToNativeLocal_continuous Q hdim i

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereLocalTrivialization
