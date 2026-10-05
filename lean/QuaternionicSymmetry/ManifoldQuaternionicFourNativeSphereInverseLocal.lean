import QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereForwardContinuous
import QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereLocalCharts

/-! In each adapted chart, the global inverse is exactly the point built from
the continuous native coefficient extraction. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereInverseLocal

open ManifoldQuaternionicMetric
open ManifoldQuaternionicFourNativeSmoothCore
open ManifoldQuaternionicFourNativeNegativeSphereSet
open ManifoldQuaternionicFourNativeSphereFormSmooth
open ManifoldQuaternionicFourNativeSphereLocalCharts
open ManifoldQuaternionicFourNativeSphereBundleEquiv
open ManifoldQuaternionicFourNativeSphereLocalCoordinate
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
local instance (i : atlas E M) : TopologicalSpace (coefficientLocalDomain Q i) := by
  unfold coefficientLocalDomain
  infer_instance
local instance (i : atlas E M) : TopologicalSpace (nativeLocalDomain Q i) := by
  unfold nativeLocalDomain
  infer_instance

def nativeLocalCoordinate (i : atlas E M)
    (p : NativeSphereBundleTotal Q)
    (hi : p.1.1 ∈ Q.frames.adaptedCore.baseSet i) :
    nativeLocalDomain Q i := by
  let Z := nativeTwoFormVectorCore Q
  refine ⟨Z.localTriv i p.1, ⟨hi, ?_⟩⟩
  exact (nativeNegativeSphereTotal_iff_chart Q hdim p.1 i hi).mp p.2

theorem nativeLocalCoordinate_apply (i : atlas E M)
    (p : NativeSphereBundleTotal Q)
    (hi : p.1.1 ∈ Q.frames.adaptedCore.baseSet i) :
    (nativeLocalCoordinate Q hdim i p hi).1 =
      (nativeTwoFormVectorCore Q).localTriv i p.1 := rfl

theorem nativeSphereToTwistor_local (i : atlas E M)
    (p : NativeSphereBundleTotal Q)
    (hi : p.1.1 ∈ Q.frames.adaptedCore.baseSet i) :
    nativeSphereToTwistor Q hdim p =
      pointOfLocal Q i p.1.1 hi
        ((localNativeHomeomorph Q hdim i).symm
          (nativeLocalCoordinate Q hdim i p hi)).1.2 := by
  let Z := nativeTwoFormVectorCore Q
  let q := nativeLocalCoordinate Q hdim i p hi
  let c := ((localNativeHomeomorph Q hdim i).symm q).1.2
  let z := pointOfLocal Q i p.1.1 hi c
  have hz : projection Q z = p.1.1 :=
    projection_pointOfLocal Q i p.1.1 hi c
  have hzi : projection Q z ∈ Q.frames.adaptedCore.baseSet i := by
    simpa [hz] using hi
  have hlocal : nativeSphereForm Q i (p.1.1,
      ManifoldTwistorCoefficientSphere.coefficientSphereHomeomorph c) =
      (Z.localTriv i p.1).2 := by
    have h := (localNativeHomeomorph Q hdim i).apply_symm_apply q
    have hs := congrArg (fun u : nativeLocalDomain Q i => u.1.2) h
    exact hs
  have hcoord : Z.localTriv i (twistorToNativeSphere Q z).1 =
      Z.localTriv i p.1 := by
    apply Prod.ext
    · exact hz
    · rw [twistorToNative_local Q hdim i z hzi]
      rw [localCoordinate_pointOfLocal Q i p.1.1 hi c]
      exact hlocal
  have htotal : (twistorToNativeSphere Q z).1 = p.1 := by
    have hleft := (Z.localTriv i).toOpenPartialHomeomorph.left_inv
      (by simpa [hz] using hi :
        (twistorToNativeSphere Q z).1 ∈ (Z.localTriv i).source)
    have hright := (Z.localTriv i).toOpenPartialHomeomorph.left_inv
      (by simpa using hi : p.1 ∈ (Z.localTriv i).source)
    calc
      (twistorToNativeSphere Q z).1 =
          (Z.localTriv i).toOpenPartialHomeomorph.symm
            (Z.localTriv i (twistorToNativeSphere Q z).1) := hleft.symm
      _ = (Z.localTriv i).toOpenPartialHomeomorph.symm
            (Z.localTriv i p.1) := congrArg _ hcoord
      _ = p.1 := hright
  have hsphere : twistorToNativeSphere Q z = p := Subtype.ext htotal
  have heq := congrArg (nativeSphereToTwistor Q hdim) hsphere
  rw [nativeSphereToTwistor_left Q hdim] at heq
  exact heq.symm

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereInverseLocal
