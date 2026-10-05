import QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereLocalCoordinate

/-! Continuity of the global twistor-to-native-Hodge sphere map follows
locally from the independently smooth native form and the genuine native
bundle trivializations. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereForwardContinuous

open ManifoldQuaternionicMetric
open ManifoldQuaternionicFourNativeSmoothCore
open ManifoldQuaternionicFourNativeSphereFormSmooth
open ManifoldQuaternionicFourNativeSphereBundleEquiv
open ManifoldQuaternionicFourNativeSphereLocalCoordinate
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

include hdim in
private theorem continuous_on (i : atlas E M) :
    ContinuousOn (twistorToNativeSphere Q)
      {z : TwistorSphere Q |
        projection Q z ∈ Q.frames.adaptedCore.baseSet i} := by
  rw [continuousOn_iff_continuous_restrict]
  let T : Set (TwistorSphere Q) :=
    {z | projection Q z ∈ Q.frames.adaptedCore.baseSet i}
  let Z := nativeTwoFormVectorCore Q
  have hbase : Continuous (fun z : T => projection Q z.1) :=
    (projection_continuous Q).comp continuous_subtype_val
  have hcoeff : Continuous (fun z : T =>
      coefficientSphereHomeomorph (localCoordinate Q i z.1 z.2)) :=
    coefficientSphereHomeomorph.continuous.comp
      (continuous_snd.comp (localTrivializationHomeomorph Q i).continuous)
  have hpair : Continuous (fun z : T =>
      (projection Q z.1,
        coefficientSphereHomeomorph (localCoordinate Q i z.1 z.2))) :=
    hbase.prodMk hcoeff
  have hform : Continuous (fun z : T =>
      nativeSphereForm Q i
        (projection Q z.1,
          coefficientSphereHomeomorph (localCoordinate Q i z.1 z.2))) :=
    ((nativeSphereForm_smooth Q i).continuousOn).comp_continuous hpair
      (by intro z; exact ⟨z.2, Set.mem_univ _⟩)
  have hcoords : Continuous (fun z : T =>
      (projection Q z.1,
        nativeSphereForm Q i
          (projection Q z.1,
            coefficientSphereHomeomorph (localCoordinate Q i z.1 z.2)))) :=
    hbase.prodMk hform
  have htotal : Continuous (fun z : T =>
      (Z.localTriv i).toOpenPartialHomeomorph.symm
        (projection Q z.1,
          nativeSphereForm Q i
            (projection Q z.1,
              coefficientSphereHomeomorph (localCoordinate Q i z.1 z.2)))) :=
    (Z.localTriv i).toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
      hcoords (by intro z; exact ⟨z.2, Set.mem_univ _⟩)
  apply continuous_induced_rng.mpr
  exact htotal.congr (by
    intro z
    let p := (twistorToNativeSphere Q z.1).1
    have hp : p.1 ∈ Z.baseSet i := z.2
    have heq : (Z.localTriv i) p =
        (projection Q z.1,
          nativeSphereForm Q i
            (projection Q z.1,
              coefficientSphereHomeomorph (localCoordinate Q i z.1 z.2))) := by
      apply Prod.ext
      · rfl
      · exact twistorToNative_local Q hdim i z.1 z.2
    change (Z.localTriv i).toOpenPartialHomeomorph.symm _ = p
    rw [← heq]
    exact (Z.localTriv i).toOpenPartialHomeomorph.left_inv
      (by simpa using hp))

include hdim in
theorem twistorToNativeSphere_continuous :
    Continuous (twistorToNativeSphere Q) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  let k := Q.frames.adaptedCore.indexAt (projection Q z)
  have hopen : IsOpen {w : TwistorSphere Q |
      projection Q w ∈ Q.frames.adaptedCore.baseSet k} :=
    (Q.frames.adaptedCore.isOpen_baseSet k).preimage (projection_continuous Q)
  exact (continuous_on Q hdim k).continuousAt
    (hopen.mem_nhds (Q.frames.adaptedCore.mem_baseSet_at _))

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereForwardContinuous
