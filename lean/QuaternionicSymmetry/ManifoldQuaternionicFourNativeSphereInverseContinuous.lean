import QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereInverseLocal

/-! Continuity of the inverse global sphere map follows from the explicit
jointly smooth native coefficient extraction and the original twistor-sphere
local homeomorphisms. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereInverseContinuous

open ManifoldQuaternionicMetric
open ManifoldQuaternionicFourNativeSmoothCore
open ManifoldQuaternionicFourNativeSphereLocalCharts
open ManifoldQuaternionicFourNativeSphereBundleEquiv
open ManifoldQuaternionicFourNativeSphereInverseLocal
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

include hdim in
private theorem continuous_on (i : atlas E M) :
    ContinuousOn (nativeSphereToTwistor Q hdim)
      {p : NativeSphereBundleTotal Q |
        p.1.1 ∈ Q.frames.adaptedCore.baseSet i} := by
  rw [continuousOn_iff_continuous_restrict]
  let T : Set (NativeSphereBundleTotal Q) :=
    {p | p.1.1 ∈ Q.frames.adaptedCore.baseSet i}
  let Z := nativeTwoFormVectorCore Q
  have htotal : Continuous (fun p : T => (p.1.1 : Z.TotalSpace)) :=
    continuous_subtype_val.comp continuous_subtype_val
  have htriv : Continuous (fun p : T => Z.localTriv i p.1.1) :=
    (Z.localTriv i).continuousOn.comp_continuous htotal
      (by intro p; exact p.2)
  have hnative : Continuous (fun p : T =>
      nativeLocalCoordinate Q hdim i p.1 p.2) :=
    htriv.subtype_mk _
  have hlocal : Continuous (fun p : T =>
      (localNativeHomeomorph Q hdim i).symm
        (nativeLocalCoordinate Q hdim i p.1 p.2)) :=
    (localNativeHomeomorph Q hdim i).symm.continuous.comp hnative
  have hbase : Continuous (fun p : T =>
      (⟨p.1.1.1,p.2⟩ :
        {x : M // x ∈ Q.frames.adaptedCore.baseSet i})) := by
    exact (continuous_fst.comp htriv).subtype_mk _
  have hcoeff : Continuous (fun p : T =>
      ((localNativeHomeomorph Q hdim i).symm
        (nativeLocalCoordinate Q hdim i p.1 p.2)).1.2) :=
    continuous_snd.comp (continuous_subtype_val.comp hlocal)
  have hpair : Continuous (fun p : T =>
      ((⟨p.1.1.1,p.2⟩ :
          {x : M // x ∈ Q.frames.adaptedCore.baseSet i}),
        ((localNativeHomeomorph Q hdim i).symm
          (nativeLocalCoordinate Q hdim i p.1 p.2)).1.2)) :=
    hbase.prodMk hcoeff
  have htwistor : Continuous (fun p : T =>
      ((localTrivializationHomeomorph Q i).symm
        ((⟨p.1.1.1,p.2⟩ :
            {x : M // x ∈ Q.frames.adaptedCore.baseSet i}),
          ((localNativeHomeomorph Q hdim i).symm
            (nativeLocalCoordinate Q hdim i p.1 p.2)).1.2)).1) :=
    continuous_subtype_val.comp
      ((localTrivializationHomeomorph Q i).symm.continuous.comp hpair)
  exact htwistor.congr (by
    intro p
    change pointOfLocal Q i p.1.1.1 p.2
      ((localNativeHomeomorph Q hdim i).symm
        (nativeLocalCoordinate Q hdim i p.1 p.2)).1.2 =
          nativeSphereToTwistor Q hdim p.1
    exact (nativeSphereToTwistor_local Q hdim i p.1 p.2).symm)

include hdim in
theorem nativeSphereToTwistor_continuous :
    Continuous (nativeSphereToTwistor Q hdim) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let Z := nativeTwoFormVectorCore Q
  let k := Q.frames.adaptedCore.indexAt p.1.1
  have hopen : IsOpen {q : NativeSphereBundleTotal Q |
      q.1.1 ∈ Q.frames.adaptedCore.baseSet k} :=
    (Z.isOpen_baseSet k).preimage
      (Z.continuous_proj.comp continuous_subtype_val)
  exact (continuous_on Q hdim k).continuousAt
    (hopen.mem_nhds (Q.frames.adaptedCore.mem_baseSet_at _))

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereInverseContinuous
