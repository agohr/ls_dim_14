import QuaternionicSymmetry.ManifoldTwistorCenterRawDerivative

/-!
# Conjugacy of the pointwise twistor complex field with a fixed raw chart

The pointwise almost-complex endomorphism on the actual twistor total-space
tangent fiber is transported by the genuine tangent map of any fixed raw
bundle chart to the smooth local complex operator. This uses the center
chart derivative and the true sphere transition tangent covariance.
-/

namespace QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
open QuaternionicSymmetry.ManifoldTwistorSphereBundle
open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldTwistorCoefficientSphere
open QuaternionicSymmetry.ManifoldTwistorLocalAlmostComplex
open QuaternionicSymmetry.ManifoldTwistorVerticalComplex
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
 [Nontrivial E] [FiniteDimensional ℝ E]
 [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
private abbrev I := (𝓘(ℝ,E)).prod (𝓡 2)

theorem fixedRawChart_overlap (p q : M) (z : SphereBundleTotal Q)
    (hp : z ∈ ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.source)
    (hq : z ∈ ((sphereCore Q).localTriv (achart E q)).toOpenPartialHomeomorph.source) :
    fixedRawChart Q q z = rawSphereTransition Q p q (fixedRawChart Q p z) := by
  let y := (fixedRawChart Q p z).1
  let s := (fixedRawChart Q p z).2
  have hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q := by
    have hpx : z.1 ∈ (extChartAt 𝓘(ℝ,E) p).source := by
      have hp' := ((sphereCore Q).mem_localTriv_source (achart E p) z).mp hp
      rw [← (sphereCore Q).baseSet_at] at hp'
      simpa only [sphereCore, ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
        tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ,E)] using hp'
    have hqx : z.1 ∈ (extChartAt 𝓘(ℝ,E) q).source := by
      have hq' := ((sphereCore Q).mem_localTriv_source (achart E q) z).mp hq
      rw [← (sphereCore Q).baseSet_at] at hq'
      simpa only [sphereCore, ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
        tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ,E)] using hq'
    exact ⟨(extChartAt 𝓘(ℝ,E) p).map_source hpx,
      by simpa only [y, fixedRawChart,
        (extChartAt 𝓘(ℝ,E) p).left_inv hpx] using hqx⟩
  have htrans := fixedRawChart_transition Q p q y s hy
  rw [fixedRawChartInv_left Q p z hp] at htrans
  exact htrans

theorem fixedRawChart_center_value (z : SphereBundleTotal Q) :
    fixedRawChart Q z.1 z = ((extChartAt 𝓘(ℝ,E) z.1) z.1,z.2) := by
  apply Prod.ext
  · rfl
  · change euclideanSphereCoordChange Q (achart E z.1) (achart E z.1)
      z.1 z.2 = z.2
    exact euclideanSphereCoordChange_self Q (achart E z.1) z.1
      (mem_chart_source E z.1) z.2

theorem fixedRawChart_mfderiv_eq_rawTransition (p : M)
    (z : SphereBundleTotal Q)
    (hp : z ∈ ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.source) :
    mfderiv (I (E := E)) (I (E := E)) (fixedRawChart Q p) z =
    mfderiv (I (E := E)) (I (E := E))
      (rawSphereTransition Q z.1 p)
      ((extChartAt 𝓘(ℝ,E) z.1) z.1,z.2) := by
  let x := z.1
  let y := (extChartAt 𝓘(ℝ,E) x) x
  let s : geometricSphere := z.2
  have hc : z ∈ ((sphereCore Q).localTriv (achart E x)).toOpenPartialHomeomorph.source :=
    ((sphereCore Q).mem_localTriv_source (achart E x) z).mpr
      (by rw [← (sphereCore Q).baseSet_at]; exact (sphereCore Q).mem_baseSet_at x)
  have hval : fixedRawChart Q x z = (y,s) := fixedRawChart_center_value Q z
  have hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) x p := by
    have hx : x ∈ (extChartAt 𝓘(ℝ,E) p).source := by
      have hp' := ((sphereCore Q).mem_localTriv_source (achart E p) z).mp hp
      rw [← (sphereCore Q).baseSet_at] at hp'
      simpa only [sphereCore, ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
        tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ,E)] using hp'
    exact ⟨(extChartAt 𝓘(ℝ,E) x).map_source (mem_extChartAt_source x),
      by simpa only [y, (extChartAt 𝓘(ℝ,E) x).left_inv (mem_extChartAt_source x)] using hx⟩
  have hEq : fixedRawChart Q p =ᶠ[𝓝 z]
      (rawSphereTransition Q x p ∘ fixedRawChart Q x) := by
    have hOpen : IsOpen
        (((sphereCore Q).localTriv (achart E x)).toOpenPartialHomeomorph.source ∩
         ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.source) :=
      ((sphereCore Q).localTriv (achart E x)).toOpenPartialHomeomorph.open_source.inter
        ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.open_source
    filter_upwards [hOpen.mem_nhds ⟨hc,hp⟩] with w hw
    exact fixedRawChart_overlap Q x p w hw.1 hw.2
  have hCenter : MDifferentiableAt (I (E := E)) (I (E := E))
      (fixedRawChart Q x) z :=
    ((fixedRawChart_smoothOn Q x).contMDiffAt
      (((sphereCore Q).localTriv (achart E x)).toOpenPartialHomeomorph.open_source.mem_nhds hc)).mdifferentiableAt (by simp)
  have hTrans : MDifferentiableAt (I (E := E)) (I (E := E))
      (rawSphereTransition Q x p) (fixedRawChart Q x z) := by
    simpa only [hval] using
      (rawSphereTransition_smoothAt Q x p y s hy).mdifferentiableAt (by simp)
  have hder := Filter.EventuallyEq.mfderiv_eq (I := I (E := E))
    (I' := I (E := E)) hEq
  rw [mfderiv_comp z hTrans hCenter,
    fixedRawChart_center_mfderiv Q z] at hder
  rw [hval] at hder
  simpa only [x,y,s, ContinuousLinearMap.comp_id] using hder

def rawTangentCoordinates (p : M)
    (v : TangentBundle (I (E := E)) (SphereBundleTotal Q)) : X (E := E) :=
  productTangentCoordinates
    (tangentMap (I (E := E)) (I (E := E)) (fixedRawChart Q p) v)

theorem rawTangentCoordinates_eq_transition (p : M)
    (z : SphereBundleTotal Q)
    (hp : z ∈ ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.source)
    (v : TangentSpace (I (E := E)) z) :
    rawTangentCoordinates Q p ⟨z,v⟩ =
    rawTangentTransition Q z.1 p
      (((extChartAt 𝓘(ℝ,E) z.1) z.1,v.1),⟨z.2,v.2⟩) := by
  let x := z.1
  have hc : z ∈ ((sphereCore Q).localTriv (achart E x)).toOpenPartialHomeomorph.source :=
    ((sphereCore Q).mem_localTriv_source (achart E x) z).mpr
      (by rw [← (sphereCore Q).baseSet_at]; exact (sphereCore Q).mem_baseSet_at x)
  have hval := fixedRawChart_overlap Q x p z hc hp
  rw [fixedRawChart_center_value Q z] at hval
  simp only [rawTangentCoordinates, productTangentCoordinates, tangentMap,
    rawTangentTransition]
  rw [fixedRawChart_mfderiv_eq_rawTransition Q p z hp]
  rw [hval]
  rfl

theorem tangentComplex_center_coordinates (D : CompatibleTangentConnection Q)
    (z : SphereBundleTotal Q) (v : TangentSpace (I (E := E)) z) :
    let y := (extChartAt 𝓘(ℝ,E) z.1) z.1
    localComplexTrivialized Q D z.1
      ((y,v.1),⟨z.2,v.2⟩) =
      ((y,(tangentComplex Q D z v).1),
        ⟨z.2,(tangentComplex Q D z v).2⟩) := by
  let a := coefficientSphereHomeomorph.symm z.2
  have hs : coefficientSphereHomeomorph a = z.2 :=
    coefficientSphereHomeomorph.apply_symm_apply z.2
  let y := (extChartAt 𝓘(ℝ,E) z.1) z.1
  have hy : y ∈ (extChartAt 𝓘(ℝ,E) z.1).target :=
    (extChartAt 𝓘(ℝ,E) z.1).map_source (mem_extChartAt_source z.1)
  have h := localComplexBundleMap_eq_local Q D z.1 y hy a v.1
    (hs ▸ v.2)
  have hT : tangentComplex Q D z v =
      ((localTwistorComplex Q D z.1 y hy a
        (v.1,sphereTangentVerticalEquiv a (hs ▸ v.2))).1,
       (sphereTangentVerticalEquiv a).symm
        (localTwistorComplex Q D z.1 y hy a
          (v.1,sphereTangentVerticalEquiv a (hs ▸ v.2))).2) := by
    rfl
  rw [hT]
  simpa only [localComplexTrivialized, hs] using
    congrArg (fun w : Y (E := E) => ((y,w.1),w.2)) h

theorem tangentComplex_rawChart_conjugacy (D : CompatibleTangentConnection Q)
    (p : M) (z : SphereBundleTotal Q)
    (hp : z ∈ ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.source)
    (v : TangentSpace (I (E := E)) z) :
    rawTangentCoordinates Q p ⟨z,tangentComplex Q D z v⟩ =
      localComplexTrivialized Q D p (rawTangentCoordinates Q p ⟨z,v⟩) := by
  let x := z.1
  let y := (extChartAt 𝓘(ℝ,E) x) x
  let a := coefficientSphereHomeomorph.symm z.2
  have hs : coefficientSphereHomeomorph a = z.2 :=
    coefficientSphereHomeomorph.apply_symm_apply z.2
  have hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) x p := by
    have hx : x ∈ (extChartAt 𝓘(ℝ,E) p).source := by
      have hp' := ((sphereCore Q).mem_localTriv_source (achart E p) z).mp hp
      rw [← (sphereCore Q).baseSet_at] at hp'
      simpa only [sphereCore, ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
        tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ,E)] using hp'
    exact ⟨(extChartAt 𝓘(ℝ,E) x).map_source (mem_extChartAt_source x),
      by simpa only [y, (extChartAt 𝓘(ℝ,E) x).left_inv (mem_extChartAt_source x)] using hx⟩
  have hcenter := tangentComplex_center_coordinates Q D z v
  have hcov := rawTangentTransition_complex Q D x p y hy a v.1 (hs ▸ v.2)
  rw [rawTangentCoordinates_eq_transition Q p z hp
    (tangentComplex Q D z v),
    rawTangentCoordinates_eq_transition Q p z hp v]
  rw [← hcenter]
  simpa only [x,y,hs] using hcov
end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
