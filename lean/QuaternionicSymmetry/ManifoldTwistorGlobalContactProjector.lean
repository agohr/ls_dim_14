import QuaternionicSymmetry.ManifoldTwistorRawContactProjectorCovariance
import QuaternionicSymmetry.ManifoldTwistorGlobalComplexSmooth

/-! The connection horizontal projection on the actual twistor tangent
bundle. Its fixed-chart formula is the checked smooth local projector, and
it commutes with the true tangent derivative of every chart transition. -/

namespace QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex

open QuaternionicSymmetry.ManifoldTwistorSphereBundle
open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldTwistorCoefficientSphere
open QuaternionicSymmetry.ManifoldTwistorVerticalComplex
open QuaternionicSymmetry.ManifoldTwistorHorizontalConnection
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open scoped Manifold ContDiff Topology

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : CompatibleTangentConnection Q)

private abbrev I := (𝓘(ℝ,E)).prod (𝓡 2)

def horizontalProjection (z : SphereBundleTotal Q)
    (v : TangentSpace (I (E := E)) z) : TangentSpace (I (E := E)) z :=
  (connectionTangentEquiv Q D z).symm
    ((connectionTangentEquiv Q D z v).1,0)

def horizontalProjectionBundleMap
    (t : TangentBundle (I (E := E)) (SphereBundleTotal Q)) :
    TangentBundle (I (E := E)) (SphereBundleTotal Q) :=
  ⟨t.1,horizontalProjection Q D t.1 t.2⟩

theorem horizontalProjection_center_coordinates (z : SphereBundleTotal Q)
    (v : TangentSpace (I (E := E)) z) :
    let y := (extChartAt 𝓘(ℝ,E) z.1) z.1
    localHorizontalProjection Q D z.1 ((y,v.1),⟨z.2,v.2⟩) =
      ((y,(horizontalProjection Q D z v).1),
        ⟨z.2,(horizontalProjection Q D z v).2⟩) := by
  let a := coefficientSphereHomeomorph.symm z.2
  have hs : coefficientSphereHomeomorph a = z.2 :=
    coefficientSphereHomeomorph.apply_symm_apply z.2
  let y := (extChartAt 𝓘(ℝ,E) z.1) z.1
  have hy : y ∈ (extChartAt 𝓘(ℝ,E) z.1).target :=
    (extChartAt 𝓘(ℝ,E) z.1).map_source (mem_extChartAt_source z.1)
  have h := localHorizontalProjection_eq_horizontalLift Q D z.1 y hy a v.1
    (hs ▸ v.2)
  have hP : horizontalProjection Q D z v =
      (v.1,(sphereTangentVerticalEquiv a).symm
        (-(connectionVertical Q D z.1 y hy a v.1))) := by
    simp [horizontalProjection, connectionTangentEquiv, connectionSplit,
      preferredTangentEquiv]
    change ((LinearEquiv.refl ℝ E).prodCongr (sphereTangentVerticalEquiv a)).symm
      ((((LinearEquiv.refl ℝ E).prodCongr (sphereTangentVerticalEquiv a)) v).1,
        -(connectionVertical Q D z.1 y hy a)
          (((LinearEquiv.refl ℝ E).prodCongr (sphereTangentVerticalEquiv a)) v).1) =
      (v.1,-(sphereTangentVerticalEquiv a).symm
        ((connectionVertical Q D z.1 y hy a) v.1))
    simp [LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply]
  rw [hP]
  simpa only [hs] using h

theorem horizontalProjection_rawChart_conjugacy (p : M)
    (z : SphereBundleTotal Q)
    (hp : z ∈ ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.source)
    (v : TangentSpace (I (E := E)) z) :
    rawTangentCoordinates Q p ⟨z,horizontalProjection Q D z v⟩ =
      localHorizontalProjection Q D p (rawTangentCoordinates Q p ⟨z,v⟩) := by
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
  have hcenter := horizontalProjection_center_coordinates Q D z v
  have hcov := rawTangentTransition_horizontalProjection Q D x p y hy a v.1
    (hs ▸ v.2)
  rw [rawTangentCoordinates_eq_transition Q p z hp
    (horizontalProjection Q D z v),
    rawTangentCoordinates_eq_transition Q p z hp v]
  rw [← hcenter]
  simpa only [x,y,hs] using hcov

/-- The metric connection horizontal projection is a smooth endomorphism
of the actual twistor tangent bundle. -/
theorem horizontalProjectionBundleMap_smooth :
    ContMDiff (I (E := E)).tangent (I (E := E)).tangent ∞
      (horizontalProjectionBundleMap Q D) := by
  intro t
  let p := t.1.1
  let U : Set (TangentBundle (I (E := E)) (SphereBundleTotal Q)) :=
    (fun v => v.1) ⁻¹'
      ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.source
  have ht : t ∈ U :=
    ((sphereCore Q).mem_localTriv_source (achart E p) t.1).mpr
      (by rw [← (sphereCore Q).baseSet_at]; exact (sphereCore Q).mem_baseSet_at p)
  have hOpen : IsOpen U :=
    ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.open_source.preimage
      (FiberBundle.continuous_proj (E × EuclideanSpace ℝ (Fin 2))
        (TangentSpace (I (E := E)) (M := SphereBundleTotal Q)))
  have hC := rawTangentCoordinates_smoothOn Q p
  have hMapC : Set.MapsTo (rawTangentCoordinates Q p) U
      (localDomain (E := E) p) := by
    intro v hv
    have hx : v.1.1 ∈ (extChartAt 𝓘(ℝ,E) p).source := by
      have hv' := ((sphereCore Q).mem_localTriv_source (achart E p) v.1).mp hv
      rw [← (sphereCore Q).baseSet_at] at hv'
      simpa only [sphereCore, ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
        tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ,E)] using hv'
    exact (extChartAt 𝓘(ℝ,E) p).map_source hx
  have hPC : ContMDiffOn (I (E := E)).tangent (IX (E := E)) ∞
      (localHorizontalProjection Q D p ∘ rawTangentCoordinates Q p) U :=
    (localHorizontalProjection_smooth Q D p).comp hC hMapC
  have hMapP : Set.MapsTo
      (localHorizontalProjection Q D p ∘ rawTangentCoordinates Q p)
      U (localDomain (E := E) p) := by
    intro v hv
    exact hMapC hv
  have hFinal : ContMDiffOn (I (E := E)).tangent (I (E := E)).tangent ∞
      (rawTangentCoordinatesInv Q p ∘
        (localHorizontalProjection Q D p ∘ rawTangentCoordinates Q p)) U :=
    (rawTangentCoordinatesInv_smoothOn Q p).comp hPC hMapP
  have hEq : ∀ v ∈ U,
      horizontalProjectionBundleMap Q D v =
        rawTangentCoordinatesInv Q p
          (localHorizontalProjection Q D p (rawTangentCoordinates Q p v)) := by
    intro v hv
    have hc := horizontalProjection_rawChart_conjugacy Q D p v.1 hv v.2
    have hi := rawTangentCoordinatesInv_left Q p v.1 hv
      (horizontalProjection Q D v.1 v.2)
    exact hi.symm.trans (congrArg (rawTangentCoordinatesInv Q p) hc)
  have hOn : ContMDiffOn (I (E := E)).tangent (I (E := E)).tangent ∞
      (horizontalProjectionBundleMap Q D) U :=
    hFinal.congr (fun v hv => by simpa only [Function.comp_apply] using hEq v hv)
  exact hOn.contMDiffAt (hOpen.mem_nhds ht)

end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
