import QuaternionicSymmetry.ManifoldTwistorProductTangentCoordinates

/-!
# Fixed raw chart of the twistor sphere bundle

A base manifold chart and its associated sphere-bundle trivialization give a
map to model base coordinates times the genuine geometric sphere. This map is
smooth on the open source of the trivialization.
-/

namespace QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
open QuaternionicSymmetry.ManifoldTwistorSphereBundle
open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldTwistorSphereManifold
open QuaternionicSymmetry.ManifoldTwistorCoefficientSphere
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
 [Nontrivial E] [FiniteDimensional ℝ E]
 [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
private abbrev I := (𝓘(ℝ,E)).prod (𝓡 2)

def fixedRawChart (p : M) (z : SphereBundleTotal Q) : E × geometricSphere :=
  ((extChartAt 𝓘(ℝ,E) p) z.1,
    ((sphereCore Q).localTriv (achart E p) z).2)

theorem fixedRawChart_smoothOn (p : M) :
    ContMDiffOn (I (E := E)) (I (E := E)) ∞
      (fixedRawChart Q p)
      ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.source := by
  let s : Set (SphereBundleTotal Q) :=
    ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.source
  have hsource : ∀ z ∈ s, z.1 ∈ (extChartAt 𝓘(ℝ,E) p).source := by
    intro z hz
    have hz' : z.1 ∈ (sphereCore Q).baseSet (achart E p) := by
      exact ((sphereCore Q).mem_localTriv_source (achart E p) z).mp hz
    simpa only [sphereCore, ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ,E)] using hz'
  have hbase : ContMDiffOn (I (E := E)) 𝓘(ℝ,E) ∞
      (fun z : SphereBundleTotal Q => (extChartAt 𝓘(ℝ,E) p) z.1) s :=
    (contMDiffOn_extChartAt (I := 𝓘(ℝ,E)) (x := p)).comp
      (sphereProjection_smooth Q).contMDiffOn (by
        intro z hz
        simpa only [extChartAt_source] using hsource z hz)
  have htriv := fixedTriv_smoothOn Q p
  have hsphere : ContMDiffOn (I (E := E)) (𝓡 2) ∞
      (fun z : SphereBundleTotal Q =>
        (((sphereCore Q).localTriv (achart E p) z) : M × geometricSphere).2) s :=
    contMDiff_snd.comp_contMDiffOn htriv
  exact hbase.prodMk hsphere

theorem fixedRawChart_tangent_smoothOn (p : M) :
    ContMDiffOn (I (E := E)).tangent (I (E := E)).tangent ∞
      (tangentMap (M := SphereBundleTotal Q) (M' := E × geometricSphere)
        (I (E := E)) (I (E := E)) (fixedRawChart Q p))
      ((fun v : TangentBundle (I (E := E)) (SphereBundleTotal Q) => v.1) ⁻¹'
        ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.source) := by
  let s : Set (SphereBundleTotal Q) :=
    ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.source
  have hs : IsOpen s :=
    ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.open_source
  have h : ContMDiffOn (I (E := E)).tangent (I (E := E)).tangent ∞
      (tangentMapWithin (M := SphereBundleTotal Q) (M' := E × geometricSphere)
        (I (E := E)) (I (E := E)) (fixedRawChart Q p) s)
      ((fun v : TangentBundle (I (E := E)) (SphereBundleTotal Q) => v.1) ⁻¹' s) :=
    (fixedRawChart_smoothOn Q p).contMDiffOn_tangentMapWithin (by simp)
      hs.uniqueMDiffOn
  apply h.congr
  intro v hv
  simp only [tangentMapWithin, tangentMap]
  rw [mfderivWithin_of_mem_nhds (hs.mem_nhds hv)]

def fixedRawChartInv (p : M) (ys : E × geometricSphere) : SphereBundleTotal Q :=
  ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.symm
    ((extChartAt 𝓘(ℝ,E) p).symm ys.1, ys.2)

def fixedRawTarget (p : M) : Set (E × geometricSphere) :=
  (extChartAt 𝓘(ℝ,E) p).target ×ˢ Set.univ

theorem fixedRawChartInv_smoothOn (p : M) :
    ContMDiffOn (I (E := E)) (I (E := E)) ∞
      (fixedRawChartInv Q p) (fixedRawTarget (E := E) p) := by
  let t := fixedRawTarget (E := E) p
  have hbase : ContMDiffOn (I (E := E)) 𝓘(ℝ,E) ∞
      (fun ys : E × geometricSphere => (extChartAt 𝓘(ℝ,E) p).symm ys.1) t :=
    (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) p).comp
      contMDiffOn_fst (by intro ys hys; exact hys.1)
  have hsphere : ContMDiffOn (I (E := E)) (𝓡 2) ∞
      (fun ys : E × geometricSphere => ys.2) t := contMDiffOn_snd
  have hpair := hbase.prodMk hsphere
  have hmaps : Set.MapsTo
      (fun ys : E × geometricSphere =>
        ((extChartAt 𝓘(ℝ,E) p).symm ys.1,ys.2)) t
      ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.target := by
    intro ys hys
    have hy : (extChartAt 𝓘(ℝ,E) p).symm ys.1 ∈
        (extChartAt 𝓘(ℝ,E) p).source :=
      (extChartAt 𝓘(ℝ,E) p).map_target hys.1
    apply ((sphereCore Q).mem_localTriv_target (achart E p)
      ((extChartAt 𝓘(ℝ,E) p).symm ys.1,ys.2)).mpr
    rw [← (sphereCore Q).baseSet_at]
    simpa only [sphereCore, ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ,E)] using hy
  exact (fixedTriv_inv_smoothOn Q p).comp hpair hmaps

theorem fixedRawChartInv_left (p : M) (z : SphereBundleTotal Q)
    (hz : z ∈ ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.source) :
    fixedRawChartInv Q p (fixedRawChart Q p z) = z := by
  let L := ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph
  have hx : z.1 ∈ (extChartAt 𝓘(ℝ,E) p).source := by
    have hz' : z.1 ∈ (sphereCore Q).baseSet (achart E p) :=
      ((sphereCore Q).mem_localTriv_source (achart E p) z).mp hz
    simpa only [sphereCore, ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ,E)] using hz'
  change L.symm ((extChartAt 𝓘(ℝ,E) p).symm
    ((extChartAt 𝓘(ℝ,E) p) z.1), (L z).2) = z
  rw [(extChartAt 𝓘(ℝ,E) p).left_inv hx]
  have hproj : (L z).1 = z.1 := by simp [L]
  convert L.left_inv hz using 1

theorem fixedRawChartInv_right (p : M) (ys : E × geometricSphere)
    (hys : ys ∈ fixedRawTarget (E := E) p) :
    fixedRawChart Q p (fixedRawChartInv Q p ys) = ys := by
  let L := ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph
  have hx : (extChartAt 𝓘(ℝ,E) p).symm ys.1 ∈
      (sphereCore Q).baseSet (achart E p) := by
    have hy := (extChartAt 𝓘(ℝ,E) p).map_target hys.1
    simpa only [sphereCore, ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ,E)] using hy
  have hw : ((extChartAt 𝓘(ℝ,E) p).symm ys.1,ys.2) ∈ L.target := by
    exact ((sphereCore Q).mem_localTriv_target (achart E p) _).mpr
      (by rwa [← (sphereCore Q).baseSet_at])
  have hr := L.right_inv hw
  change ((extChartAt 𝓘(ℝ,E) p) (L.symm
    ((extChartAt 𝓘(ℝ,E) p).symm ys.1,ys.2)).1,
    (L (L.symm ((extChartAt 𝓘(ℝ,E) p).symm ys.1,ys.2))).2) = ys
  rw [hr]
  have hproj : (L.symm ((extChartAt 𝓘(ℝ,E) p).symm ys.1,ys.2)).1 =
      (extChartAt 𝓘(ℝ,E) p).symm ys.1 :=
    ((sphereCore Q).localTriv (achart E p)).proj_symm_apply hw
  rw [hproj, (extChartAt 𝓘(ℝ,E) p).right_inv hys.1]
end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
