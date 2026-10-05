import QuaternionicSymmetry.ManifoldQuaternionicInducedTotalGeodesy
import QuaternionicSymmetry.ManifoldQuaternionicCoordinateConnection
import Mathlib.Geometry.Manifold.MFDeriv.Tangent

/-! Derivatives and solder forms of an immersion in arbitrary fixed charts. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicImmersionCharts
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedLocalIntertwining
open ManifoldQuaternionicInducedTotalGeodesy
open ManifoldQuaternionicConnection
open ManifoldQuaternionicCoordinateConnection
open Filter
open scoped Manifold ContDiff Topology
noncomputable section
variable {E F M N : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [FiniteDimensional ℝ F] [Nontrivial F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
variable (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
  (R : PositiveQuaternionicKahlerGeometry (E := F) (M := N))
  (ι : N → M) (hSmooth : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι)

include hSmooth

lemma overlap_eventually (q : N) (p : M) (y : F)
    (hy : y ∈ immersionChartOverlap (E := E) (F := F) ι q p) :
    ∀ᶠ z in 𝓝 y, z ∈ immersionChartOverlap (E := E) (F := F) ι q p := by
  have hs := (isOpen_extChartAt_target (I := 𝓘(ℝ,F)) q).mem_nhds hy.1
  have hc : ContinuousAt (fun z => ι ((extChartAt 𝓘(ℝ,F) q).symm z)) y :=
    hSmooth.continuous.continuousAt.comp
      (((contMDiffOn_extChartAt_symm (n := ∞) q y hy.1).contMDiffAt hs).continuousAt)
  have ht := hc ((isOpen_extChartAt_source p).mem_nhds hy.2)
  filter_upwards [hs, ht] with z hz hzt
  exact ⟨hz, hzt⟩

lemma localBaseMap_contDiffAt (q : N) (p : M) (y : F)
    (hy : y ∈ immersionChartOverlap (E := E) (F := F) ι q p) :
    ContDiffAt ℝ ∞ (localBaseMap (E := E) (F := F) ι q p) y := by
  have hi := (contMDiffOn_extChartAt_symm (n := ∞) q y hy.1).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) q).mem_nhds hy.1)
  have ho := contMDiffAt_extChartAt' (I := 𝓘(ℝ,E)) (n := ∞)
    (by simpa only [← extChartAt_source 𝓘(ℝ,E)] using hy.2)
  exact (ho.comp y (hSmooth.contMDiffAt.comp y hi)).contDiffAt

lemma localBaseMap_fderiv (q : N) (p : M) (y : F)
    (hy : y ∈ immersionChartOverlap (E := E) (F := F) ι q p) :
    fderiv ℝ (localBaseMap (E := E) (F := F) ι q p) y =
      localDerivative ι (achart F q) (achart E p)
        ((extChartAt 𝓘(ℝ,F) q).symm y) := by
  let x := (extChartAt 𝓘(ℝ,F) q).symm y
  have hx : x ∈ (extChartAt 𝓘(ℝ,F) q).source :=
    (extChartAt 𝓘(ℝ,F) q).map_target hy.1
  have hi := ((contMDiffOn_extChartAt_symm (n := ∞) q y hy.1).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) q).mem_nhds hy.1)).mdifferentiableAt
      (by simp)
  have hm := hSmooth.mdifferentiable (by simp) x
  have ho := (contMDiffAt_extChartAt' (I := 𝓘(ℝ,E)) (n := ∞)
    (by simpa only [← extChartAt_source 𝓘(ℝ,E)] using hy.2)).mdifferentiableAt
      (by simp)
  have hc := mfderiv_comp y ho (hm.comp y hi)
  rw [mfderiv_comp y hm hi, mfderiv_eq_fderiv] at hc
  have hfrom : (tangentBundleCore 𝓘(ℝ,F) N).coordChange
      (achart F q) (achart F x) x =
        mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F) (extChartAt 𝓘(ℝ,F) q).symm y := by
    rw [← TangentBundle.symmL_trivializationAt_eq_core
      (by simpa only [extChartAt_source] using hx)]
    rw [TangentBundle.symmL_trivializationAt
      (by simpa only [extChartAt_source] using hx)]
    simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ]
    rw [(extChartAt 𝓘(ℝ,F) q).right_inv hy.1]
  change fderiv ℝ (localBaseMap (E := E) (F := F) ι q p) y =
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) p) (ι x)).comp
      ((mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x).comp
        (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F) (extChartAt 𝓘(ℝ,F) q).symm y)) at hc
  rw [← hfrom] at hc
  rw [localDerivative]
  exact hc.trans (by
    congr 1
    exact (tangentCoordChange_toChart_eq_mfderiv (I := 𝓘(ℝ,E)) p (ι x) hy.2).symm)

lemma adapted_eq_solder_derivative (q : N) (p : M) (y : F)
    (hy : y ∈ immersionChartOverlap (E := E) (F := F) ι q p) :
    adaptedRectangularDerivative P R ι q p y =
      (solder P.tangent p (localBaseMap (E := E) (F := F) ι q p y)).comp
        ((fderiv ℝ (localBaseMap (E := E) (F := F) ι q p) y).comp
          (coordinateInverse R.tangent q y)) := by
  rw [localBaseMap_fderiv ι hSmooth q p y hy]
  have hG : localBaseMap (E := E) (F := F) ι q p y ∈ (extChartAt 𝓘(ℝ,E) p).target :=
    (extChartAt 𝓘(ℝ,E) p).map_source hy.2
  rw [solder_eq_toFrame P.tangent p _ hG]
  simp only [localBaseMap, (extChartAt 𝓘(ℝ,E) p).left_inv hy.2]
  rfl

lemma adapted_differentiableAt (q : N) (p : M) (y : F)
    (hy : y ∈ immersionChartOverlap (E := E) (F := F) ι q p) :
    DifferentiableAt ℝ (adaptedRectangularDerivative P R ι q p) y := by
  have hG := (contDiffAt_infty.mp (localBaseMap_contDiffAt ι hSmooth q p y hy)) 2
  have ht := solder_contDiffAt P.tangent p (localBaseMap (E := E) (F := F) ι q p y)
    ((extChartAt 𝓘(ℝ,E) p).map_source hy.2)
  have hs := coordinateInverse_contDiffAt R.tangent q y hy.1
  have hd := (hG.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h := (ht.differentiableAt (by norm_num) |>.comp y
    (hG.differentiableAt (by norm_num))).clm_comp
      (hd.clm_comp (hs.differentiableAt (by norm_num)))
  apply h.congr_of_eventuallyEq
  filter_upwards [overlap_eventually ι hSmooth q p y hy] with z hz
  exact adapted_eq_solder_derivative P R ι hSmooth q p z hz

lemma solder_covariance (q : N) (p : M) (y : F)
    (hy : y ∈ immersionChartOverlap (E := E) (F := F) ι q p) :
    (adaptedRectangularDerivative P R ι q p y).comp (solder R.tangent q y) =
      (solder P.tangent p (localBaseMap (E := E) (F := F) ι q p y)).comp
        (fderiv ℝ (localBaseMap (E := E) (F := F) ι q p) y) := by
  rw [adapted_eq_solder_derivative P R ι hSmooth q p y hy]
  ext v
  have hs := congrArg (fun L : F →L[ℝ] F => L v)
    (coordinateInverse_left R.tangent q y hy.1)
  change coordinateInverse R.tangent q y (solder R.tangent q y v) = v at hs
  simp only [ContinuousLinearMap.comp_apply, hs]


omit hSmooth in
lemma adapted_inner
    (hR : IsInducedQuaternionicGeometry P R ι)
    (q : N) (p : M) (y : F)
    (hy : y ∈ immersionChartOverlap (E := E) (F := F) ι q p) (v w : F) :
    inner ℝ (adaptedRectangularDerivative P R ι q p y v)
      (adaptedRectangularDerivative P R ι q p y w) = inner ℝ v w := by
  let x := (extChartAt 𝓘(ℝ,F) q).symm y
  let i := achart F q
  let j := achart E p
  let k := achart F x
  let B := (tangentBundleCore 𝓘(ℝ,F) N).coordChange i k x
  let U := R.tangent.frames.fromFrame i x
  have hi : x ∈ (tangentBundleCore 𝓘(ℝ,F) N).baseSet i := by
    simpa only [i, x, tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ,F)]
      using (extChartAt 𝓘(ℝ,F) q).map_target hy.1
  have hj : ι x ∈ (tangentBundleCore 𝓘(ℝ,E) M).baseSet j := by
    simpa only [j, x, tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ,E)]
      using hy.2
  have hk := (tangentBundleCore 𝓘(ℝ,F) N).mem_baseSet_at x
  have hcancel (a : F) : (tangentBundleCore 𝓘(ℝ,F) N).coordChange k i x (B a) = a := by
    change (tangentBundleCore 𝓘(ℝ,F) N).coordChange k i x
      ((tangentBundleCore 𝓘(ℝ,F) N).coordChange i k x a) = a
    rw [(tangentBundleCore 𝓘(ℝ,F) N).coordChange_comp i k i x ⟨⟨hi,hk⟩,hi⟩,
      (tangentBundleCore 𝓘(ℝ,F) N).coordChange_self i x hi]
  have h := hR.1 x (B (U v)) (B (U w))
  rw [R.tangent.tangentMetric_chart_eq i x hi,
    P.tangent.tangentMetric_chart_eq j (ι x) hj] at h
  change inner ℝ (R.tangent.frames.toFrame i x
    ((tangentBundleCore 𝓘(ℝ,F) N).coordChange k i x (B (U v))))
    (R.tangent.frames.toFrame i x
    ((tangentBundleCore 𝓘(ℝ,F) N).coordChange k i x (B (U w)))) = _ at h
  rw [hcancel, hcancel, R.tangent.frames.to_from i x hi,
    R.tangent.frames.to_from i x hi] at h
  exact h.symm

end
end QuaternionicSymmetry.ManifoldQuaternionicImmersionCharts
