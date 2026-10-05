import QuaternionicSymmetry.HolomorphicLinePowerSections

/-! Scalar ratios of actual sections of a holomorphic line and its tensor
powers on the open locus where the denominator section is nonzero. -/

namespace QuaternionicSymmetry.HolomorphicLineSectionRatios

open QuaternionicSymmetry.HolomorphicLineCoreClasses
open QuaternionicSymmetry.HolomorphicLineCorePullback
open QuaternionicSymmetry.HolomorphicLineTensorPowerClasses
open QuaternionicSymmetry.HolomorphicLinePowers
open scoped Manifold ContDiff Topology
noncomputable section
universe u

variable {B H F : Type*} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H) [IsManifold IB ∞ B]
  (L : LineCore.{u} (B := B) IB)

def nonzeroSet (s : GlobalSections IB L) : Set B :=
  {x | s x ≠ 0}

omit [IsManifold IB ∞ B] in
theorem isOpen_nonzeroSet (s : GlobalSections IB L) :
    IsOpen (nonzeroSet IB L s) := by
  letI := L.holomorphic
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  have hc : ContinuousAt (fun y : B =>
      L.core.coordChange (L.core.indexAt y) (L.core.indexAt x) y (s y)) x := by
    have h := ((Bundle.contMDiffAt_section x).mp (s.contMDiff x)).continuousAt
    simpa only [VectorBundleCore.trivializationAt, VectorBundleCore.localTrivAt,
      VectorBundleCore.localTriv_apply] using h
  have hcx : L.core.coordChange (L.core.indexAt x) (L.core.indexAt x) x
      (s x) ≠ 0 := by
    rw [L.core.coordChange_self _ _ (L.core.mem_baseSet_at x)]
    exact hx
  have hne := (hc.ne_iff_eventually_ne continuousAt_const).mp hcx
  filter_upwards [hne] with y hy
  change s y ≠ 0
  intro hz
  apply hy
  rw [hz, map_zero]

/-- The ratio of a section of `L^k` by the `k`th power of a nonzero
section of `L`, expressed in the common scalar fiber of the two cores. -/
def sectionRatio (k : ℕ) (s : GlobalSections IB L)
    (t : GlobalSections IB (powerCoreRep IB L k)) (x : B) : ℂ :=
  (show ℂ from t x) / ((show ℂ from s x) ^ k)

omit [IsManifold IB ∞ B] in
private theorem transitionScalar_ne_zero (i j : L.Index) (x : B)
    (hx : x ∈ L.core.baseSet i ∩ L.core.baseSet j) :
    transitionScalar L.core i j x ≠ 0 := by
  intro hzero
  have hcomp := L.core.coordChange_comp i j i x
    ⟨⟨hx.1, hx.2⟩, hx.1⟩ (1 : ℂ)
  rw [L.core.coordChange_self i x hx.1] at hcomp
  have hmap : L.core.coordChange i j x (1 : ℂ) = 0 := hzero
  rw [hmap, map_zero] at hcomp
  exact zero_ne_one hcomp

omit [IsManifold IB ∞ B] in
/-- On the actual nonzero locus, tensor-power section ratios are
holomorphic scalar functions. The local scalar transition factors cancel. -/
theorem sectionRatio_contMDiffOn (k : ℕ) (s : GlobalSections IB L)
    (t : GlobalSections IB (powerCoreRep IB L k)) :
    ContMDiffOn IB 𝓘(ℂ,ℂ) ∞ (sectionRatio IB L k s t)
      (nonzeroSet IB L s) := by
  letI := L.holomorphic
  let P := powerCoreRep IB L k
  letI := P.holomorphic
  letI : ContMDiffVectorBundle ∞ ℂ P.core.Fiber IB :=
    VectorBundleCore.instContMDiffVectorBundle P.core
  intro x hx
  let e := trivializationAt ℂ L.core.Fiber x
  let eP := trivializationAt ℂ P.core.Fiber x
  have he : x ∈ e.baseSet := L.core.mem_baseSet_at x
  have heP : x ∈ eP.baseSet := P.core.mem_baseSet_at x
  have hs : ContMDiffAt IB 𝓘(ℂ,ℂ) ∞
      (fun y => (e ⟨y, s y⟩).2) x :=
    (e.contMDiffAt_section_iff he).1 (s.contMDiff x)
  have ht : ContMDiffAt IB 𝓘(ℂ,ℂ) ∞
      (fun y => (eP ⟨y, t y⟩).2) x :=
    (eP.contMDiffAt_section_iff heP).1 (t.contMDiff x)
  have hden : (e ⟨x, s x⟩).2 ≠ 0 := by
    change L.core.coordChange (L.core.indexAt x) (L.core.indexAt x) x (s x) ≠ 0
    rw [L.core.coordChange_self _ _ (L.core.mem_baseSet_at x)]
    exact hx
  have hratio : ContMDiffAt IB 𝓘(ℂ,ℂ) ∞
      (fun y => (eP ⟨y, t y⟩).2 / ((e ⟨y, s y⟩).2)^k) x :=
    ht.div₀ (hs.pow k) (pow_ne_zero k hden)
  have hEq : (fun y => (eP ⟨y, t y⟩).2 / ((e ⟨y, s y⟩).2)^k) =ᶠ[𝓝 x]
      sectionRatio IB L k s t := by
    filter_upwards [(L.core.isOpen_baseSet (L.core.indexAt x)).mem_nhds
      (L.core.mem_baseSet_at x)] with y hy
    have ha : transitionScalar L.core (L.core.indexAt y) (L.core.indexAt x) y ≠ 0 :=
      transitionScalar_ne_zero IB L _ _ y ⟨L.core.mem_baseSet_at y, hy⟩
    change (transitionScalar L.core (L.core.indexAt y) (L.core.indexAt x) y)^k *
        (show ℂ from t y) /
        ((L.core.coordChange (L.core.indexAt y) (L.core.indexAt x) y) (s y))^k =
      (show ℂ from t y) / ((show ℂ from s y)^k)
    have hcoord :
        (L.core.coordChange (L.core.indexAt y) (L.core.indexAt x) y) (s y) =
          transitionScalar L.core (L.core.indexAt y) (L.core.indexAt x) y *
            (show ℂ from s y) :=
      linear_apply_one _ _
    rw [hcoord]
    rw [mul_pow]
    field_simp [ha]
  exact (hratio.congr_of_eventuallyEq hEq.symm).contMDiffWithinAt


end
end QuaternionicSymmetry.HolomorphicLineSectionRatios
