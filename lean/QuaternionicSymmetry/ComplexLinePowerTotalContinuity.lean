import QuaternionicSymmetry.ComplexLineFamilyContinuity
import QuaternionicSymmetry.HolomorphicLinePowers

/-! A genuine map of line-bundle total spaces induces continuous maps on
all scalar-cocycle tensor powers. The proof uses local power-bundle charts;
the preferred scalar is never assumed globally continuous. -/
namespace QuaternionicSymmetry.ComplexLinePowerTotalContinuity

open ComplexLineFamilyContinuity HolomorphicLinePowers Bundle
noncomputable section

variable {B ι : Type*} [TopologicalSpace B]
  (Z : VectorBundleCore ℂ B ℂ ι) (k : ℕ)

def totalSpacePower : Z.TotalSpace → (powerCore Z k).TotalSpace :=
  fun p => ⟨p.1, (show ℂ from p.2) ^ k⟩

private theorem power_localTriv_coordinate (i : ι) (p : Z.TotalSpace) :
    (((powerCore Z k).localTriv i) (totalSpacePower Z k p)).2 =
      ((Z.localTriv i) p).2 ^ k := by
  change (transitionScalar Z (Z.indexAt p.1) i p.1 ^ k) *
    ((show ℂ from p.2) ^ k) =
    (Z.coordChange (Z.indexAt p.1) i p.1 p.2) ^ k
  rw [linear_apply_one, mul_pow]
  rfl

theorem continuous_totalSpacePower : Continuous (totalSpacePower Z k) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let i := Z.indexAt p.1
  have hi : p.1 ∈ Z.baseSet i := Z.mem_baseSet_at p.1
  have hs : ContinuousAt (fun q : Z.TotalSpace => (Z.localTriv i q).2) p :=
    ((Z.localTriv i).continuousAt ((Z.localTriv i).mem_source.mpr hi)).snd
  have hb : ContinuousAt (fun q : Z.TotalSpace => q.1) p :=
    Z.continuous_proj.continuousAt
  have ht : totalSpacePower Z k p ∈ ((powerCore Z k).localTriv i).source :=
    ((powerCore Z k).localTriv i).mem_source.mpr hi
  apply (((powerCore Z k).localTriv i).tendsto_nhds_iff
    ht).mpr
  refine ⟨hb, ?_⟩
  have heq : (fun q : Z.TotalSpace =>
      (((powerCore Z k).localTriv i) (totalSpacePower Z k q)).2) =
      (fun q => ((Z.localTriv i) q).2 ^ k) := by
    funext q
    exact power_localTriv_coordinate Z k i q
  simpa only [heq, power_localTriv_coordinate] using hs.pow k

variable {G : Type*} [TopologicalSpace G]
  (φ : G × B → B)
  (A : ∀ (g : G) (x : B), Z.Fiber x →ₗ[ℂ] Z.Fiber (φ (g,x)))

def powerFiberMap (g : G) (x : B) :
    (powerCore Z k).Fiber x →ₗ[ℂ] (powerCore Z k).Fiber (φ (g,x)) :=
  ((show ℂ from A g x (1 : ℂ)) ^ k) • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)

def powerTotalMap (p : G × (powerCore Z k).TotalSpace) :
    (powerCore Z k).TotalSpace :=
  totalMap (powerCore Z k) (powerCore Z k) φ (powerFiberMap Z k φ A) p

private def chartUnit (i : ι) (x : B) : Z.Fiber x :=
  ((Z.localTriv i).toOpenPartialHomeomorph.symm (x, 1)).2

private theorem chartUnit_power (i : ι) (x : B) :
    chartUnit (powerCore Z k) i x = (show ℂ from chartUnit Z i x) ^ k := by
  change (transitionScalar Z i (Z.indexAt x) x ^ k) * 1 =
    (Z.coordChange i (Z.indexAt x) x 1) ^ k
  simp only [mul_one]
  rfl

private theorem chartUnit_continuousAt (i : ι) (x : B)
    (hx : x ∈ Z.baseSet i) :
    ContinuousAt (fun y : B => (⟨y,chartUnit Z i y⟩ : Z.TotalSpace)) x := by
  have ht : (x, (1 : ℂ)) ∈ (Z.localTriv i).target :=
    (Z.mem_localTriv_target (i := i) (p := (x, (1 : ℂ)))).2 hx
  change ContinuousAt (fun y : B =>
    (Z.localTriv i).toOpenPartialHomeomorph.symm (y, (1 : ℂ))) x
  have hsymm : ContinuousAt
      ((Z.localTriv i).toOpenPartialHomeomorph.symm : B × ℂ → Z.TotalSpace)
      (x, (1 : ℂ)) :=
    (Z.localTriv i).toOpenPartialHomeomorph.continuousAt_symm ht
  exact hsymm.comp₂ continuousAt_id continuousAt_const

private theorem chartUnit_ne_zero (i : ι) (x : B)
    (hx : x ∈ Z.baseSet i) : chartUnit Z i x ≠ 0 := by
  have hcoord : ((Z.localTriv i) ⟨x,chartUnit Z i x⟩).2 = 1 := by
    change Z.coordChange (Z.indexAt x) i x
      (Z.coordChange i (Z.indexAt x) x 1) = 1
    have h := Z.coordChange_comp i (Z.indexAt x) i x
      ⟨⟨hx, Z.mem_baseSet_at x⟩, hx⟩ (1 : ℂ)
    exact h.trans (Z.coordChange_self i x hx 1)
  intro hzero
  rw [hzero] at hcoord
  simp at hcoord

theorem continuous_powerTotalMap_of_lineTotalMap
    (hφ : Continuous φ)
    (hA : Continuous (totalMap Z Z φ A)) :
    Continuous (powerTotalMap Z k φ A) := by
  change Continuous (totalMap (powerCore Z k) (powerCore Z k) φ
    (powerFiberMap Z k φ A))
  apply continuous_totalMap_of_local_sections (hφ := hφ)
  intro g x
  let i := Z.indexAt x
  let sL : ∀ y : B, Z.Fiber y := chartUnit Z i
  let sP : ∀ y : B, (powerCore Z k).Fiber y := chartUnit (powerCore Z k) i
  refine ⟨sP, ?_, ?_, ?_⟩
  · exact chartUnit_continuousAt (powerCore Z k) i x (Z.mem_baseSet_at x)
  · exact chartUnit_ne_zero (powerCore Z k) i x (Z.mem_baseSet_at x)
  · have hsL : ContinuousAt (fun y : B => (⟨y,sL y⟩ : Z.TotalSpace)) x :=
      chartUnit_continuousAt Z i x (Z.mem_baseSet_at x)
    have hsLpair : ContinuousAt (fun q : G × B =>
        (⟨q.2,sL q.2⟩ : Z.TotalSpace)) (g,x) := by
      have hpr : ContinuousAt (Prod.snd : G × B → B) (g,x) := continuousAt_snd
      simpa only [Function.comp_def] using
        hsL.comp hpr
    have hpair : ContinuousAt (fun q : G × B =>
        (q.1, (⟨q.2,sL q.2⟩ : Z.TotalSpace))) (g,x) :=
      continuousAt_fst.prodMk hsLpair
    have hc : ContinuousAt (fun q : G × B =>
        totalSpacePower Z k (totalMap Z Z φ A
          (q.1, (⟨q.2,sL q.2⟩ : Z.TotalSpace)))) (g,x) :=
      (continuous_totalSpacePower Z k).continuousAt.comp (hA.continuousAt.comp hpair)
    have heq : (fun q : G × B =>
        (⟨φ q, powerFiberMap Z k φ A q.1 q.2 (sP q.2)⟩ :
          (powerCore Z k).TotalSpace)) =
        (fun q => totalSpacePower Z k (totalMap Z Z φ A
          (q.1, (⟨q.2,sL q.2⟩ : Z.TotalSpace)))) := by
      funext q
      apply Bundle.TotalSpace.ext
      · rfl
      · apply heq_of_eq
        have hs : (show ℂ from sP q.2) = (show ℂ from sL q.2) ^ k :=
          chartUnit_power Z k i q.2
        have hlin : (show ℂ from A q.1 q.2 (sL q.2)) =
            (show ℂ from A q.1 q.2 (1 : ℂ)) * (show ℂ from sL q.2) := by
          have h := (A q.1 q.2).map_smul (show ℂ from sL q.2) (1 : ℂ)
          simp only [smul_eq_mul, mul_one] at h
          simpa only [mul_comm] using h
        change (show ℂ from A q.1 q.2 (1 : ℂ)) ^ k * (show ℂ from sP q.2) =
          (show ℂ from A q.1 q.2 (sL q.2)) ^ k
        rw [hs, hlin, mul_pow]
    rw [heq]
    exact hc

end
end QuaternionicSymmetry.ComplexLinePowerTotalContinuity
