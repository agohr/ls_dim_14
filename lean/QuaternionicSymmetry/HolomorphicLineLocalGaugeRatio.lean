import QuaternionicSymmetry.HolomorphicLineGaugeFromBundleIso

/-! The local scalar of a fiberwise linear map of holomorphic lines is a
ratio of holomorphic section coordinates whenever the map carries a
nonvanishing local holomorphic section to another holomorphic section. -/
namespace QuaternionicSymmetry.HolomorphicLineLocalGaugeRatio
open QuaternionicSymmetry.HolomorphicLineGaugeFromBundleIso
open QuaternionicSymmetry.HolomorphicLinePowers
open scoped Manifold ContDiff Topology
noncomputable section

variable {B H F : Type*} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H) {ι κ : Type*}
  (Z : VectorBundleCore ℂ B ℂ ι) (W : VectorBundleCore ℂ B ℂ κ)
  [Z.IsContMDiff IB ∞] [W.IsContMDiff IB ∞]
  (e : ∀ x : B, Z.Fiber x ≃ₗ[ℂ] W.Fiber x)

/-- The gauge scalar in a chosen source and target local trivialization. -/
def localScalar (i : ι) (a : κ) (x : B) : ℂ :=
  ((W.localTriv a) ⟨x,e x (chartUnit Z i x)⟩).2

private theorem chartUnit_coordinate_self (i : ι) (x : B)
    (hx : x ∈ Z.baseSet i) :
    ((Z.localTriv i) ⟨x,chartUnit Z i x⟩).2 = 1 := by
  change Z.coordChange (Z.indexAt x) i x
    (Z.coordChange i (Z.indexAt x) x 1) = 1
  have h := Z.coordChange_comp i (Z.indexAt x) i x
    ⟨⟨hx,Z.mem_baseSet_at x⟩,hx⟩ (1 : ℂ)
  exact h.trans (Z.coordChange_self i x hx 1)

private theorem fiber_reconstruct (i : ι) (x : B) (v : Z.Fiber x)
    (hx : x ∈ Z.baseSet i) :
    v = ((Z.localTriv i) ⟨x,v⟩).2 • chartUnit Z i x := by
  let T := (Z.localTriv i).linearEquivAt (R := ℂ) x hx
  apply T.injective
  rw [T.map_smul]
  change T v = ((Z.localTriv i) ⟨x,v⟩).2 • T (chartUnit Z i x)
  change ((Z.localTriv i) ⟨x,v⟩).2 =
    ((Z.localTriv i) ⟨x,v⟩).2 *
      ((Z.localTriv i) ⟨x,chartUnit Z i x⟩).2
  rw [chartUnit_coordinate_self Z i x hx, mul_one]

private theorem localScalar_eq_ratio
    (i : ι) (a : κ) (x : B)
    (s : ∀ y : B, Z.Fiber y) (t : ∀ y : B, W.Fiber y)
    (hi : x ∈ Z.baseSet i) (ha : x ∈ W.baseSet a)
    (hmap : e x (s x) = t x)
    (hd : ((Z.localTriv i) ⟨x,s x⟩).2 ≠ 0) :
    localScalar Z W e i a x =
      ((W.localTriv a) ⟨x,t x⟩).2 /
        ((Z.localTriv i) ⟨x,s x⟩).2 := by
  let d := ((Z.localTriv i) ⟨x,s x⟩).2
  let c := localScalar Z W e i a x
  have hs := fiber_reconstruct Z i x (s x) hi
  have ht : ((W.localTriv a) ⟨x,t x⟩).2 = d * c := by
    rw [← hmap, hs, map_smul]
    change ((W.localTriv a) ⟨x,d • e x (chartUnit Z i x)⟩).2 =
      d * ((W.localTriv a) ⟨x,e x (chartUnit Z i x)⟩).2
    exact ((W.localTriv a).linearEquivAt (R := ℂ) x ha).map_smul
      d (e x (chartUnit Z i x))
  rw [ht]
  exact (mul_div_cancel_left₀ c hd).symm

/-- The scalar of a fiberwise linear map is holomorphic at a point if it
carries one local holomorphic source section, nonzero at that point, to a
local holomorphic target section. The proof computes the scalar as a ratio
of actual chart coordinates. -/
theorem localScalar_contMDiffAt_of_local_sections
    (i : ι) (a : κ) (x : B)
    (hi : x ∈ Z.baseSet i) (ha : x ∈ W.baseSet a)
    (U : Set B) (hU : IsOpen U) (hx : x ∈ U)
    (s : ∀ y : B, Z.Fiber y) (t : ∀ y : B, W.Fiber y)
    (hs : ContMDiffOn IB (IB.prod 𝓘(ℂ,ℂ)) ∞
      (fun y => (⟨y,s y⟩ : Bundle.TotalSpace ℂ Z.Fiber)) U)
    (ht : ContMDiffOn IB (IB.prod 𝓘(ℂ,ℂ)) ∞
      (fun y => (⟨y,t y⟩ : Bundle.TotalSpace ℂ W.Fiber)) U)
    (hmap : ∀ y ∈ U, e y (s y) = t y)
    (hsx : s x ≠ 0) :
    ContMDiffAt IB 𝓘(ℂ,ℂ) ∞ (localScalar Z W e i a) x := by
  letI : MemTrivializationAtlas (Z.localTriv i) := ⟨⟨i,rfl⟩⟩
  letI : MemTrivializationAtlas (W.localTriv a) := ⟨⟨a,rfl⟩⟩
  let d : B → ℂ := fun y => ((Z.localTriv i) ⟨y,s y⟩).2
  let q : B → ℂ := fun y => ((W.localTriv a) ⟨y,t y⟩).2
  have hs' : ContMDiffAt IB 𝓘(ℂ,ℂ) ∞ d x :=
    ((Z.localTriv i).contMDiffAt_section_iff hi).1
      ((hs x hx).contMDiffAt (hU.mem_nhds hx))
  have ht' : ContMDiffAt IB 𝓘(ℂ,ℂ) ∞ q x :=
    ((W.localTriv a).contMDiffAt_section_iff ha).1
      ((ht x hx).contMDiffAt (hU.mem_nhds hx))
  have hd : d x ≠ 0 := by
    intro hz
    have hv := fiber_reconstruct Z i x (s x) hi
    change s x = d x • chartUnit Z i x at hv
    rw [hz, zero_smul] at hv
    exact hsx hv
  have hratio : ContMDiffAt IB 𝓘(ℂ,ℂ) ∞ (fun y => q y / d y) x :=
    ht'.div₀ hs' hd
  have hne : ∀ᶠ y in 𝓝 x, d y ≠ 0 :=
    (hs'.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hd
  have hEq : (fun y => q y / d y) =ᶠ[𝓝 x]
      localScalar Z W e i a := by
    filter_upwards [hU.mem_nhds hx,
      (Z.isOpen_baseSet i).mem_nhds hi,
      (W.isOpen_baseSet a).mem_nhds ha, hne] with y hyU hyi hya hyd
    exact (localScalar_eq_ratio Z W e i a y s t hyi hya (hmap y hyU) hyd).symm
  exact hratio.congr_of_eventuallyEq hEq.symm

/-- The purely local holomorphic-section criterion for a fiberwise line
equivalence. This contains no target-specific contact or gauge conclusion. -/
def HasLocalHolomorphicWitness : Prop :=
  ∀ x : B, ∃ U : Set B, IsOpen U ∧ x ∈ U ∧
    ∃ s : ∀ y : B, Z.Fiber y,
    ∃ t : ∀ y : B, W.Fiber y,
      ContMDiffOn IB (IB.prod 𝓘(ℂ,ℂ)) ∞
        (fun y => (⟨y,s y⟩ : Bundle.TotalSpace ℂ Z.Fiber)) U ∧
      ContMDiffOn IB (IB.prod 𝓘(ℂ,ℂ)) ∞
        (fun y => (⟨y,t y⟩ : Bundle.TotalSpace ℂ W.Fiber)) U ∧
      s x ≠ 0 ∧ ∀ y ∈ U, e y (s y) = t y

theorem hasLocalHolomorphicWitness_symm
    (h : HasLocalHolomorphicWitness IB Z W e) :
    HasLocalHolomorphicWitness IB W Z (fun x => (e x).symm) := by
  intro x
  obtain ⟨U,hU,hx,s,t,hs,ht,hsx,hmap⟩ := h x
  refine ⟨U,hU,hx,t,s,ht,hs,?_,?_⟩
  · intro hz
    apply hsx
    apply (e x).injective
    rw [hmap x hx,hz,map_zero]
  · intro y hy
    rw [← hmap y hy]
    exact (e y).symm_apply_apply _

theorem localScalar_contMDiffOn_of_witness
    (h : HasLocalHolomorphicWitness IB Z W e)
    (i : ι) (a : κ) :
    ContMDiffOn IB 𝓘(ℂ,ℂ) ∞ (localScalar Z W e i a)
      (Z.baseSet i ∩ W.baseSet a) := by
  intro x hx
  obtain ⟨U,hU,hxU,s,t,hs,ht,hsx,hmap⟩ := h x
  exact (localScalar_contMDiffAt_of_local_sections IB Z W e i a x
    hx.1 hx.2 U hU hxU s t hs ht hmap hsx).contMDiffWithinAt

private theorem chartUnit_change (i j : ι) (x : B)
    (hx : x ∈ Z.baseSet i ∩ Z.baseSet j) :
    chartUnit Z i x = transitionScalar Z i j x • chartUnit Z j x := by
  have h := Z.coordChange_comp i j (Z.indexAt x) x
    ⟨hx,Z.mem_baseSet_at x⟩ (1 : ℂ)
  change Z.coordChange i (Z.indexAt x) x 1 =
    transitionScalar Z i j x • Z.coordChange j (Z.indexAt x) x 1
  calc
    Z.coordChange i (Z.indexAt x) x 1 =
        Z.coordChange j (Z.indexAt x) x (Z.coordChange i j x 1) := h.symm
    _ = transitionScalar Z i j x • Z.coordChange j (Z.indexAt x) x 1 := by
      rw [linear_apply_one]
      exact mul_comm _ _

private theorem coordinate_change (a b : κ) (x : B) (v : W.Fiber x)
    (hx : x ∈ W.baseSet a ∩ W.baseSet b) :
    transitionScalar W a b x * ((W.localTriv a) ⟨x,v⟩).2 =
      ((W.localTriv b) ⟨x,v⟩).2 := by
  have h := W.coordChange_comp (W.indexAt x) a b x
    ⟨⟨W.mem_baseSet_at x,hx.1⟩,hx.2⟩ v
  change transitionScalar W a b x * W.coordChange (W.indexAt x) a x v =
    W.coordChange (W.indexAt x) b x v
  calc
    transitionScalar W a b x * W.coordChange (W.indexAt x) a x v =
        W.coordChange a b x (W.coordChange (W.indexAt x) a x v) := by
      exact (linear_apply_one (W.coordChange a b x)
        (W.coordChange (W.indexAt x) a x v)).symm
    _ = W.coordChange (W.indexAt x) b x v := h

private theorem localScalar_target_change
    (i : ι) (a b : κ) (x : B)
    (hx : x ∈ W.baseSet a ∩ W.baseSet b) :
    transitionScalar W a b x * localScalar Z W e i a x =
      localScalar Z W e i b x :=
  coordinate_change W a b x (e x (chartUnit Z i x)) hx

private theorem localScalar_source_change
    (i j : ι) (a : κ) (x : B)
    (hx : x ∈ Z.baseSet i ∩ Z.baseSet j) :
    localScalar Z W e i a x =
      transitionScalar Z i j x * localScalar Z W e j a x := by
  change W.coordChange (W.indexAt x) a x (e x (chartUnit Z i x)) =
    transitionScalar Z i j x *
      W.coordChange (W.indexAt x) a x (e x (chartUnit Z j x))
  rw [chartUnit_change Z i j x hx,map_smul,map_smul]
  rfl

private theorem localScalar_compat
    (i j : ι) (a b : κ) (x : B)
    (hx : x ∈ Z.baseSet i ∩ Z.baseSet j ∩ W.baseSet a ∩ W.baseSet b) :
    transitionScalar W a b x * localScalar Z W e i a x =
      localScalar Z W e j b x * transitionScalar Z i j x := by
  rw [localScalar_target_change Z W e i a b x ⟨hx.1.2,hx.2⟩,
    localScalar_source_change Z W e i j b x ⟨hx.1.1.1,hx.1.1.2⟩]
  ring

private theorem localScalar_inverse
    (i : ι) (a : κ) (x : B)
    (hx : x ∈ Z.baseSet i ∩ W.baseSet a) :
    localScalar W Z (fun y => (e y).symm) a i x *
      localScalar Z W e i a x = 1 := by
  have hrec := fiber_reconstruct W a x (e x (chartUnit Z i x)) hx.2
  change e x (chartUnit Z i x) =
    localScalar Z W e i a x • chartUnit W a x at hrec
  have hu : chartUnit Z i x =
      localScalar Z W e i a x • (e x).symm (chartUnit W a x) := by
    calc
      chartUnit Z i x = (e x).symm (e x (chartUnit Z i x)) :=
        ((e x).symm_apply_apply _).symm
      _ = (e x).symm (localScalar Z W e i a x • chartUnit W a x) := by
        rw [hrec]
      _ = localScalar Z W e i a x • (e x).symm (chartUnit W a x) := by
        rw [map_smul]
  have hc := congrArg
    (fun v : Z.Fiber x => ((Z.localTriv i) ⟨x,v⟩).2) hu
  change ((Z.localTriv i) ⟨x,chartUnit Z i x⟩).2 =
    ((Z.localTriv i) ⟨x,
      localScalar Z W e i a x • (e x).symm (chartUnit W a x)⟩).2 at hc
  rw [chartUnit_coordinate_self Z i x hx.1] at hc
  change 1 = Z.coordChange (Z.indexAt x) i x
    (localScalar Z W e i a x • (e x).symm (chartUnit W a x)) at hc
  rw [map_smul] at hc
  change 1 = localScalar Z W e i a x *
    localScalar W Z (fun y => (e y).symm) a i x at hc
  simpa only [mul_comm] using hc.symm

/-- A fiberwise line equivalence carrying a nonzero local holomorphic
section to a holomorphic section at every point yields an all-overlap
holomorphic gauge. Both inverse holomorphicity and transition compatibility
are proved internally. -/
def gaugeIsoOfLocalWitness
    (h : HasLocalHolomorphicWitness IB Z W e) :
    HolomorphicLineGauge.GaugeIso (IB := IB) Z W where
  forward := localScalar Z W e
  backward := localScalar W Z (fun x => (e x).symm)
  forward_holomorphic := localScalar_contMDiffOn_of_witness IB Z W e h
  backward_holomorphic :=
    localScalar_contMDiffOn_of_witness IB W Z (fun x => (e x).symm)
      (hasLocalHolomorphicWitness_symm IB Z W e h)
  forward_compat := localScalar_compat Z W e
  backward_compat := localScalar_compat W Z (fun x => (e x).symm)
  left_inverse := localScalar_inverse Z W e
  right_inverse a i x hx := by
    have h := localScalar_inverse Z W e i a x ⟨hx.2,hx.1⟩
    simpa only [mul_comm] using h

end
end QuaternionicSymmetry.HolomorphicLineLocalGaugeRatio
