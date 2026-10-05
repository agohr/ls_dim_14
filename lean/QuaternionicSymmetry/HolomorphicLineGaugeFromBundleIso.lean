import QuaternionicSymmetry.HolomorphicLineGauge
import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-! Relate holomorphic fiberwise linear maps of bundled total spaces to
all-overlap chartwise line gauges. -/

namespace QuaternionicSymmetry.HolomorphicLineGaugeFromBundleIso

open QuaternionicSymmetry.HolomorphicLineGauge
open QuaternionicSymmetry.HolomorphicLinePowers
open scoped Manifold ContDiff
noncomputable section

variable {B H F : Type*} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  {IB : ModelWithCorners ℂ F H} {ι κ : Type*}
  (Z : VectorBundleCore ℂ B ℂ ι) (W : VectorBundleCore ℂ B ℂ κ)
  [Z.IsContMDiff IB ∞] [W.IsContMDiff IB ∞]

/-- A holomorphic total-bundle isomorphism covering the identity,
as furnished by the registered complex-contact canonical formula. -/
structure TotalIso where
  fiberEquiv : ∀ x : B, Z.Fiber x ≃ₗ[ℂ] W.Fiber x
  holomorphicForward : ContMDiff (IB.prod 𝓘(ℂ,ℂ))
    (IB.prod 𝓘(ℂ,ℂ)) ∞
    (fun t : Bundle.TotalSpace ℂ Z.Fiber =>
      (⟨t.1, fiberEquiv t.1 t.2⟩ : Bundle.TotalSpace ℂ W.Fiber))
  holomorphicBackward : ContMDiff (IB.prod 𝓘(ℂ,ℂ))
    (IB.prod 𝓘(ℂ,ℂ)) ∞
    (fun t : Bundle.TotalSpace ℂ W.Fiber =>
      (⟨t.1, (fiberEquiv t.1).symm t.2⟩ : Bundle.TotalSpace ℂ Z.Fiber))

def TotalIso.symm (e : TotalIso (IB := IB) Z W) : TotalIso (IB := IB) W Z where
  fiberEquiv x := (e.fiberEquiv x).symm
  holomorphicForward := e.holomorphicBackward
  holomorphicBackward := e.holomorphicForward

/-- The source chart unit, viewed as an actual fiber element. -/
def chartUnit (i : ι) (x : B) : Z.Fiber x :=
  ((Z.localTriv i).toOpenPartialHomeomorph.symm (x, 1)).2

/-- The scalar of a total-bundle isomorphism in a source and target chart. -/
def localScalar (e : TotalIso (IB := IB) Z W) (i : ι) (a : κ) (x : B) : ℂ :=
  ((W.localTriv a) ⟨x, e.fiberEquiv x (chartUnit Z i x)⟩).2

private theorem chartUnit_change (i j : ι) (x : B)
    (hx : x ∈ Z.baseSet i ∩ Z.baseSet j) :
    chartUnit Z i x = transitionScalar Z i j x • chartUnit Z j x := by
  have h := Z.coordChange_comp i j (Z.indexAt x) x
    ⟨hx, Z.mem_baseSet_at x⟩ (1 : ℂ)
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
    transitionScalar W a b x * ((W.localTriv a) ⟨x, v⟩).2 =
      ((W.localTriv b) ⟨x, v⟩).2 := by
  have h := W.coordChange_comp (W.indexAt x) a b x
    ⟨⟨W.mem_baseSet_at x, hx.1⟩, hx.2⟩ v
  change transitionScalar W a b x * W.coordChange (W.indexAt x) a x v =
    W.coordChange (W.indexAt x) b x v
  calc
    transitionScalar W a b x * W.coordChange (W.indexAt x) a x v =
        W.coordChange a b x (W.coordChange (W.indexAt x) a x v) := by
      exact (linear_apply_one (W.coordChange a b x)
        (W.coordChange (W.indexAt x) a x v)).symm
    _ = W.coordChange (W.indexAt x) b x v := h

private theorem chartUnit_coordinate_self (i : ι) (x : B)
    (hx : x ∈ Z.baseSet i) :
    ((Z.localTriv i) ⟨x, chartUnit Z i x⟩).2 = 1 := by
  change Z.coordChange (Z.indexAt x) i x
    (Z.coordChange i (Z.indexAt x) x 1) = 1
  have h := Z.coordChange_comp i (Z.indexAt x) i x
    ⟨⟨hx, Z.mem_baseSet_at x⟩, hx⟩ (1 : ℂ)
  exact h.trans (Z.coordChange_self i x hx 1)

private theorem fiber_reconstruct (a : κ) (x : B) (v : W.Fiber x)
    (hx : x ∈ W.baseSet a) :
    v = ((W.localTriv a) ⟨x, v⟩).2 • chartUnit W a x := by
  have h := W.coordChange_comp (W.indexAt x) a (W.indexAt x) x
    ⟨⟨W.mem_baseSet_at x, hx⟩, W.mem_baseSet_at x⟩ v
  change v = W.coordChange (W.indexAt x) a x v •
    W.coordChange a (W.indexAt x) x 1
  calc
    v = W.coordChange (W.indexAt x) (W.indexAt x) x v :=
      (W.coordChange_self (W.indexAt x) x (W.mem_baseSet_at x) v).symm
    _ = W.coordChange a (W.indexAt x) x
          (W.coordChange (W.indexAt x) a x v) := h.symm
    _ = W.coordChange (W.indexAt x) a x v •
          W.coordChange a (W.indexAt x) x 1 := by
      rw [linear_apply_one]
      exact mul_comm _ _

private theorem localScalar_holomorphic (e : TotalIso (IB := IB) Z W)
    (i : ι) (a : κ) :
    ContMDiffOn IB 𝓘(ℂ,ℂ) ∞ (localScalar Z W e i a)
      (Z.baseSet i ∩ W.baseSet a) := by
  letI : MemTrivializationAtlas (Z.localTriv i) := ⟨⟨i, rfl⟩⟩
  letI : MemTrivializationAtlas (W.localTriv a) := ⟨⟨a, rfl⟩⟩
  let S := Z.baseSet i ∩ W.baseSet a
  have hpair : ContMDiffOn IB (IB.prod 𝓘(ℂ,ℂ)) ∞
      (fun x : B => (x, (1 : ℂ))) S :=
    contMDiffOn_id.prodMk contMDiffOn_const
  have hsource : ContMDiffOn IB (IB.prod 𝓘(ℂ,ℂ)) ∞
      (fun x : B => (Z.localTriv i).toOpenPartialHomeomorph.symm (x, (1 : ℂ))) S := by
    exact (Z.localTriv i).contMDiffOn_symm.comp hpair (by
      intro x hx
      exact (Z.mem_localTriv_target (i := i) (p := (x, (1 : ℂ)))).2 hx.1)
  have hforward : ContMDiffOn IB (IB.prod 𝓘(ℂ,ℂ)) ∞
      (fun x : B => (⟨x, e.fiberEquiv x (chartUnit Z i x)⟩ :
        Bundle.TotalSpace ℂ W.Fiber)) S := by
    exact e.holomorphicForward.comp_contMDiffOn hsource
  have htarget : ContMDiffOn IB (IB.prod 𝓘(ℂ,ℂ)) ∞
      (fun x : B => (W.localTriv a)
        (⟨x, e.fiberEquiv x (chartUnit Z i x)⟩ : Bundle.TotalSpace ℂ W.Fiber)) S := by
    exact (W.localTriv a).contMDiffOn.comp hforward (by
      intro x hx
      exact (W.mem_localTriv_source (i := a) (p :=
        (⟨x, e.fiberEquiv x (chartUnit Z i x)⟩ : Bundle.TotalSpace ℂ W.Fiber))).2 hx.2)
  exact contMDiff_snd.comp_contMDiffOn htarget

omit [Z.IsContMDiff IB ∞] [W.IsContMDiff IB ∞] in
private theorem localScalar_target_change (e : TotalIso (IB := IB) Z W)
    (i : ι) (a b : κ) (x : B)
    (hx : x ∈ W.baseSet a ∩ W.baseSet b) :
    transitionScalar W a b x * localScalar Z W e i a x =
      localScalar Z W e i b x := by
  exact coordinate_change W a b x (e.fiberEquiv x (chartUnit Z i x)) hx

omit [Z.IsContMDiff IB ∞] [W.IsContMDiff IB ∞] in
private theorem localScalar_source_change (e : TotalIso (IB := IB) Z W)
    (i j : ι) (a : κ) (x : B)
    (hx : x ∈ Z.baseSet i ∩ Z.baseSet j) :
    localScalar Z W e i a x =
      transitionScalar Z i j x * localScalar Z W e j a x := by
  change W.coordChange (W.indexAt x) a x (e.fiberEquiv x (chartUnit Z i x)) =
    transitionScalar Z i j x *
      W.coordChange (W.indexAt x) a x (e.fiberEquiv x (chartUnit Z j x))
  rw [chartUnit_change Z i j x hx, map_smul, map_smul]
  rfl

omit [Z.IsContMDiff IB ∞] [W.IsContMDiff IB ∞] in
private theorem localScalar_compat (e : TotalIso (IB := IB) Z W)
    (i j : ι) (a b : κ) (x : B)
    (hx : x ∈ Z.baseSet i ∩ Z.baseSet j ∩ W.baseSet a ∩ W.baseSet b) :
    transitionScalar W a b x * localScalar Z W e i a x =
      localScalar Z W e j b x * transitionScalar Z i j x := by
  rw [localScalar_target_change Z W e i a b x ⟨hx.1.2, hx.2⟩,
    localScalar_source_change Z W e i j b x ⟨hx.1.1.1, hx.1.1.2⟩]
  ring

omit [Z.IsContMDiff IB ∞] [W.IsContMDiff IB ∞] in
private theorem localScalar_inverse (e : TotalIso (IB := IB) Z W)
    (i : ι) (a : κ) (x : B)
    (hx : x ∈ Z.baseSet i ∩ W.baseSet a) :
    localScalar W Z e.symm a i x * localScalar Z W e i a x = 1 := by
  have hrec := fiber_reconstruct W a x
    (e.fiberEquiv x (chartUnit Z i x)) hx.2
  change e.fiberEquiv x (chartUnit Z i x) =
    localScalar Z W e i a x • chartUnit W a x at hrec
  have hu : chartUnit Z i x =
      localScalar Z W e i a x •
        (e.fiberEquiv x).symm (chartUnit W a x) := by
    calc
      chartUnit Z i x =
          (e.fiberEquiv x).symm (e.fiberEquiv x (chartUnit Z i x)) :=
        ((e.fiberEquiv x).symm_apply_apply _).symm
      _ = (e.fiberEquiv x).symm
          (localScalar Z W e i a x • chartUnit W a x) := by
        rw [hrec]
      _ = localScalar Z W e i a x •
          (e.fiberEquiv x).symm (chartUnit W a x) := by rw [map_smul]
  have hc := congrArg
    (fun v : Z.Fiber x => ((Z.localTriv i) ⟨x, v⟩).2) hu
  change ((Z.localTriv i) ⟨x, chartUnit Z i x⟩).2 =
    ((Z.localTriv i) ⟨x,
      localScalar Z W e i a x • (e.fiberEquiv x).symm (chartUnit W a x)⟩).2 at hc
  rw [chartUnit_coordinate_self Z i x hx.1] at hc
  change 1 = Z.coordChange (Z.indexAt x) i x
    (localScalar Z W e i a x • (e.fiberEquiv x).symm (chartUnit W a x)) at hc
  rw [map_smul] at hc
  change 1 = localScalar Z W e i a x *
    localScalar W Z e.symm a i x at hc
  simpa only [mul_comm] using hc.symm

/-- A holomorphic fiberwise linear isomorphism of actual total spaces
determines an all-overlap holomorphic gauge on any two core covers. -/
def TotalIso.toGaugeIso (e : TotalIso (IB := IB) Z W) :
    GaugeIso (IB := IB) Z W where
  forward := localScalar Z W e
  backward := localScalar W Z e.symm
  forward_holomorphic := localScalar_holomorphic Z W e
  backward_holomorphic := localScalar_holomorphic W Z e.symm
  forward_compat := localScalar_compat Z W e
  backward_compat := localScalar_compat W Z e.symm
  left_inverse := localScalar_inverse Z W e
  right_inverse a i x hx := by
    have h := localScalar_inverse Z W e i a x ⟨hx.2, hx.1⟩
    simpa only [mul_comm] using h

end
end QuaternionicSymmetry.HolomorphicLineGaugeFromBundleIso
