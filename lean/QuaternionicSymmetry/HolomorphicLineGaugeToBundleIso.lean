import QuaternionicSymmetry.HolomorphicLineGaugeFromBundleIso
import QuaternionicSymmetry.HolomorphicLineCoreClassGroup

/-! All-overlap holomorphic line gauges give genuine holomorphic
fiberwise-linear isomorphisms of the total bundles. Together with the
reverse construction, equality of represented line classes is exactly
existence of such an actual bundle isomorphism. -/

namespace QuaternionicSymmetry.HolomorphicLineGaugeToBundleIso

open HolomorphicLineGauge HolomorphicLineGaugeFromBundleIso
open HolomorphicLinePowers HolomorphicLineCoreClasses
open scoped Manifold ContDiff Topology
noncomputable section

variable {B H F : Type*} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  {IB : ModelWithCorners ℂ F H} {ι κ : Type*}
  {Z : VectorBundleCore ℂ B ℂ ι} {W : VectorBundleCore ℂ B ℂ κ}
  [Z.IsContMDiff IB ∞] [W.IsContMDiff IB ∞]

/-- The pointwise gauge gives an actual linear equivalence in the
preferred fiber coordinates; its inverse uses the backward gauge. -/
def gaugeFiberEquiv (e : GaugeIso (IB := IB) Z W) (x : B) :
    Z.Fiber x ≃ₗ[ℂ] W.Fiber x where
  toFun v := e.forward (Z.indexAt x) (W.indexAt x) x * (show ℂ from v)
  invFun v := e.backward (W.indexAt x) (Z.indexAt x) x * (show ℂ from v)
  left_inv v := by
    change _ * (_ * (show ℂ from v)) = (show ℂ from v)
    rw [← mul_assoc, e.left_inverse _ _ x
      ⟨Z.mem_baseSet_at x, W.mem_baseSet_at x⟩, one_mul]
  right_inv v := by
    change _ * (_ * (show ℂ from v)) = (show ℂ from v)
    rw [← mul_assoc, e.right_inverse _ _ x
      ⟨W.mem_baseSet_at x, Z.mem_baseSet_at x⟩, one_mul]
  map_add' v w := by
    change e.forward (Z.indexAt x) (W.indexAt x) x *
        ((show ℂ from v) + (show ℂ from w)) =
      e.forward (Z.indexAt x) (W.indexAt x) x * (show ℂ from v) +
        e.forward (Z.indexAt x) (W.indexAt x) x * (show ℂ from w)
    exact mul_add _ _ _
  map_smul' c v := by
    change _ * (c * (show ℂ from v)) = c * (_ * (show ℂ from v))
    ring

theorem gaugeFiberEquiv_coordinates (e : GaugeIso (IB := IB) Z W)
    (i : ι) (a : κ) (x : B) (v : Z.Fiber x)
    (hx : x ∈ Z.baseSet i ∩ W.baseSet a) :
    ((W.localTriv a) ⟨x, gaugeFiberEquiv e x v⟩).2 =
      e.forward i a x * ((Z.localTriv i) ⟨x, v⟩).2 := by
  change W.coordChange (W.indexAt x) a x
      (e.forward (Z.indexAt x) (W.indexAt x) x * (show ℂ from v)) =
    e.forward i a x * Z.coordChange (Z.indexAt x) i x v
  rw [linear_apply_one (W.coordChange (W.indexAt x) a x),
    linear_apply_one (Z.coordChange (Z.indexAt x) i x)]
  have hc := e.forward_compat (Z.indexAt x) i (W.indexAt x) a x
    ⟨⟨⟨Z.mem_baseSet_at x, hx.1⟩, W.mem_baseSet_at x⟩, hx.2⟩
  change transitionScalar W (W.indexAt x) a x *
      (e.forward (Z.indexAt x) (W.indexAt x) x * (show ℂ from v)) =
    e.forward i a x * (transitionScalar Z (Z.indexAt x) i x * (show ℂ from v))
  rw [← mul_assoc, hc, mul_assoc]

theorem gaugeTotalMap_holomorphic (e : GaugeIso (IB := IB) Z W) :
    ContMDiff (IB.prod 𝓘(ℂ,ℂ)) (IB.prod 𝓘(ℂ,ℂ)) ∞
      (fun t : Bundle.TotalSpace ℂ Z.Fiber =>
        (⟨t.1, gaugeFiberEquiv e t.1 t.2⟩ : Bundle.TotalSpace ℂ W.Fiber)) := by
  intro t
  let i := Z.indexAt t.1
  let a := W.indexAt t.1
  have hi : t.1 ∈ Z.baseSet i := Z.mem_baseSet_at t.1
  have ha : t.1 ∈ W.baseSet a := W.mem_baseSet_at t.1
  letI : MemTrivializationAtlas (Z.localTriv i) := ⟨⟨i, rfl⟩⟩
  letI : MemTrivializationAtlas (W.localTriv a) := ⟨⟨a, rfl⟩⟩
  have hp : ContMDiffAt (IB.prod 𝓘(ℂ,ℂ)) IB ∞
      (fun p : Bundle.TotalSpace ℂ Z.Fiber => p.1) t :=
    Bundle.contMDiffAt_proj Z.Fiber
  apply ((W.localTriv a).contMDiffAt_iff
    ((W.mem_localTriv_source a _).2 ha)).2
  refine ⟨hp, ?_⟩
  have hs : ContMDiffAt (IB.prod 𝓘(ℂ,ℂ)) 𝓘(ℂ,ℂ) ∞
      (fun p : Bundle.TotalSpace ℂ Z.Fiber => ((Z.localTriv i) p).2) t :=
    (((Z.localTriv i).contMDiffAt_iff
      ((Z.mem_localTriv_source i t).2 hi)).1 contMDiffAt_id).2
  have he : ContMDiffAt IB 𝓘(ℂ,ℂ) ∞ (e.forward i a) t.1 :=
    (e.forward_holomorphic i a t.1 ⟨hi, ha⟩).contMDiffAt
      (((Z.isOpen_baseSet i).inter (W.isOpen_baseSet a)).mem_nhds ⟨hi, ha⟩)
  apply ((he.comp t hp).mul hs).congr_of_eventuallyEq
  have hi' := hp.continuousAt.preimage_mem_nhds ((Z.isOpen_baseSet i).mem_nhds hi)
  have ha' := hp.continuousAt.preimage_mem_nhds ((W.isOpen_baseSet a).mem_nhds ha)
  filter_upwards [hi', ha'] with p hpi hpa
  exact gaugeFiberEquiv_coordinates e i a p.1 p.2 ⟨hpi, hpa⟩

/-- A chartwise gauge is realized on the actual holomorphic total spaces. -/
def toTotalIso (e : GaugeIso (IB := IB) Z W) : TotalIso (IB := IB) Z W where
  fiberEquiv := gaugeFiberEquiv e
  holomorphicForward := gaugeTotalMap_holomorphic e
  holomorphicBackward := gaugeTotalMap_holomorphic e.symm

theorem nonempty_gauge_iff_totalIso :
    Nonempty (GaugeIso (IB := IB) Z W) ↔ Nonempty (TotalIso (IB := IB) Z W) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨toTotalIso e⟩
  · rintro ⟨e⟩
    exact ⟨e.toGaugeIso⟩

universe u
theorem class_eq_iff_totalIso (L M : LineCore.{u} (B := B) IB) :
    (Quotient.mk _ L : CoreClass IB) = Quotient.mk _ M ↔
      letI := L.holomorphic
      letI := M.holomorphic
      Nonempty (TotalIso (IB := IB) L.core M.core) := by
  letI := L.holomorphic
  letI := M.holomorphic
  rw [HolomorphicLineCoreClassGroup.class_eq_iff_isomorphic]
  exact nonempty_gauge_iff_totalIso

end
end QuaternionicSymmetry.HolomorphicLineGaugeToBundleIso
