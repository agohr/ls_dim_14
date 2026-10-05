import QuaternionicSymmetry.ComplexLineFamilyContinuity
import QuaternionicSymmetry.HolomorphicLineGaugeToBundleIso

/-! A jointly holomorphic family of linear maps of complex lines is
holomorphic on total spaces when one nonzero local section detects it.
The base map may move with the parameter. -/

namespace QuaternionicSymmetry.HolomorphicLineFamilyJointHolomorphic

open Bundle Filter
open scoped Manifold ContDiff Topology
noncomputable section

variable {G B C P H K F V W ι κ : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace P] [TopologicalSpace H] [TopologicalSpace K]
  [TopologicalSpace G] [ChartedSpace P G]
  [TopologicalSpace B] [ChartedSpace H B]
  [TopologicalSpace C] [ChartedSpace K C]
  (IG : ModelWithCorners ℂ F P)
  (IB : ModelWithCorners ℂ V H)
  (IC : ModelWithCorners ℂ W K)
  (Z : VectorBundleCore ℂ B ℂ ι) (T : VectorBundleCore ℂ C ℂ κ)
  [Z.IsContMDiff IB ∞] [T.IsContMDiff IC ∞]
  (φ : G × B → C)
  (A : ∀ (g : G) (x : B), Z.Fiber x →ₗ[ℂ] T.Fiber (φ (g,x)))

private theorem fiber_reconstruct (i : ι) (x : B) (v : Z.Fiber x)
    (s : ∀ y : B, Z.Fiber y) (hx : x ∈ Z.baseSet i)
    (hd : ((Z.localTriv i) ⟨x,s x⟩).2 ≠ 0) :
    v = (((Z.localTriv i) ⟨x,v⟩).2 /
      ((Z.localTriv i) ⟨x,s x⟩).2) • s x := by
  apply (Z.localTriv i).linearEquivAt (R := ℂ) x hx |>.injective
  rw [map_smul]
  change ((Z.localTriv i) ⟨x,v⟩).2 =
    (((Z.localTriv i) ⟨x,v⟩).2 /
      ((Z.localTriv i) ⟨x,s x⟩).2) *
      ((Z.localTriv i) ⟨x,s x⟩).2
  exact (div_mul_cancel₀ _ hd).symm

theorem contMDiff_totalMap_of_local_sections
    (hφ : ContMDiff (IG.prod IB) IC ∞ φ)
    (hLocal : ∀ (g : G) (x : B),
      ∃ U : Set B, IsOpen U ∧ x ∈ U ∧
      ∃ s : ∀ y : B, Z.Fiber y,
        s x ≠ 0 ∧
        ContMDiffOn IB (IB.prod 𝓘(ℂ,ℂ)) ∞
          (fun y => (⟨y,s y⟩ : Z.TotalSpace)) U ∧
        ContMDiffOn (IG.prod IB) (IC.prod 𝓘(ℂ,ℂ)) ∞
          (fun q : G × B =>
            (⟨φ q,A q.1 q.2 (s q.2)⟩ : T.TotalSpace))
          (Set.univ ×ˢ U)) :
    ContMDiff (IG.prod (IB.prod 𝓘(ℂ,ℂ)))
      (IC.prod 𝓘(ℂ,ℂ)) ∞
      (ComplexLineFamilyContinuity.totalMap Z T φ A) := by
  intro p
  obtain ⟨U,hU,hx,s,hs0,hs,ht⟩ := hLocal p.1 p.2.1
  let i := Z.indexAt p.2.1
  let a := T.indexAt (φ (p.1,p.2.1))
  have hi : p.2.1 ∈ Z.baseSet i := Z.mem_baseSet_at _
  have ha : φ (p.1,p.2.1) ∈ T.baseSet a := T.mem_baseSet_at _
  letI : MemTrivializationAtlas (Z.localTriv i) := ⟨⟨i,rfl⟩⟩
  letI : MemTrivializationAtlas (T.localTriv a) := ⟨⟨a,rfl⟩⟩
  let base : G × Z.TotalSpace → G × B := fun q => (q.1,q.2.1)
  have hbase : ContMDiff (IG.prod (IB.prod 𝓘(ℂ,ℂ)))
      (IG.prod IB) ∞ base :=
    contMDiff_fst.prodMk (Bundle.contMDiff_proj Z.Fiber |>.comp contMDiff_snd)
  have hφbase : ContMDiffAt (IG.prod (IB.prod 𝓘(ℂ,ℂ))) IC ∞
      (fun q => φ (base q)) p := (hφ.comp hbase).contMDiffAt
  apply ((T.localTriv a).contMDiffAt_iff
    (f := ComplexLineFamilyContinuity.totalMap Z T φ A) (x₀ := p)
    (IM := IG.prod (IB.prod 𝓘(ℂ,ℂ))) (IB := IC)
    ((T.mem_localTriv_source a _).2 ha)).2
  refine ⟨hφbase,?_⟩
  let d : B → ℂ := fun x => ((Z.localTriv i) ⟨x,s x⟩).2
  have hds : ContMDiffAt IB 𝓘(ℂ,ℂ) ∞ d p.2.1 :=
    ((Z.localTriv i).contMDiffAt_section_iff (s := s) hi).1
      ((hs p.2.1 hx).contMDiffAt (hU.mem_nhds hx))
  have hd0 : d p.2.1 ≠ 0 := by
    intro hz
    have hzero : s p.2.1 = 0 :=
      ((Z.localTriv i).linearEquivAt (R := ℂ) p.2.1 hi).map_eq_zero_iff.mp hz
    exact hs0 hzero
  have hnum : ContMDiffAt (IG.prod (IB.prod 𝓘(ℂ,ℂ)))
      𝓘(ℂ,ℂ) ∞ (fun q : G × Z.TotalSpace => ((Z.localTriv i) q.2).2) p := by
    have hcoord : ContMDiffAt (IB.prod 𝓘(ℂ,ℂ)) 𝓘(ℂ,ℂ) ∞
        (fun v : Z.TotalSpace => ((Z.localTriv i) v).2) p.2 :=
      (((Z.localTriv i).contMDiffAt_iff (f := id) (x₀ := p.2)
        (IM := IB.prod 𝓘(ℂ,ℂ)) (IB := IB)
        ((Z.mem_localTriv_source i p.2).2 hi)).1 contMDiffAt_id).2
    exact hcoord.comp p contMDiff_snd.contMDiffAt
  have hden : ContMDiffAt (IG.prod (IB.prod 𝓘(ℂ,ℂ)))
      𝓘(ℂ,ℂ) ∞ (fun q : G × Z.TotalSpace => d q.2.1) p := by
    have hp : ContMDiffAt (IG.prod (IB.prod 𝓘(ℂ,ℂ))) IB ∞
        (fun q : G × Z.TotalSpace => q.2.1) p :=
      (Bundle.contMDiff_proj Z.Fiber |>.comp contMDiff_snd).contMDiffAt
    exact hds.comp (f := fun q : G × Z.TotalSpace => q.2.1) p hp
  have htarget : ContMDiffAt (IG.prod (IB.prod 𝓘(ℂ,ℂ)))
      𝓘(ℂ,ℂ) ∞
      (fun q : G × Z.TotalSpace =>
        ((T.localTriv a) ⟨φ (base q),A q.1 q.2.1 (s q.2.1)⟩).2) p := by
    have hsection : ContMDiffAt (IG.prod IB) (IC.prod 𝓘(ℂ,ℂ)) ∞
        (fun q : G × B => (⟨φ q,A q.1 q.2 (s q.2)⟩ : T.TotalSpace))
        (p.1,p.2.1) :=
      (ht (p.1,p.2.1) ⟨Set.mem_univ _,hx⟩).contMDiffAt
        ((isOpen_univ.prod hU).mem_nhds ⟨Set.mem_univ _,hx⟩)
    have hcoord : ContMDiffAt (IG.prod IB) 𝓘(ℂ,ℂ) ∞
        (fun q : G × B =>
          ((T.localTriv a) ⟨φ q,A q.1 q.2 (s q.2)⟩).2)
        (p.1,p.2.1) :=
      (((T.localTriv a).contMDiffAt_iff
        (f := fun q : G × B => (⟨φ q,A q.1 q.2 (s q.2)⟩ : T.TotalSpace))
        (x₀ := (p.1,p.2.1)) (IM := IG.prod IB) (IB := IC)
        ((T.mem_localTriv_source a _).2 ha)).1 hsection).2
    exact hcoord.comp (f := base) p hbase.contMDiffAt
  have hratio := (hnum.div₀ hden hd0).mul htarget
  apply hratio.congr_of_eventuallyEq
  have hsource : ∀ᶠ q : G × Z.TotalSpace in 𝓝 p,
      q.2.1 ∈ Z.baseSet i :=
    hbase.continuous.snd.continuousAt.preimage_mem_nhds
      ((Z.isOpen_baseSet i).mem_nhds hi)
  have hnonzero : ∀ᶠ q : G × Z.TotalSpace in 𝓝 p,
      d q.2.1 ≠ 0 :=
    (hden.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hd0
  have htargetBase : ∀ᶠ q : G × Z.TotalSpace in 𝓝 p,
      φ (base q) ∈ T.baseSet a :=
    hφbase.continuousAt.preimage_mem_nhds ((T.isOpen_baseSet a).mem_nhds ha)
  filter_upwards [hsource,hnonzero,htargetBase] with q hqi hqd hqa
  have hrec := fiber_reconstruct Z i q.2.1 q.2.2 s hqi hqd
  change ((T.localTriv a) ⟨φ (base q),A q.1 q.2.1 q.2.2⟩).2 =
    ((Z.localTriv i) q.2).2 / d q.2.1 *
      ((T.localTriv a) ⟨φ (base q),A q.1 q.2.1 (s q.2.1)⟩).2
  let e := (T.localTriv a).linearEquivAt (R := ℂ) (φ (base q)) hqa
  calc
    _ = e (A q.1 q.2.1
        ((((Z.localTriv i) q.2).2 / d q.2.1) • s q.2.1)) :=
      congrArg (fun w => e (A q.1 q.2.1 w)) hrec
    _ = _ := by rw [map_smul, map_smul]; rfl

end
end QuaternionicSymmetry.HolomorphicLineFamilyJointHolomorphic
