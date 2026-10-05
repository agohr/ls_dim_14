import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Analysis.Complex.Basic

/-! Joint continuity of a family of linear maps between genuine complex
line bundles can be tested on one nonzero local section. The base may move
with the parameter; no continuity of the finished total-space map is assumed.
-/

namespace QuaternionicSymmetry.ComplexLineFamilyContinuity

open Bundle Filter
open scoped Topology
noncomputable section

variable {G B C ι κ : Type*}
  [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace C]
  (Z : VectorBundleCore ℂ B ℂ ι) (W : VectorBundleCore ℂ C ℂ κ)
  (φ : G × B → C)
  (A : ∀ (g : G) (x : B), Z.Fiber x →ₗ[ℂ] W.Fiber (φ (g,x)))

/-- The actual map on line-bundle total spaces defined by a family of
fiberwise complex-linear maps. -/
def totalMap (p : G × Z.TotalSpace) : W.TotalSpace :=
  ⟨φ (p.1,p.2.1), A p.1 p.2.1 p.2.2⟩

/-- Local nonvanishing sections detect continuity of a parametrized linear
line-bundle map. The section need only be continuous at the base point,
and its image need only be jointly continuous at the parameter/base pair. -/
theorem continuous_totalMap_of_local_sections
    (hφ : Continuous φ)
    (hLocal : ∀ (g : G) (x : B),
      ∃ s : ∀ y : B, Z.Fiber y,
        ContinuousAt (fun y => (⟨y,s y⟩ : Z.TotalSpace)) x ∧
        s x ≠ 0 ∧
        ContinuousAt (fun q : G × B =>
          (⟨φ q, A q.1 q.2 (s q.2)⟩ : W.TotalSpace)) (g,x)) :
    Continuous (totalMap Z W φ A) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨s,hs,hs0,ht⟩ := hLocal p.1 p.2.1
  let i := Z.indexAt p.2.1
  let a := W.indexAt (φ (p.1,p.2.1))
  let e := Z.localTriv i
  let f := W.localTriv a
  have hi : p.2.1 ∈ e.baseSet := Z.mem_baseSet_at p.2.1
  have ha : φ (p.1,p.2.1) ∈ f.baseSet := W.mem_baseSet_at _
  let d : B → ℂ := fun x => (e ⟨x,s x⟩).2
  have heSection : ContinuousAt e (⟨p.2.1,s p.2.1⟩ : Z.TotalSpace) :=
    e.continuousAt (e.mem_source.mpr hi)
  have hd : ContinuousAt d p.2.1 :=
    (heSection.comp
      (f := fun y => (⟨y,s y⟩ : Z.TotalSpace)) hs).snd
  have hd0 : d p.2.1 ≠ 0 := by
    exact (e.linearEquivAt (R := ℂ) p.2.1 hi).map_ne_zero_iff.mpr hs0
  let base : G × Z.TotalSpace → G × B := fun q => (q.1,q.2.1)
  have hbase : Continuous base :=
    continuous_fst.prodMk ((Z.continuous_proj).comp continuous_snd)
  have htarget : ContinuousAt (fun q : G × Z.TotalSpace =>
      (f ⟨φ (base q), A q.1 q.2.1 (s q.2.1)⟩).2) p :=
    (((f.continuousAt (f.mem_source.mpr ha)).comp
      (f := fun q : G × B => (⟨φ q, A q.1 q.2 (s q.2)⟩ : W.TotalSpace))
      ht).snd).comp (f := base) hbase.continuousAt
  have hnum : ContinuousAt (fun q : G × Z.TotalSpace => (e q.2).2) p :=
    ((e.continuousAt (e.mem_source.mpr hi)).comp continuousAt_snd).snd
  have hden : ContinuousAt (fun q : G × Z.TotalSpace => d q.2.1) p :=
    hd.comp (f := fun q : G × Z.TotalSpace => q.2.1)
      ((Z.continuous_proj).comp continuous_snd).continuousAt
  have hcoord := (hnum.div hden hd0).mul htarget
  have hEq : (fun q : G × Z.TotalSpace =>
      (e q.2).2 / d q.2.1 *
        (f ⟨φ (base q), A q.1 q.2.1 (s q.2.1)⟩).2) =ᶠ[𝓝 p]
      (fun q => (f (totalMap Z W φ A q)).2) := by
    have hsource : ∀ᶠ q : G × Z.TotalSpace in 𝓝 p, q.2.1 ∈ e.baseSet :=
      ((Z.continuous_proj).comp continuous_snd).continuousAt.preimage_mem_nhds
        (e.open_baseSet.mem_nhds hi)
    have htargetBase : ∀ᶠ q : G × Z.TotalSpace in 𝓝 p,
        φ (base q) ∈ f.baseSet :=
      (hφ.comp hbase).continuousAt.preimage_mem_nhds (f.open_baseSet.mem_nhds ha)
    have hnonzero : ∀ᶠ q : G × Z.TotalSpace in 𝓝 p, d q.2.1 ≠ 0 :=
      (hden.ne_iff_eventually_ne continuousAt_const).mp hd0
    filter_upwards [hsource,htargetBase,hnonzero] with q hqi hqa hqd
    have hrec : q.2.2 = ((e q.2).2 / d q.2.1) • s q.2.1 := by
      apply (e.linearEquivAt (R := ℂ) q.2.1 hqi).injective
      rw [map_smul]
      change (e q.2).2 = ((e q.2).2 / d q.2.1) * d q.2.1
      exact (div_mul_cancel₀ _ hqd).symm
    change _ = (f ⟨φ (base q), A q.1 q.2.1 q.2.2⟩).2
    rw [hrec, map_smul]
    exact ((f.linearEquivAt (R := ℂ) (φ (base q)) hqa).map_smul
      ((e q.2).2 / d q.2.1) (A q.1 q.2.1 (s q.2.1))).symm
  apply (f.tendsto_nhds_iff (f.mem_source.mpr ha)).mpr
  exact ⟨(hφ.comp hbase).continuousAt,
    hcoord.congr_of_eventuallyEq hEq.symm⟩

end
end QuaternionicSymmetry.ComplexLineFamilyContinuity
