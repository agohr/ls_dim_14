import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Connected.Clopen

/-! Topological separation and compactness for actual locally trivial bundles.
These lemmas use the local trivializations, not extra total-space hypotheses. -/

namespace QuaternionicSymmetry.FiberBundleCompactHausdorff

open Bundle Filter Set Topology

variable {B F : Type*} [TopologicalSpace B] [TopologicalSpace F]
  (E : B → Type*) [∀ b, TopologicalSpace (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]

theorem totalSpace_t2 [T2Space B] [T2Space F] : T2Space (TotalSpace F E) := by
  apply t2Space_iff_disjoint_nhds.mpr
  intro x y hxy
  by_cases hb : x.proj = y.proj
  · let e := trivializationAt F E x.proj
    have hx : x ∈ e.source := FiberBundle.mem_trivializationAt_proj_source
    have hy : y ∈ e.source := e.mem_source.mpr (by
      rw [← hb]
      exact mem_baseSet_trivializationAt F E x.proj)
    have hne : e x ≠ e y := fun h => hxy
      (e.toOpenPartialHomeomorph.injOn hx hy h)
    exact (e.toOpenPartialHomeomorph.continuousAt hx).disjoint
      (disjoint_nhds_nhds.mpr hne) (e.toOpenPartialHomeomorph.continuousAt hy)
  · exact (FiberBundle.continuous_proj F E).continuousAt.disjoint
      (disjoint_nhds_nhds.mpr hb) (FiberBundle.continuous_proj F E).continuousAt

theorem totalSpace_compact [CompactSpace B] [CompactSpace F] :
    CompactSpace (TotalSpace F E) := by
  classical
  refine ⟨isCompact_iff_ultrafilter_le_nhds.mpr ?_⟩
  intro u _
  let b := (u.map (Bundle.TotalSpace.proj : TotalSpace F E → B)).lim
  have hb : Tendsto (Bundle.TotalSpace.proj : TotalSpace F E → B) u (𝓝 b) :=
    (u.map _).le_nhds_lim
  let e := trivializationAt F E b
  let a := (u.map (fun z => (e z).2)).lim
  have ha : Tendsto (fun z => (e z).2) u (𝓝 a) := (u.map _).le_nhds_lim
  have hs : ∀ᶠ z in (u : Filter (TotalSpace F E)), z ∈ e.source :=
    (hb.eventually (e.open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt F E b))).mono (fun _ h => e.mem_source.mpr h)
  have ht : (b, a) ∈ e.target := e.mem_target.mpr
    (mem_baseSet_trivializationAt F E b)
  refine ⟨e.toOpenPartialHomeomorph.symm (b, a), mem_univ _, ?_⟩
  have hc := (e.toOpenPartialHomeomorph.symm.continuousAt ht).tendsto.comp
    (hb.prodMk_nhds ha)
  have he : (fun z : TotalSpace F E =>
      e.toOpenPartialHomeomorph.symm (z.proj, (e z).2)) =ᶠ[u] id :=
    hs.mono (fun z hz => e.symm_apply_mk_proj hz)
  exact hc.congr' he

theorem totalSpace_preconnected [PreconnectedSpace B] [ConnectedSpace F] :
    PreconnectedSpace (TotalSpace F E) := by
  have hf : ∀ b : B, IsConnected
      ((Bundle.TotalSpace.proj : TotalSpace F E → B) ⁻¹' {b}) := by
    intro b
    let e := (trivializationAt F E b).preimageSingletonHomeomorph
      (mem_baseSet_trivializationAt F E b)
    letI := e.symm.surjective.connectedSpace e.symm.continuous
    exact isConnected_iff_connectedSpace.mpr inferInstance
  apply preconnectedSpace_iff_connectedComponent.mpr
  intro z
  rw [← (FiberBundle.isQuotientMap_proj F E).preimage_connectedComponent hf z,
    PreconnectedSpace.connectedComponent_eq_univ]
  rfl

end QuaternionicSymmetry.FiberBundleCompactHausdorff
