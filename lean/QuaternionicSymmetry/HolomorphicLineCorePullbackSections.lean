import QuaternionicSymmetry.HolomorphicLineCorePullback

/-! Restrict actual global holomorphic sections to a holomorphic pullback
line core. In particular, this is the restriction map for a holomorphic
inclusion of a complex submanifold. -/

namespace QuaternionicSymmetry.HolomorphicLineCorePullback

open scoped Manifold ContDiff
noncomputable section
universe u

variable {B B' H H' F F' : Type*}
  [TopologicalSpace B] [TopologicalSpace B'] [TopologicalSpace H]
  [TopologicalSpace H'] [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup F'] [NormedSpace ℂ F']
  [ChartedSpace H B] [ChartedSpace H' B']
  (IB : ModelWithCorners ℂ F H)
  (IB' : ModelWithCorners ℂ F' H')
  (L : HolomorphicLineCoreClasses.LineCore.{u} (B := B) IB)
  (f : B' → B) (hf : ContMDiff IB' IB ∞ f)

/-- An ambient holomorphic section remains holomorphic after restriction
to the actual pulled-back line bundle. -/
def restrictSection (s : GlobalSections IB L) :
    RestrictedGlobalSections IB IB' L f hf := by
  letI := L.holomorphic
  let L' := pullbackLineCore IB IB' L f hf
  letI := L'.holomorphic
  letI : ContMDiffVectorBundle ∞ ℂ L'.core.Fiber IB' :=
    VectorBundleCore.instContMDiffVectorBundle L'.core
  refine ⟨fun x => s (f x), ?_⟩
  intro y
  let e := trivializationAt ℂ L.core.Fiber (f y)
  let e' := trivializationAt ℂ L'.core.Fiber y
  have hy : f y ∈ e.baseSet := by
    change f y ∈ L.core.baseSet (L.core.indexAt (f y))
    exact L.core.mem_baseSet_at (f y)
  have hy' : y ∈ e'.baseSet := by
    change f y ∈ L.core.baseSet (L.core.indexAt (f y))
    exact L.core.mem_baseSet_at (f y)
  apply (e'.contMDiffAt_section_iff hy').2
  have hs : ContMDiffAt IB 𝓘(ℂ, ℂ) ∞
      (fun x => (e ⟨x, s x⟩).2) (f y) :=
    (e.contMDiffAt_section_iff hy).1 (s.contMDiff (f y))
  convert hs.comp y hf.contMDiffAt using 1

/-- Restriction of holomorphic sections is complex-linear, even when the
source and target manifolds have different complex dimensions. -/
def restrictionLinear : GlobalSections IB L →ₗ[ℂ]
    RestrictedGlobalSections IB IB' L f hf where
  toFun := restrictSection IB IB' L f hf
  map_add' s t := by
    ext x
    rfl
  map_smul' c s := by
    ext x
    rfl

/-- Actual global generation of a represented holomorphic line core.
The fiber is one-dimensional, so a nonzero section value spans it. -/
def GloballyGenerated
    (L : HolomorphicLineCoreClasses.LineCore.{u} (B := B) IB) : Prop :=
  ∀ x : B, ∃ s : GlobalSections IB L, s x ≠ 0

/-- Global generation descends along any holomorphic map, in particular a
holomorphic inclusion of a Wolf twistor into a larger complex twistor.
Only restrictions of ambient generating sections are used; no extension
theorem for all restricted sections is assumed. -/
theorem globallyGenerated_pullback (h : GloballyGenerated IB L) :
    GloballyGenerated IB' (pullbackLineCore IB IB' L f hf) := by
  intro x
  obtain ⟨s, hs⟩ := h (f x)
  exact ⟨restrictSection IB IB' L f hf s, hs⟩

end
end QuaternionicSymmetry.HolomorphicLineCorePullback
