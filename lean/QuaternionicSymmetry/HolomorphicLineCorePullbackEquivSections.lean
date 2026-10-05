import QuaternionicSymmetry.HolomorphicLineCorePullbackSections

/-! Pullback along a biholomorphism is a complex-linear equivalence on
global holomorphic sections of a represented line core. -/

namespace QuaternionicSymmetry.HolomorphicLineCorePullbackEquivSections

open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open scoped Manifold ContDiff
noncomputable section

variable {B H F : Type*} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)
  (L : LineCore.{0} (B := B) IB)
  (f : B ≃ B)
  (hf : ContMDiff IB IB ∞ f)
  (hfinv : ContMDiff IB IB ∞ f.symm)

private def inverseValue
    (s : GlobalSections IB (pullbackLineCore IB IB L f hf))
    (x : B) : L.core.Fiber x := by
  have h : (pullbackLineCore IB IB L f hf).core.Fiber (f.symm x) =
      L.core.Fiber x := by
    change L.core.Fiber (f (f.symm x)) = L.core.Fiber x
    exact congrArg L.core.Fiber (f.apply_symm_apply x)
  exact h ▸ s (f.symm x)

include hfinv in
private theorem inverseValue_contMDiffAt
    (s : GlobalSections IB (pullbackLineCore IB IB L f hf)) (x : B) :
    letI := L.holomorphic
    ContMDiffAt IB (IB.prod 𝓘(ℂ,ℂ)) ∞
      (fun y => (⟨y, inverseValue IB L f hf s y⟩ :
        Bundle.TotalSpace ℂ L.core.Fiber)) x := by
  letI := L.holomorphic
  let P := pullbackLineCore IB IB L f hf
  letI := P.holomorphic
  let i := L.core.indexAt x
  let e := L.core.localTriv i
  let e' := P.core.localTriv i
  have hx : x ∈ L.core.baseSet i := L.core.mem_baseSet_at x
  have hx' : f.symm x ∈ P.core.baseSet i := by
    change f (f.symm x) ∈ L.core.baseSet i
    rw [f.apply_symm_apply]
    exact hx
  letI : MemTrivializationAtlas e := ⟨⟨i,rfl⟩⟩
  letI : MemTrivializationAtlas e' := ⟨⟨i,rfl⟩⟩
  have hs : ContMDiffAt IB 𝓘(ℂ,ℂ) ∞
      (fun y => (e' ⟨y,s y⟩).2) (f.symm x) :=
    (e'.contMDiffAt_section_iff hx').1 (s.contMDiff (f.symm x))
  have hcomp : ContMDiffAt IB 𝓘(ℂ,ℂ) ∞
      (fun y => (e' ⟨f.symm y,s (f.symm y)⟩).2) x :=
    hs.comp x hfinv.contMDiffAt
  apply (e.contMDiffAt_section_iff hx).2
  have hcoord :
      (fun y => (e ⟨y,inverseValue IB L f hf s y⟩).2) =
      (fun y => (e' ⟨f.symm y,s (f.symm y)⟩).2) := by
    funext y
    simp [inverseValue, e, e', P, pullbackLineCore, pullbackCore,
      f.apply_symm_apply]
  rw [hcoord]
  exact hcomp

/-- Pullback of global holomorphic sections along a biholomorphism. -/
def sectionLinearEquiv : GlobalSections IB L ≃ₗ[ℂ]
    GlobalSections IB (pullbackLineCore IB IB L f hf) := by
  letI := L.holomorphic
  letI := (pullbackLineCore IB IB L f hf).holomorphic
  let forward := restrictionLinear IB IB L f hf
  let backward : GlobalSections IB (pullbackLineCore IB IB L f hf) →
      GlobalSections IB L := fun s =>
    ⟨inverseValue IB L f hf s,
      inverseValue_contMDiffAt IB L f hf hfinv s⟩
  exact {
    toFun := forward
    invFun := backward
    left_inv := by
      intro s
      apply ContMDiffSection.ext
      intro x
      change inverseValue IB L f hf
        (restrictionLinear IB IB L f hf s) x = s x
      simp [inverseValue, restrictionLinear, restrictSection]
      rw [f.apply_symm_apply]
    right_inv := by
      intro s
      apply ContMDiffSection.ext
      intro x
      change inverseValue IB L f hf s (f x) = s x
      simp [inverseValue]
      rw [f.symm_apply_apply]
    map_add' := by intro s t; exact map_add forward s t
    map_smul' := by intro c s; exact map_smul forward c s }

theorem sectionLinearEquiv_symm_apply_at_image
    (s : GlobalSections IB (pullbackLineCore IB IB L f hf)) (x : B) :
    ((sectionLinearEquiv IB L f hf hfinv).symm s) (f x) = s x := by
  change inverseValue IB L f hf s (f x) = s x
  simp [inverseValue]
  rw [f.symm_apply_apply]

end
end QuaternionicSymmetry.HolomorphicLineCorePullbackEquivSections
