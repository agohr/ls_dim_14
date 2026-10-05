import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Analysis.Complex.Basic

/-! A local holomorphic vector-bundle section with any prescribed constant
trivialization coordinate. This elementary construction is used to descend
holomorphic contact forms through their rank-one quotients. -/
namespace QuaternionicSymmetry.HolomorphicBundleLocalVector
open Bundle
open scoped Manifold ContDiff
noncomputable section

variable {H M F : Type*}
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  (I : ModelWithCorners ℂ F H)
  {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V]
  [VectorBundle ℂ F V]
  [ContMDiffVectorBundle ∞ F V I]
  (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
  [MemTrivializationAtlas e]

/-- The local section whose coordinate is the chosen model-fiber vector.
Outside the trivialization domain its zero value is only junk data. -/
def localVector (w : F) (x : M) : V x := by
  classical
  exact if hx : x ∈ e.baseSet then (e.linearEquivAt (R := ℂ) x hx).symm w else 0

theorem localVector_apply_of_mem (w : F) {x : M} (hx : x ∈ e.baseSet) :
    localVector e w x = (e.linearEquivAt (R := ℂ) x hx).symm w := by
  simp [localVector, hx]

/-- The local constant-coordinate section is holomorphic on its natural
domain. No global extension is asserted. -/
theorem localVector_contMDiffOn (w : F) :
    ContMDiffOn I (I.prod 𝓘(ℂ,F)) ∞
      (fun x : M => (⟨x, localVector e w x⟩ : TotalSpace F V))
      e.baseSet := by
  rw [e.contMDiffOn_section_baseSet_iff]
  apply (contMDiffOn_const (c := w)).congr
  intro x hx
  simp [localVector, hx]

/-- Every fiber vector extends to a holomorphic section on the chart
domain, with no claim of global holomorphic extension. -/
theorem exists_local_section_through (x : M) (hx : x ∈ e.baseSet)
    (v : V x) :
    ∃ s : ∀ y : M, V y,
      ContMDiffOn I (I.prod 𝓘(ℂ,F)) ∞
        (fun y : M => (⟨y, s y⟩ : TotalSpace F V)) e.baseSet ∧
      s x = v := by
  let w := (e.linearEquivAt (R := ℂ) x hx) v
  refine ⟨localVector e w, localVector_contMDiffOn I e w, ?_⟩
  rw [localVector_apply_of_mem e w hx]
  exact (e.linearEquivAt (R := ℂ) x hx).symm_apply_apply v

end
end QuaternionicSymmetry.HolomorphicBundleLocalVector
