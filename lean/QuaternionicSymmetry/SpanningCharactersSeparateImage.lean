import QuaternionicSymmetry.ToralBracketEigenbasis
import Mathlib.LinearAlgebra.Dual.Basis

/-! Pure linear-algebra boundary for later weight-span arguments. Full span
of genuine complex-linear character functionals separates the parameter
space, and this separation descends along any surjective image map whose
characters agree on the image. The geometric full-span assertion is NOT
provided here. -/

namespace QuaternionicSymmetry.SpanningCharactersSeparateImage

open Module
noncomputable section

variable {ι U L : Type*} [AddCommGroup U] [Module ℂ U]
  [FiniteDimensional ℂ U] [AddCommGroup L] [Module ℂ L]

theorem separates_of_dual_span_top
    (β : ι → (U →ₗ[ℂ] ℂ))
    (hSpan : Submodule.span ℂ (Set.range β) = ⊤)
    (u : U) (hu : ∀ i, β i u = 0) : u = 0 := by
  classical
  have hAll (f : U →ₗ[ℂ] ℂ) : f u = 0 := by
    have hf : f ∈ Submodule.span ℂ (Set.range β) := by rw [hSpan]; trivial
    induction hf using Submodule.span_induction with
    | mem f hf =>
        obtain ⟨i, rfl⟩ := hf
        exact hu i
    | zero => simp
    | add f g hf hg ihf ihg => simp [ihf, ihg]
    | smul a f hf ihf => simp [ihf]
  apply (Module.Free.chooseBasis ℂ U).eval_injective
  apply LinearMap.ext
  intro f
  simpa [Dual.eval_apply] using hAll f

/-- No injectivity of `f` is required: separation of a parameter space
descends to the actual image if each image character pulls back to β. -/
theorem separates_image_of_dual_span_top
    (β : ι → (U →ₗ[ℂ] ℂ))
    (hSpan : Submodule.span ℂ (Set.range β) = ⊤)
    (f : U →ₗ[ℂ] L) (χ : ι → L → ℂ)
    (hCompat : ∀ i u, χ i (f u) = β i u)
    (x : L) (hx : x ∈ LinearMap.range f)
    (hZero : ∀ i, χ i x = 0) : x = 0 := by
  obtain ⟨u, rfl⟩ := hx
  have hu : u = 0 := separates_of_dual_span_top β hSpan u (by
    intro i
    rw [← hCompat]
    exact hZero i)
  rw [hu, map_zero]

end
end QuaternionicSymmetry.SpanningCharactersSeparateImage
