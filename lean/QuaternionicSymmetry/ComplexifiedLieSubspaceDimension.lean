import QuaternionicSymmetry.ComplexifiedLieCentralizerComponents
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.RingTheory.TensorProduct.Finite

/-! The literal complex span of a real Lie subspace has the expected
dimension. It is identified with actual scalar extension by the canonical
inclusion, rather than by a chosen dimension or a Lie-group source. -/

namespace QuaternionicSymmetry.ComplexifiedLieSubspaceDimension

open ComplexifiedLieCentralizerComponents
open scoped TensorProduct
noncomputable section

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

theorem complexSpan_eq_baseChange (T : Submodule ℝ L) :
    complexSpan T = T.baseChange ℂ := by
  rw [Submodule.baseChange_eq_span]
  unfold complexSpan
  congr 1
  ext z
  change (∃ t : T, (1 : ℂ) ⊗ₜ[ℝ] (t : L) = z) ↔
    ∃ t : L, t ∈ T ∧ (TensorProduct.mk ℝ ℂ L 1) t = z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, t.property, rfl⟩
  · rintro ⟨t, ht, hz⟩
    exact ⟨⟨t, ht⟩, hz⟩

theorem subtype_baseChange_injective (T : Submodule ℝ L) :
    Function.Injective (T.subtype.baseChange ℂ) := by
  obtain ⟨p, hp⟩ := T.subtype.exists_leftInverse_of_injective T.ker_subtype
  have hLeft : (p.baseChange ℂ).comp (T.subtype.baseChange ℂ) =
      LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hp, LinearMap.baseChange_id]
  have hInv : Function.LeftInverse (p.baseChange ℂ) (T.subtype.baseChange ℂ) := by
    intro z
    exact congrArg (fun f : (ℂ ⊗[ℝ] T) →ₗ[ℂ] (ℂ ⊗[ℝ] T) => f z) hLeft
  exact hInv.injective

def complexSpanEquiv (T : Submodule ℝ L) :
    (ℂ ⊗[ℝ] T) ≃ₗ[ℂ] complexSpan T :=
  (LinearEquiv.ofInjective (T.subtype.baseChange ℂ)
    (subtype_baseChange_injective T)).trans
      (LinearEquiv.ofEq _ _ (complexSpan_eq_baseChange T).symm)

theorem complexSpanEquiv_tmul (T : Submodule ℝ L) (c : ℂ) (t : T) :
    (complexSpanEquiv T (c ⊗ₜ[ℝ] t) : ℂ ⊗[ℝ] L) =
      c ⊗ₜ[ℝ] (t : L) := rfl

theorem finrank_complexSpan (T : Submodule ℝ L) :
    Module.finrank ℂ (complexSpan T) = Module.finrank ℝ T := by
  rw [← (complexSpanEquiv T).finrank_eq, Module.finrank_baseChange]

theorem complexSpan_finiteDimensional (T : Submodule ℝ L)
    [FiniteDimensional ℝ T] : FiniteDimensional ℂ (complexSpan T) := by
  exact Module.Finite.of_surjective (complexSpanEquiv T).toLinearMap
    (complexSpanEquiv T).surjective

theorem finrank_real_complexSpan (T : Submodule ℝ L) :
    Module.finrank ℝ (complexSpan T) = 2 * Module.finrank ℝ T := by
  rw [finrank_real_of_complex, finrank_complexSpan]

end
end QuaternionicSymmetry.ComplexifiedLieSubspaceDimension
