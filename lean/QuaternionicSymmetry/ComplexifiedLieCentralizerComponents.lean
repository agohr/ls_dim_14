import QuaternionicSymmetry.ComplexTensorRealImagComponents
import Mathlib.Algebra.Lie.BaseChange

/-! Literal bracket decomposition in `ℂ ⊗[ℝ] L`. This is the algebraic
part of maximal-compact-torus centralizer transfer, independent of any
choice of automorphism-group atlas. -/

namespace QuaternionicSymmetry.ComplexifiedLieCentralizerComponents

open scoped TensorProduct
open ComplexTensorRealImagComponents
noncomputable section

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

theorem bracket_one_tmul (z : ℂ ⊗[ℝ] L) (t : L) :
    ⁅z, (1 : ℂ) ⊗ₜ[ℝ] t⁆ =
      ((1 : ℂ) ⊗ₜ[ℝ] ⁅realComponent z, t⁆) +
      (Complex.I ⊗ₜ[ℝ] ⁅imagComponent z, t⁆) := by
  conv_lhs => rw [eq_one_tmul_add_I_tmul z]
  rw [add_lie]
  simp only [LieAlgebra.ExtendScalars.bracket_tmul, mul_one]

theorem real_bracket_of_zero (z : ℂ ⊗[ℝ] L) (t : L)
    (hz : ⁅z, (1 : ℂ) ⊗ₜ[ℝ] t⁆ = 0) :
    ⁅realComponent z, t⁆ = 0 := by
  rw [bracket_one_tmul] at hz
  have h := congrArg realComponent hz
  simpa only [map_add, realComponent_tmul, map_zero, Complex.one_re,
    Complex.I_re, one_smul, zero_smul, add_zero] using h

theorem imag_bracket_of_zero (z : ℂ ⊗[ℝ] L) (t : L)
    (hz : ⁅z, (1 : ℂ) ⊗ₜ[ℝ] t⁆ = 0) :
    ⁅imagComponent z, t⁆ = 0 := by
  rw [bracket_one_tmul] at hz
  have h := congrArg imagComponent hz
  simpa only [map_add, imagComponent_tmul, map_zero, Complex.one_im,
    Complex.I_im, zero_smul, one_smul, zero_add] using h

/-- The literal complex span of a real Lie subspace, using the canonical
pure-tensor inclusion. -/
def complexSpan (T : Submodule ℝ L) : Submodule ℂ (ℂ ⊗[ℝ] L) :=
  Submodule.span ℂ (Set.range (fun t : T => (1 : ℂ) ⊗ₜ[ℝ] (t : L)))

theorem one_tmul_mem_complexSpan (T : Submodule ℝ L) {t : L} (ht : t ∈ T) :
    ((1 : ℂ) ⊗ₜ[ℝ] t) ∈ complexSpan T := by
  apply Submodule.subset_span
  exact ⟨⟨t, ht⟩, rfl⟩

theorem I_tmul_mem_complexSpan (T : Submodule ℝ L) {t : L} (ht : t ∈ T) :
    (Complex.I ⊗ₜ[ℝ] t) ∈ complexSpan T := by
  have h := (complexSpan T).smul_mem Complex.I (one_tmul_mem_complexSpan T ht)
  convert h using 1
  simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- If a real Lie subspace is its own centralizer, a complexified vector
centralizing its pure tensors belongs to its literal complex span. This
does not integrate a torus or identify any two Lie-group atlases. -/
theorem mem_complexSpan_of_centralizes
    (T : Submodule ℝ L)
    (hself : ∀ x : L, (∀ t ∈ T, ⁅x,t⁆ = 0) → x ∈ T)
    (z : ℂ ⊗[ℝ] L)
    (hz : ∀ t ∈ T, ⁅z, (1 : ℂ) ⊗ₜ[ℝ] t⁆ = 0) :
    z ∈ complexSpan T := by
  have hr : realComponent z ∈ T :=
    hself _ (fun t ht => real_bracket_of_zero z t (hz t ht))
  have hi : imagComponent z ∈ T :=
    hself _ (fun t ht => imag_bracket_of_zero z t (hz t ht))
  rw [eq_one_tmul_add_I_tmul z]
  exact (complexSpan T).add_mem
    (one_tmul_mem_complexSpan T hr)
    (I_tmul_mem_complexSpan T hi)

theorem complexSpan_centralizes_of_abelian
    (T : Submodule ℝ L)
    (habel : ∀ x ∈ T, ∀ y ∈ T, ⁅x,y⁆ = 0)
    {z : ℂ ⊗[ℝ] L} (hz : z ∈ complexSpan T)
    (t : L) (ht : t ∈ T) :
    ⁅z, (1 : ℂ) ⊗ₜ[ℝ] t⁆ = 0 := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨u, rfl⟩ := hx
      simp only [LieAlgebra.ExtendScalars.bracket_tmul, mul_one]
      rw [habel u.1 u.2 t ht, TensorProduct.tmul_zero]
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [add_lie, ihx, ihy, zero_add]
  | smul a x hx ihx => simpa only [smul_lie, ihx, smul_zero]

/-- A self-centralizing abelian real Lie subspace remains exactly
self-centralizing after literal scalar extension to `ℂ`. -/
theorem complexSpan_selfCentralizing
    (T : Submodule ℝ L)
    (habel : ∀ x ∈ T, ∀ y ∈ T, ⁅x,y⁆ = 0)
    (hself : ∀ x : L, (∀ t ∈ T, ⁅x,t⁆ = 0) → x ∈ T)
    (z : ℂ ⊗[ℝ] L) :
    z ∈ complexSpan T ↔
      ∀ t ∈ T, ⁅z, (1 : ℂ) ⊗ₜ[ℝ] t⁆ = 0 := by
  constructor
  · intro hz t ht
    exact complexSpan_centralizes_of_abelian T habel hz t ht
  · exact mem_complexSpan_of_centralizes T hself z

theorem complexSpan_selfCentralizing_full
    (T : Submodule ℝ L)
    (habel : ∀ x ∈ T, ∀ y ∈ T, ⁅x,y⁆ = 0)
    (hself : ∀ x : L, (∀ t ∈ T, ⁅x,t⁆ = 0) → x ∈ T)
    (z : ℂ ⊗[ℝ] L) :
    z ∈ complexSpan T ↔
      ∀ w ∈ complexSpan T, ⁅z,w⁆ = 0 := by
  constructor
  · intro hz w hw
    have hsmall := (complexSpan_selfCentralizing T habel hself z).mp hz
    induction hw using Submodule.span_induction with
    | mem w hw =>
        obtain ⟨t,rfl⟩ := hw
        exact hsmall t.1 t.2
    | zero => simp
    | add x y hx hy ihx ihy => simpa only [lie_add, ihx, ihy, zero_add]
    | smul a x hx ihx => simpa only [lie_smul, ihx, smul_zero]
  · intro hz
    apply (complexSpan_selfCentralizing T habel hself z).mpr
    intro t ht
    exact hz ((1 : ℂ) ⊗ₜ[ℝ] t) (one_tmul_mem_complexSpan T ht)

end
end QuaternionicSymmetry.ComplexifiedLieCentralizerComponents
