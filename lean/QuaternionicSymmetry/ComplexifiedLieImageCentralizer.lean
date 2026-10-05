import QuaternionicSymmetry.ComplexifiedLieCentralizerComponents
import QuaternionicSymmetry.RealToComplexTangentComplexificationLinear

/-! Centralization of an actual real differential image extends to its
literal complexified image. This is only linear/Lie algebra; applications
must establish the real differential identities on the actual manifolds. -/

namespace QuaternionicSymmetry.ComplexifiedLieImageCentralizer

open ComplexifiedLieCentralizerComponents
open RealToComplexTangentComplexification
open scoped TensorProduct
noncomputable section

variable {L V W : Type*} [LieRing L] [LieAlgebra ℝ L]
  [LieRing V] [LieAlgebra ℂ V] [AddCommGroup W] [Module ℝ W]

theorem centralizes_complexified_image
    (T : Submodule ℝ L) (f : L →ₗ[ℝ] V) (z : V)
    (hz : ∀ t ∈ T, ⁅z, f t⁆ = 0)
    {s : V} (hs : s ∈ (complexSpan T).map (complexifiedMapComplex f)) :
    ⁅z, s⁆ = 0 := by
  obtain ⟨t, ht, rfl⟩ := hs
  induction ht using Submodule.span_induction with
  | mem t ht =>
      obtain ⟨u, rfl⟩ := ht
      simpa only [complexifiedMapComplex_tmul, one_smul] using hz u.1 u.2
  | zero => simp
  | add x y hx hy ihx ihy =>
      simpa only [map_add, lie_add, ihx, ihy, zero_add]
  | smul a x hx ihx =>
      simpa only [map_smul, lie_smul, ihx, smul_zero]

theorem centralizes_complexified_image_iff
    (T : Submodule ℝ L) (f : L →ₗ[ℝ] V) (z : V) :
    (∀ s ∈ (complexSpan T).map (complexifiedMapComplex f), ⁅z,s⁆ = 0) ↔
      ∀ t ∈ T, ⁅z, f t⁆ = 0 := by
  constructor
  · intro h t ht
    have hm : f t ∈ (complexSpan T).map (complexifiedMapComplex f) := by
      refine ⟨(1 : ℂ) ⊗ₜ[ℝ] t, one_tmul_mem_complexSpan T ht, ?_⟩
      simp only [complexifiedMapComplex_tmul, one_smul]
    exact h (f t) hm
  · intro h s hs
    exact centralizes_complexified_image T f z h hs

theorem centralizes_complexified_image_of_range
    (T : Submodule ℝ L) (f : L →ₗ[ℝ] V) (g : W →ₗ[ℝ] L)
    (hRange : T = LinearMap.range g) (z : V)
    (hz : ∀ w : W, ⁅z, f (g w)⁆ = 0)
    {s : V} (hs : s ∈ (complexSpan T).map (complexifiedMapComplex f)) :
    ⁅z,s⁆ = 0 := by
  apply centralizes_complexified_image T f z _ hs
  intro t ht
  rw [hRange] at ht
  obtain ⟨w, rfl⟩ := ht
  exact hz w

end
end QuaternionicSymmetry.ComplexifiedLieImageCentralizer
