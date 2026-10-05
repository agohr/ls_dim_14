import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! Internal linear algebra for extremal restriction. Surjectivity of a
restriction map remains an explicit premise: vanishing of the other basis
weights alone never proves extension of sections. Once extension is supplied,
the target dimension is bounded by the surviving weight submodule. -/

namespace QuaternionicSymmetry.SurjectiveRestrictionWeightBound

noncomputable section

variable {K V W ι : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

theorem domRestrict_surjective_of_basis_mem_or_zero
    (b : Module.Basis ι K V) (S : Submodule K V) (f : V →ₗ[K] W)
    (hf : Function.Surjective f)
    (hBasis : ∀ i, b i ∈ S ∨ f (b i) = 0) :
    Function.Surjective (f.domRestrict S) := by
  have hTop : (⊤ : Submodule K V) ≤ (S.map f).comap f := by
    rw [← b.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change f (b i) ∈ S.map f
    rcases hBasis i with hi | hi
    · exact Submodule.mem_map.mpr ⟨b i, hi, rfl⟩
    · rw [hi]
      exact (S.map f).zero_mem
  intro w
  obtain ⟨v, rfl⟩ := hf w
  have hv : f v ∈ S.map f := hTop (by trivial)
  obtain ⟨u, hu, heq⟩ := Submodule.mem_map.mp hv
  exact ⟨⟨u, hu⟩, heq⟩

theorem finrank_le_of_basis_mem_or_zero
    [Module.Finite K V]
    (b : Module.Basis ι K V) (S : Submodule K V) (f : V →ₗ[K] W)
    (hf : Function.Surjective f)
    (hBasis : ∀ i, b i ∈ S ∨ f (b i) = 0) :
    Module.finrank K W ≤ Module.finrank K S := by
  have hs := domRestrict_surjective_of_basis_mem_or_zero b S f hf hBasis
  have hr := (f.domRestrict S).finrank_range_le
  rw [LinearMap.range_eq_top.mpr hs, finrank_top] at hr
  exact hr

end
end QuaternionicSymmetry.SurjectiveRestrictionWeightBound
