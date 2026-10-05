import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-! Vanishing of the actual derived extension class is equivalent to an
actual section of the quotient morphism. This is a consequence of the
derived Ext long exact sequence, not an assumed classification of Ext¹. -/

namespace QuaternionicSymmetry.DerivedExtensionClassSplitting

open CategoryTheory CategoryTheory.Abelian
noncomputable section

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {S : ShortComplex C} (hS : S.ShortExact)

theorem extClass_eq_zero_iff_section :
    hS.extClass = 0 ↔ ∃ s : S.X₃ ⟶ S.X₂, s ≫ S.g = 𝟙 S.X₃ := by
  constructor
  · intro h
    have hδ : (Ext.mk₀ (𝟙 S.X₃)).comp hS.extClass (zero_add 1) = 0 := by
      rw [Ext.mk₀_id_comp, h]
    obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₃ S.X₃ hS
      (Ext.mk₀ (𝟙 S.X₃)) (zero_add 1) hδ
    obtain ⟨s, rfl⟩ := (Ext.mk₀_bijective S.X₃ S.X₂).surjective x
    exact ⟨s, (Ext.mk₀_bijective S.X₃ S.X₃).injective (by
      simpa only [Ext.mk₀_comp_mk₀] using hx)⟩
  · rintro ⟨s, hs⟩
    calc
      hS.extClass = (Ext.mk₀ (s ≫ S.g)).comp hS.extClass (zero_add 1) := by
        rw [hs, Ext.mk₀_id_comp]
      _ = (Ext.mk₀ s).comp
          ((Ext.mk₀ S.g).comp hS.extClass (zero_add 1)) (zero_add 1) :=
        (Ext.mk₀_comp_mk₀_assoc s S.g hS.extClass).symm
      _ = 0 := by rw [hS.comp_extClass, Ext.comp_zero]

end
end QuaternionicSymmetry.DerivedExtensionClassSplitting
