import QuaternionicSymmetry.DerivedShortExactNaturality

/-! Full naturality of actual derived extension classes, allowing both
end objects to vary. This is needed for coefficient change and addition,
not only identity-end comparisons. -/

namespace QuaternionicSymmetry.DerivedExtensionClassNaturality

open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Abelian
open DerivedCategory DerivedShortExactNaturality
noncomputable section

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C]

section
variable [HasDerivedCategory.{w} C]

theorem singleδ_eq_triangleOfSESδ {S : ShortComplex C} (hS : S.ShortExact) :
    hS.singleδ = triangleOfSESδ
      (hS.map_of_exact (HomologicalComplex.single C (ComplexShape.up ℤ) 0)) := by
  change ((singleFunctorsPostcompQIso C).hom.hom 0).app S.X₃ ≫
      triangleOfSESδ (hS.map_of_exact (HomologicalComplex.single C (ComplexShape.up ℤ) 0)) ≫
      (((singleFunctorsPostcompQIso C).inv.hom 0).app S.X₁)⟦(1 : ℤ)⟧' = _
  rw [singleFunctorsPostcompQIso_hom_hom, singleFunctorsPostcompQIso_inv_hom,
    NatTrans.id_app, NatTrans.id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

theorem singleδ_naturality {S T : ShortComplex C}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) :
    (singleFunctor C 0).map φ.τ₃ ≫ hT.singleδ =
      hS.singleδ ≫ ((singleFunctor C 0).map φ.τ₁)⟦(1 : ℤ)⟧' := by
  rw [singleδ_eq_triangleOfSESδ, singleδ_eq_triangleOfSESδ]
  let F := HomologicalComplex.single C (ComplexShape.up ℤ) 0
  exact triangleOfSESδ_naturality (hS.map_of_exact F) (hT.map_of_exact F)
    (F.mapShortComplex.map φ)

end

variable [HasExt.{w} C]

theorem extClass_naturality {S T : ShortComplex C}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) :
    hS.extClass.comp (Ext.mk₀ φ.τ₁) (add_zero 1) =
      (Ext.mk₀ φ.τ₃).comp hT.extClass (zero_add 1) := by
  letI := HasDerivedCategory.standard C
  apply Ext.ext
  simp only [Ext.comp_hom, Ext.mk₀_hom, ShortComplex.ShortExact.extClass_hom,
    ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]
  exact (singleδ_naturality hS hT φ).symm

end
end QuaternionicSymmetry.DerivedExtensionClassNaturality
