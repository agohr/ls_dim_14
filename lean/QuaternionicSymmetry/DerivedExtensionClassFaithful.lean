import QuaternionicSymmetry.DerivedExtensionClassComparison

/-! Equality of derived Ext¹ classes of short exact sequences with fixed
end objects yields an actual middle-object comparison in the original
abelian category. Distinguished-triangle completion and full faithfulness
of the single-complex functor supply the comparison internally. -/

namespace QuaternionicSymmetry.DerivedExtensionClassFaithful

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Pretriangulated
open DerivedCategory DerivedExtensionClassComparison
noncomputable section

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

theorem extClass_eq_iff_middle_map {X Y M N : C}
    (f : X ⟶ M) (g : M ⟶ Y) (hfg : f ≫ g = 0)
    (f' : X ⟶ N) (g' : N ⟶ Y) (hfg' : f' ≫ g' = 0)
    (hS : (ShortComplex.mk f g hfg).ShortExact)
    (hT : (ShortComplex.mk f' g' hfg').ShortExact) :
    hS.extClass = hT.extClass ↔
      ∃ k : M ⟶ N, f ≫ k = f' ∧ k ≫ g' = g := by
  constructor
  · intro h
    letI := HasDerivedCategory.standard C
    let F := singleFunctor C 0
    have hδ : hS.singleδ = hT.singleδ := by
      calc
        hS.singleδ = hS.extClass.hom := hS.extClass_hom.symm
        _ = hT.extClass.hom := congrArg _ h
        _ = hT.singleδ := hT.extClass_hom
    have hcomm : hS.singleTriangle.mor₃ ≫ (𝟙 (F.obj X))⟦(1 : ℤ)⟧' =
        𝟙 (F.obj Y) ≫ hT.singleTriangle.mor₃ := by
      change hS.singleδ ≫ (shiftFunctor (DerivedCategory C) (1 : ℤ)).map
        (𝟙 (F.obj X)) = 𝟙 (F.obj Y) ≫ hT.singleδ
      rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp, hδ]
    obtain ⟨b, hbf, hbg⟩ := complete_distinguished_triangle_morphism₂
      hS.singleTriangle hT.singleTriangle
      hS.singleTriangle_distinguished hT.singleTriangle_distinguished
      (𝟙 (F.obj X)) (𝟙 (F.obj Y)) hcomm
    let k : M ⟶ N := F.preimage b
    have hk : F.map k = b := F.map_preimage b
    refine ⟨k, ?_, ?_⟩
    · apply F.map_injective
      rw [CategoryTheory.Functor.map_comp, hk]
      change F.map f ≫ b = 𝟙 (F.obj X) ≫ F.map f' at hbf
      simpa only [Category.id_comp] using hbf
    · apply F.map_injective
      rw [CategoryTheory.Functor.map_comp, hk]
      change F.map g ≫ 𝟙 (F.obj Y) = b ≫ F.map g' at hbg
      simpa only [Category.comp_id] using hbg.symm
  · rintro ⟨k, hkf, hkg⟩
    exact extClass_eq_of_middle_map f g hfg f' g' hfg' hS hT k hkf hkg

end
end QuaternionicSymmetry.DerivedExtensionClassFaithful
