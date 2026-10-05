import QuaternionicSymmetry.DerivedShortExactNaturality

/-! A genuine map of short exact sequences which is the identity on the
two end objects preserves their actual derived extension classes. -/

namespace QuaternionicSymmetry.DerivedExtensionClassComparison

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Abelian
open DerivedCategory DerivedShortExactNaturality
noncomputable section

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

theorem extClass_eq_of_middle_map {X Y M N : C}
    (f : X ⟶ M) (g : M ⟶ Y) (hfg : f ≫ g = 0)
    (f' : X ⟶ N) (g' : N ⟶ Y) (hfg' : f' ≫ g' = 0)
    (hS : (ShortComplex.mk f g hfg).ShortExact)
    (hT : (ShortComplex.mk f' g' hfg').ShortExact)
    (k : M ⟶ N) (hkf : f ≫ k = f') (hkg : k ≫ g' = g) :
    hS.extClass = hT.extClass := by
  letI := HasDerivedCategory.standard C
  let S := ShortComplex.mk f g hfg
  let T := ShortComplex.mk f' g' hfg'
  let φ : S ⟶ T := {
    τ₁ := 𝟙 X
    τ₂ := k
    τ₃ := 𝟙 Y
    comm₁₂ := by
      change 𝟙 X ≫ f' = f ≫ k
      rw [Category.id_comp, hkf]
    comm₂₃ := by
      change k ≫ g' = g ≫ 𝟙 Y
      rw [Category.comp_id, hkg] }
  let F := HomologicalComplex.single C (ComplexShape.up ℤ) 0
  let φ' := F.mapShortComplex.map φ
  have hδ := triangleOfSESδ_naturality (hS.map_of_exact F) (hT.map_of_exact F) φ'
  have hφ₁ : φ'.τ₁ = 𝟙 (F.obj X) := F.map_id X
  have hφ₃ : φ'.τ₃ = 𝟙 (F.obj Y) := F.map_id Y
  rw [hφ₁, hφ₃] at hδ
  have hQX : Q.map (𝟙 (F.obj X)) = 𝟙 (Q.obj (F.obj X)) :=
    CategoryTheory.Functor.map_id (Q : CochainComplex C ℤ ⥤ DerivedCategory C) (F.obj X)
  have hQY : Q.map (𝟙 (F.obj Y)) = 𝟙 (Q.obj (F.obj Y)) :=
    CategoryTheory.Functor.map_id (Q : CochainComplex C ℤ ⥤ DerivedCategory C) (F.obj Y)
  have hShift : (shiftFunctor (DerivedCategory C) (1 : ℤ)).map
      (𝟙 (Q.obj (F.obj X))) =
      𝟙 ((shiftFunctor (DerivedCategory C) (1 : ℤ)).obj (Q.obj (F.obj X))) :=
    (shiftFunctor (DerivedCategory C) (1 : ℤ)).map_id _
  rw [hQX, hQY, hShift] at hδ
  erw [Category.id_comp (triangleOfSESδ (hT.map_of_exact F)),
    Category.comp_id (triangleOfSESδ (hS.map_of_exact F))] at hδ
  have hδ' : triangleOfSESδ (hS.map_of_exact F) =
      triangleOfSESδ (hT.map_of_exact F) := by
    exact hδ.symm
  apply Ext.ext
  erw [hS.extClass_hom, hT.extClass_hom]
  dsimp only [ShortComplex.ShortExact.singleδ]
  erw [hδ']

end
end QuaternionicSymmetry.DerivedExtensionClassComparison
