import QuaternionicSymmetry.DerivedSingleConnectingUnique

/-! Every genuine derived Ext¹ element is represented by an actual short
exact sequence in the original abelian category. The construction uses
distinguished triangles, concentration in degree zero, actual homology
exactness and uniqueness of the connecting map, all proved internally. -/

namespace QuaternionicSymmetry.DerivedExtensionClassRealization

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Pretriangulated
open DerivedCategory DerivedHeartExtensionTriangles DerivedHeartTriangleShortExact
open DerivedSingleConnectingUnique
noncomputable section

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

theorem exists_shortExact_extClass {X Y : C} (x : Ext Y X 1) :
    ∃ (M : C) (f : X ⟶ M) (g : M ⟶ Y) (hfg : f ≫ g = 0)
      (hS : (ShortComplex.mk f g hfg).ShortExact), hS.extClass = x := by
  letI := HasDerivedCategory.standard C
  let F := singleFunctor C 0
  obtain ⟨M, f, g, hT⟩ := exists_single_middle x.hom
  have hfg : f ≫ g = 0 := by
    apply F.map_injective
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero]
    exact comp_distTriang_mor_zero₁₂ _ hT
  let hS := shortExact_of_single_triangle f g hfg x.hom hT
  refine ⟨M, f, g, hfg, hS, ?_⟩
  apply Ext.ext
  calc
    hS.extClass.hom = hS.singleδ := hS.extClass_hom
    _ = x.hom := singleδ_eq_of_distinguished hS x.hom hT

end
end QuaternionicSymmetry.DerivedExtensionClassRealization
