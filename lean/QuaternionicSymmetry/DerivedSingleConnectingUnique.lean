import QuaternionicSymmetry.DerivedHeartTriangleShortExact
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-! A distinguished triangle on the two actual maps of a short exact
sequence has its canonical connecting morphism. The third triangle map is
forced to be the identity using fullness and the actual quotient epimorphism
in the original category, not an epimorphism assumption in the derived one. -/

namespace QuaternionicSymmetry.DerivedSingleConnectingUnique

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open DerivedCategory
noncomputable section

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

theorem singleδ_eq_of_distinguished {S : ShortComplex C} (hS : S.ShortExact)
    (δ : (singleFunctor C 0).obj S.X₃ ⟶ ((singleFunctor C 0).obj S.X₁)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk ((singleFunctor C 0).map S.f)
      ((singleFunctor C 0).map S.g) δ ∈ distTriang (DerivedCategory C)) :
    hS.singleδ = δ := by
  let F := singleFunctor C 0
  let T := Triangle.mk (F.map S.f) (F.map S.g) δ
  obtain ⟨c, hc, hδ⟩ := complete_distinguished_triangle_morphism
    hS.singleTriangle T hS.singleTriangle_distinguished hT
    (𝟙 (F.obj S.X₁)) (𝟙 (F.obj S.X₂)) (by
      change F.map S.f ≫ 𝟙 _ = 𝟙 _ ≫ F.map S.f
      rw [Category.comp_id, Category.id_comp])
  let k : S.X₃ ⟶ S.X₃ := F.preimage c
  have hk : F.map k = c := F.map_preimage c
  have hgk : S.g ≫ k = S.g := by
    apply F.map_injective
    rw [CategoryTheory.Functor.map_comp, hk]
    change F.map S.g ≫ c = 𝟙 _ ≫ F.map S.g at hc
    simpa only [Category.id_comp] using hc
  letI := hS.epi_g
  have hkid : k = 𝟙 S.X₃ := (cancel_epi S.g).1 (by
    simpa only [Category.comp_id] using hgk)
  have hcid : c = 𝟙 (F.obj S.X₃) := by
    rw [← hk, hkid, CategoryTheory.Functor.map_id]
  change hS.singleδ ≫ (shiftFunctor (DerivedCategory C) (1 : ℤ)).map
      (𝟙 (F.obj S.X₁)) = c ≫ δ at hδ
  rw [CategoryTheory.Functor.map_id, Category.comp_id, hcid] at hδ
  exact hδ.trans (Category.id_comp δ)

end
end QuaternionicSymmetry.DerivedSingleConnectingUnique
