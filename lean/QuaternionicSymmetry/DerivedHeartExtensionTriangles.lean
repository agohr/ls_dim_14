import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! Extensions of objects concentrated in degree zero stay concentrated
in degree zero. Hence any genuine derived degree-one morphism between
single objects completes to a triangle whose middle object also comes
from the original abelian category. No extension representability premise
is introduced. Short exactness and recovery of the Ext class follow later. -/

namespace QuaternionicSymmetry.DerivedHeartExtensionTriangles

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open DerivedCategory
noncomputable section

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

theorem triangle_middle_isGE (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang _) (n : ℤ) [T.obj₁.IsGE n] [T.obj₃.IsGE n] :
    T.obj₂.IsGE n := by
  apply (DerivedCategory.isGE_iff T.obj₂ n).2
  intro i hi
  have h₁ := DerivedCategory.isZero_of_isGE T.obj₁ n i hi
  have h₃ := DerivedCategory.isZero_of_isGE T.obj₃ n i hi
  exact ((homologyFunctor C i).map_distinguished_exact T hT).isZero_X₂
    (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)

theorem triangle_middle_isLE (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang _) (n : ℤ) [T.obj₁.IsLE n] [T.obj₃.IsLE n] :
    T.obj₂.IsLE n := by
  apply (DerivedCategory.isLE_iff T.obj₂ n).2
  intro i hi
  have h₁ := DerivedCategory.isZero_of_isLE T.obj₁ n i hi
  have h₃ := DerivedCategory.isZero_of_isLE T.obj₃ n i hi
  exact ((homologyFunctor C i).map_distinguished_exact T hT).isZero_X₂
    (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)

theorem exists_single_middle {X Y : C}
    (δ : (singleFunctor C 0).obj Y ⟶ ((singleFunctor C 0).obj X)⟦(1 : ℤ)⟧) :
    ∃ (M : C) (f : X ⟶ M) (g : M ⟶ Y),
      Triangle.mk ((singleFunctor C 0).map f) ((singleFunctor C 0).map g) δ ∈
        distTriang (DerivedCategory C) := by
  let F := singleFunctor C 0
  obtain ⟨K, a, b, hT⟩ := distinguished_cocone_triangle₂ δ
  let T := Triangle.mk a b δ
  letI : T.obj₁.IsGE 0 :=
    inferInstanceAs (((singleFunctor C 0).obj X).IsGE 0)
  letI : T.obj₃.IsGE 0 :=
    inferInstanceAs (((singleFunctor C 0).obj Y).IsGE 0)
  letI : T.obj₁.IsLE 0 :=
    inferInstanceAs (((singleFunctor C 0).obj X).IsLE 0)
  letI : T.obj₃.IsLE 0 :=
    inferInstanceAs (((singleFunctor C 0).obj Y).IsLE 0)
  letI : K.IsGE 0 := triangle_middle_isGE T hT 0
  letI : K.IsLE 0 := triangle_middle_isLE T hT 0
  obtain ⟨M, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE K 0
  let f : X ⟶ M := F.preimage (a ≫ e.hom)
  let g : M ⟶ Y := F.preimage (e.inv ≫ b)
  refine ⟨M, f, g, ?_⟩
  have hf : F.map f = a ≫ e.hom := F.map_preimage _
  have hg : F.map g = e.inv ≫ b := F.map_preimage _
  change Triangle.mk (F.map f) (F.map g) δ ∈ distTriang _
  rw [hf, hg]
  apply isomorphic_distinguished T hT
  exact Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _)
    (by simp [T]) (by simp [T]) (by simp [T])

end
end QuaternionicSymmetry.DerivedHeartExtensionTriangles
