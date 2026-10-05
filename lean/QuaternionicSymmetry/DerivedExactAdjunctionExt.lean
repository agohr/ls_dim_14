import QuaternionicSymmetry.DerivedExactAdjunction
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.HomCongr

/-! Exact adjunction gives an additive comparison of actual derived Ext,
in every degree. Both functors and their exactness remain explicit, so this
does not silently supply the sheaf change-of-coefficients construction. -/

namespace QuaternionicSymmetry.DerivedExactAdjunctionExt

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open DerivedExactAdjunction
noncomputable section

universe u₁ u₂ v₁ v₂ w₁ w₂ t₁ t₂

private def homAddCongr {A : Type*} [Category* A] [Preadditive A]
    {X Y X' Y' : A} (e : X ≅ X') (f : Y ≅ Y') :
    (X ⟶ Y) ≃+ (X' ⟶ Y') where
  toEquiv := Iso.homCongr e f
  map_add' a b := by simp [Iso.homCongr, Preadditive.comp_add, Preadditive.add_comp]

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
  [HasExt.{t₁} C] [HasExt.{t₂} D]

def extAddEquiv (X : C) (Y : D) (n : ℕ) :
    Ext.{t₂} (F.obj X) Y n ≃+ Ext.{t₁} X (G.obj Y) n :=
  Ext.homAddEquiv.trans
    ((homAddCongr ((F.mapDerivedCategorySingleFunctor 0).app X).symm
      (Iso.refl _)).trans
      (((derivedAdjunction adj).homAddEquiv
        ((DerivedCategory.singleFunctor C 0).obj X)
        (((DerivedCategory.singleFunctor D 0).obj Y)⟦(n : ℤ)⟧)).trans
        ((homAddCongr (Iso.refl _)
          (((G.mapDerivedCategory.commShiftIso (n : ℤ)).app
            ((DerivedCategory.singleFunctor D 0).obj Y)) ≪≫
            (shiftFunctor (DerivedCategory C) (n : ℤ)).mapIso
              ((G.mapDerivedCategorySingleFunctor 0).app Y))).trans
          Ext.homAddEquiv.symm)))

include adj in
theorem ext_subsingleton (X : C) (Y : D) (n : ℕ)
    (h : Subsingleton (Ext.{t₂} (F.obj X) Y n)) :
    Subsingleton (Ext.{t₁} X (G.obj Y) n) := by
  letI := h
  exact (extAddEquiv adj X Y n).symm.injective.subsingleton

end
end QuaternionicSymmetry.DerivedExactAdjunctionExt
