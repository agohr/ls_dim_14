import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Adjunction

/-! Exact adjoint functors induce an actual adjunction on the derived
categories. This is an internal bridge for changing sheaf coefficients,
not an assumption identifying two cohomology theories. -/

namespace QuaternionicSymmetry.DerivedExactAdjunction

open CategoryTheory CategoryTheory.Limits
noncomputable section

universe u₁ u₂ v₁ v₂ w₁ w₂

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  [F.Additive] [G.Additive]

def complexAdjunction {ι : Type*} (c : ComplexShape ι) :
    F.mapHomologicalComplex c ⊣ G.mapHomologicalComplex c where
  unit :=
    { app := fun K =>
        { f := fun i => adj.unit.app (K.X i)
          comm' := fun i j _ => (adj.unit.naturality (K.d i j)).symm }
      naturality := fun K L f => by
        ext i
        exact adj.unit.naturality (f.f i) }
  counit :=
    { app := fun K =>
        { f := fun i => adj.counit.app (K.X i)
          comm' := fun i j _ => (adj.counit.naturality (K.d i j)).symm }
      naturality := fun K L f => by
        ext i
        exact adj.counit.naturality (f.f i) }
  left_triangle_components K := by
    ext i
    exact adj.left_triangle_components (K.X i)
  right_triangle_components K := by
    ext i
    exact adj.right_triangle_components (K.X i)

variable [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

def derivedAdjunction : F.mapDerivedCategory ⊣ G.mapDerivedCategory := by
  letI : CatCommSq (F.mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q F.mapDerivedCategory :=
    ⟨F.mapDerivedCategoryFactors.symm⟩
  letI : CatCommSq (G.mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q G.mapDerivedCategory :=
    ⟨G.mapDerivedCategoryFactors.symm⟩
  exact (complexAdjunction adj (ComplexShape.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso D (ComplexShape.up ℤ))
    F.mapDerivedCategory G.mapDerivedCategory

end
end QuaternionicSymmetry.DerivedExactAdjunction
