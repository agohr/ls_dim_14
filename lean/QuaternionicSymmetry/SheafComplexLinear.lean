import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Sites.Abelian

/-! The category of sheaves of complex modules is complex linear. Mathlib's
sheaf category already has additive hom groups; this file identifies their
pointwise complex scalar action with composition. -/

namespace QuaternionicSymmetry.SheafComplexLinear

open CategoryTheory TopologicalSpace

universe u v w z

/-- A linear right adjoint makes the additive hom-set adjunction linear. -/
noncomputable def adjunctionHomLinearEquiv
    {R : Type*} [CommSemiring R]
    {C : Type*} {D : Type*}
    [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [Linear R C] [Linear R D]
    {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) [F.Additive] [G.Linear R]
    (X : C) (Y : D) : (F.obj X ⟶ Y) ≃ₗ[R] (X ⟶ G.obj Y) := by
  refine { adj.homAddEquiv X Y with map_smul' := ?_ }
  intro r f
  change (adj.homEquiv X Y) (r • f) = r • (adj.homEquiv X Y) f
  calc
    (adj.homEquiv X Y) (r • f) =
        (adj.homEquiv X Y) (f ≫ (r • 𝟙 Y)) := by simp
    _ = (adj.homEquiv X Y) f ≫ G.map (r • 𝟙 Y) :=
      adj.homEquiv_naturality_right f (r • 𝟙 Y)
    _ = r • (adj.homEquiv X Y) f := by simp


variable {C : Type u} [Category.{v} C]
  {J : GrothendieckTopology C}

private example [HasSheafify J (ModuleCat.{w} ℂ)] :
    Abelian (Sheaf J (ModuleCat.{w} ℂ)) := inferInstance

private example [HasSheafify J (ModuleCat.{w} ℂ)] :
    (inferInstance : Abelian (Sheaf J (ModuleCat.{w} ℂ))).toPreadditive =
      (inferInstance : Preadditive (Sheaf J (ModuleCat.{w} ℂ))) := by
  rfl



noncomputable instance sheafHomSMul
    (F G : Sheaf J (ModuleCat.{w} ℂ)) : SMul ℂ (F ⟶ G) :=
  ⟨fun c f => ⟨c • f.val⟩⟩

noncomputable instance sheafHomModule
    (F G : Sheaf J (ModuleCat.{w} ℂ)) : Module ℂ (F ⟶ G) :=
  Function.Injective.module ℂ
    { toFun := fun f => f.val
      map_zero' := rfl
      map_add' := by intro f g; rfl }
    (fun _ _ h => Sheaf.Hom.ext h)
    (by intro c f; rfl)

noncomputable instance sheafLinear : Linear ℂ (Sheaf J (ModuleCat.{w} ℂ)) where
  homModule := sheafHomModule
  smul_comp := by
    intro F G H c f g
    apply Sheaf.Hom.ext
    exact Linear.smul_comp F.val G.val H.val c f.val g.val
  comp_smul := by
    intro F G H f c g
    apply Sheaf.Hom.ext
    exact Linear.comp_smul F.val G.val H.val f.val c g.val

noncomputable instance sheafSectionsLinear (X : C) :
    Functor.Linear ℂ
      ((CategoryTheory.sheafSections J (ModuleCat.{w} ℂ)).obj (Opposite.op X)) where
  map_smul := by
    intro F G f c
    rfl

/-- Morphisms of complex module objects are the usual linear maps, with
the same pointwise complex scalar action. -/
noncomputable def moduleCatHomLinearEquiv (A B : ModuleCat.{w} ℂ) :
    (A ⟶ B) ≃ₗ[ℂ] (A →ₗ[ℂ] B) := by
  refine { ModuleCat.homEquiv with map_add' := ?_, map_smul' := ?_ }
  · intro f g
    rfl
  · intro c f
    rfl

noncomputable instance topCatSheafPreadditive (X : TopCat.{u}) :
    Preadditive (TopCat.Sheaf (ModuleCat.{w} ℂ) X) := by
  change Preadditive (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{w} ℂ))
  infer_instance

noncomputable instance topCatSheafAbelian (X : TopCat.{u})
    [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{w} ℂ)] :
    Abelian (TopCat.Sheaf (ModuleCat.{w} ℂ) X) := by
  change Abelian (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{w} ℂ))
  infer_instance

noncomputable instance topCatSheafLinear (X : TopCat.{u}) :
    Linear ℂ (TopCat.Sheaf (ModuleCat.{w} ℂ) X) := by
  change Linear ℂ (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{w} ℂ))
  infer_instance

theorem preadditive_eq (X : TopCat.{u})
    [hA : Abelian (TopCat.Sheaf (ModuleCat.{w} ℂ) X)] :
    hA.toPreadditive = topCatSheafPreadditive X := by
  letI : Limits.HasFiniteProducts (TopCat.Sheaf (ModuleCat.{w} ℂ) X) :=
    Abelian.has_finite_products
  letI : Limits.HasBinaryProducts (TopCat.Sheaf (ModuleCat.{w} ℂ) X) :=
    inferInstance
  letI : Limits.HasBinaryBiproducts (TopCat.Sheaf (ModuleCat.{w} ℂ) X) :=
    Limits.HasBinaryBiproducts.of_hasBinaryProducts
  exact Subsingleton.elim _ _

noncomputable instance sheafExtModule (X : TopCat.{u})
    [hA : Abelian (TopCat.Sheaf (ModuleCat.{w} ℂ) X)]
    [hE : HasExt.{z} (TopCat.Sheaf (ModuleCat.{w} ℂ) X)]
    (F G : TopCat.Sheaf (ModuleCat.{w} ℂ) X) (n : ℕ) :
    Module ℂ (Abelian.Ext.{z} F G n) := by
  let C := TopCat.Sheaf (ModuleCat.{w} ℂ) X
  have hLin : @Linear ℂ Complex.instSemiring C inferInstance hA.toPreadditive :=
    (preadditive_eq X).symm ▸ topCatSheafLinear X
  exact @Abelian.Ext.instModule ℂ inferInstance
    C inferInstance hA hLin hE F G n


end QuaternionicSymmetry.SheafComplexLinear
