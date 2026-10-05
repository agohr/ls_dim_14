import QuaternionicSymmetry.SheafExtensionReconstructionProjection
import QuaternionicSymmetry.SheafCechExtension
import QuaternionicSymmetry.DerivedExtensionClassComparison

/-! The cocycle reconstructed from an actual sheaf extension has exactly
that extension's original derived class. The comparison morphism is obtained
by genuine gluing and sheafification and preserves both end maps. -/

namespace QuaternionicSymmetry.SheafExtensionReconstructionClass

open CategoryTheory TopologicalSpace Opposite
open AbelianSheafCohomology SheafCechOneCocycle
open IntegralSheafLocalUnitLift SheafExtensionCocycle SheafCechTwistedSections
open SheafCechTwistedPresheafSequence SheafCechExtension
open SheafExtensionReconstructionNatural SheafExtensionReconstructionProjection
open DerivedExtensionClassComparison
noncomputable section

variable {B : Type} [TopologicalSpace B]

theorem originalSheafIso_naturality {A M : AbelianSheaves B} (f : A ⟶ M) :
    (sheafification (B := B)).map f.val ≫ (originalSheafIso (A := M)).hom =
      (originalSheafIso (A := A)).hom ≫ f :=
  (sheafificationAdjunction (Opens.grothendieckTopology (TopCat.of B))
    AddCommGrpCat).counit.naturality f

variable {ι : Type} {A M : AbelianSheaves B}
  (f : A ⟶ M) (g : M ⟶ integralSheaf B)
  (hfg : f ≫ g = 0) (hS : (ShortComplex.mk f g hfg).ShortExact)
  {U : ι → Opens B} (s : ∀ i, M.val.obj (op (U i)))
  (hs : ∀ i, g.val.app (op (U i)) (s i) = unitSection (U i))
  (hcover : ∀ x : B, ∃ i, x ∈ U i)

def reconstructionMiddleMap : (extensionComplex (cocycle f g hfg hS s hs)).X₂ ⟶ M :=
  (sheafification (B := B)).map (reconstructionNat f g hfg hS s hs hcover) ≫
    (originalSheafIso (A := M)).hom

theorem reconstructionMiddleMap_inclusion :
    (extensionComplex (cocycle f g hfg hS s hs)).f ≫
      reconstructionMiddleMap f g hfg hS s hs hcover = f := by
  let F := sheafification (B := B)
  change ((originalSheafIso (A := A)).inv ≫
    F.map (inclusionNat (cocycle f g hfg hS s hs))) ≫
    F.map (reconstructionNat f g hfg hS s hs hcover) ≫
      (originalSheafIso (A := M)).hom = f
  rw [Category.assoc, ← Category.assoc (F.map _), ← CategoryTheory.Functor.map_comp,
    inclusionNat_reconstructionNat, originalSheafIso_naturality]
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

theorem reconstructionMiddleMap_projection :
    reconstructionMiddleMap f g hfg hS s hs hcover ≫ g =
      (extensionComplex (cocycle f g hfg hS s hs)).g := by
  let F := sheafification (B := B)
  let J := Opens.grothendieckTopology (TopCat.of B)
  let P := constantIntegerPresheaf (B := B)
  change (F.map (reconstructionNat f g hfg hS s hs hcover) ≫
    (originalSheafIso (A := M)).hom) ≫ g =
      F.map (projectionNat (cocycle f g hfg hS s hs))
  rw [Category.assoc, ← originalSheafIso_naturality g,
    ← Category.assoc, ← CategoryTheory.Functor.map_comp,
    reconstructionNat_projection, CategoryTheory.Functor.map_comp, Category.assoc]
  have htri : F.map (toSheafify J P) ≫
      (originalSheafIso (A := integralSheaf B)).hom = 𝟙 (F.obj P) :=
    (sheafificationAdjunction J AddCommGrpCat).left_triangle_components P
  rw [htri, Category.comp_id]

theorem reconstructed_cohomologyClass :
    cohomologyClass (cocycle f g hfg hS s hs) hcover = hS.extClass :=
  extClass_eq_of_middle_map
    (extensionComplex (cocycle f g hfg hS s hs)).f
    (extensionComplex (cocycle f g hfg hS s hs)).g
    (extensionComplex (cocycle f g hfg hS s hs)).zero
    f g hfg (extensionComplex_shortExact _ hcover) hS
    (reconstructionMiddleMap f g hfg hS s hs hcover)
    (reconstructionMiddleMap_inclusion f g hfg hS s hs hcover)
    (reconstructionMiddleMap_projection f g hfg hS s hs hcover)

end
end QuaternionicSymmetry.SheafExtensionReconstructionClass
