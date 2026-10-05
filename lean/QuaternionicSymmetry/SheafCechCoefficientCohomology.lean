import QuaternionicSymmetry.SheafCechCoefficientMap
import QuaternionicSymmetry.SheafExtensionReconstructionClass
import QuaternionicSymmetry.DerivedExtensionClassNaturality

/-! Coefficient change of genuine cocycles induces exactly the covariant
map on Mathlib's derived H¹, proved from the actual extension morphism. -/

namespace QuaternionicSymmetry.SheafCechCoefficientCohomology

open CategoryTheory CategoryTheory.Abelian TopologicalSpace
open AbelianSheafCohomology SheafCechOneCocycle SheafCechExtension
open SheafCechTwistedPresheafSequence SheafCechCoefficientMap
open SheafExtensionReconstructionClass DerivedExtensionClassNaturality
noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type}
  {A D : AbelianSheaves B} (f : A ⟶ D) {U : ι → Opens B} (c : OneCocycle A U)

theorem originalSheafIso_inv_naturality :
    (originalSheafIso (A := A)).inv ≫ (sheafification (B := B)).map f.val =
      f ≫ (originalSheafIso (A := D)).inv := by
  apply (cancel_mono (originalSheafIso (A := D)).hom).mp
  rw [Category.assoc, originalSheafIso_naturality,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

def coefficientMiddleMap :
    (extensionComplex c).X₂ ⟶ (extensionComplex (mappedCocycle f c)).X₂ :=
  (sheafification (B := B)).map (coefficientNat f c)

theorem coefficientMiddleMap_inclusion :
    (extensionComplex c).f ≫ coefficientMiddleMap f c =
      f ≫ (extensionComplex (mappedCocycle f c)).f := by
  let F := sheafification (B := B)
  change ((originalSheafIso (A := A)).inv ≫ F.map (inclusionNat c)) ≫
    F.map (coefficientNat f c) =
    f ≫ (originalSheafIso (A := D)).inv ≫ F.map (inclusionNat (mappedCocycle f c))
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp,
    inclusionNat_coefficientNat, CategoryTheory.Functor.map_comp,
    ← Category.assoc, originalSheafIso_inv_naturality, Category.assoc]

theorem coefficientMiddleMap_projection :
    coefficientMiddleMap f c ≫ (extensionComplex (mappedCocycle f c)).g =
      (extensionComplex c).g := by
  change (sheafification (B := B)).map (coefficientNat f c) ≫
    (sheafification (B := B)).map (projectionNat (mappedCocycle f c)) =
      (sheafification (B := B)).map (projectionNat c)
  rw [← CategoryTheory.Functor.map_comp, coefficientNat_projectionNat]

theorem cohomologyClass_mapped (hcover : ∀ x : B, ∃ i, x ∈ U i) :
    cohomologyClass (mappedCocycle f c) hcover =
      (cohomologyClass c hcover).comp (Ext.mk₀ f) (add_zero 1) := by
  let φ : extensionComplex c ⟶ extensionComplex (mappedCocycle f c) := {
    τ₁ := f
    τ₂ := coefficientMiddleMap f c
    τ₃ := 𝟙 (integralSheaf B)
    comm₁₂ := (coefficientMiddleMap_inclusion f c).symm
    comm₂₃ := by simpa only [Category.comp_id] using coefficientMiddleMap_projection f c }
  have h := extClass_naturality (extensionComplex_shortExact c hcover)
    (extensionComplex_shortExact (mappedCocycle f c) hcover) φ
  change (cohomologyClass c hcover).comp (Ext.mk₀ f) (add_zero 1) =
    (Ext.mk₀ (𝟙 (integralSheaf B))).comp
      (cohomologyClass (mappedCocycle f c) hcover) (zero_add 1) at h
  simpa only [Ext.mk₀_id_comp] using h.symm

end
end QuaternionicSymmetry.SheafCechCoefficientCohomology
