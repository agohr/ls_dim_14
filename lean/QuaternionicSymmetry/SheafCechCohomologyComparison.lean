import QuaternionicSymmetry.SheafCechExtension
import QuaternionicSymmetry.SheafCechTwistedSectionComparison
import QuaternionicSymmetry.DerivedExtensionClassComparison

/-! A coboundary comparison on one actual open cover gives equality in
Mathlib's derived H¹, by the natural map of constructed short exact
extensions. Refinements and arbitrary cover comparisons are subsequent. -/

namespace QuaternionicSymmetry.SheafCechCohomologyComparison

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open SheafCechOneCocycle SheafCechCocycleComparison
open SheafCechTwistedPresheafSequence SheafCechTwistedSectionComparison
open SheafCechExtension DerivedExtensionClassComparison
noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type}
  {A : TopCat.Sheaf AddCommGrpCat (TopCat.of B)} {U : ι → Opens B}
  {c d : OneCocycle A U} (e : Comparison c d)

theorem inclusionNat_comparisonNat : inclusionNat c ≫ comparisonNat e = inclusionNat d := by
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.ext
  intro s
  exact sectionMap_inclusion e V.unop s

theorem comparisonNat_projectionNat : comparisonNat e ≫ projectionNat d = projectionNat c := by
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.ext
  intro s
  rfl

def extensionMiddleMap : (extensionComplex c).X₂ ⟶ (extensionComplex d).X₂ :=
  (sheafification (B := B)).map (comparisonNat e)

theorem extensionMiddleMap_inclusion :
    (extensionComplex c).f ≫ extensionMiddleMap e = (extensionComplex d).f := by
  change ((originalSheafIso (A := A)).inv ≫
    (sheafification (B := B)).map (inclusionNat c)) ≫
      (sheafification (B := B)).map (comparisonNat e) =
    (originalSheafIso (A := A)).inv ≫
      (sheafification (B := B)).map (inclusionNat d)
  rw [Category.assoc, ← Functor.map_comp, inclusionNat_comparisonNat]

theorem extensionMiddleMap_projection :
    extensionMiddleMap e ≫ (extensionComplex d).g = (extensionComplex c).g := by
  change (sheafification (B := B)).map (comparisonNat e) ≫
    (sheafification (B := B)).map (projectionNat d) =
    (sheafification (B := B)).map (projectionNat c)
  rw [← Functor.map_comp, comparisonNat_projectionNat]

include e in
/-- An actual coboundary comparison preserves the actual derived class,
not merely a newly defined equivalence class of cocycle data. -/
theorem cohomologyClass_eq (hcover : ∀ x : B, ∃ i, x ∈ U i) :
    cohomologyClass c hcover = cohomologyClass d hcover := by
  exact extClass_eq_of_middle_map
    (extensionComplex c).f (extensionComplex c).g (extensionComplex c).zero
    (extensionComplex d).f (extensionComplex d).g (extensionComplex d).zero
    (extensionComplex_shortExact c hcover) (extensionComplex_shortExact d hcover)
    (extensionMiddleMap e) (extensionMiddleMap_inclusion e) (extensionMiddleMap_projection e)

end
end QuaternionicSymmetry.SheafCechCohomologyComparison
