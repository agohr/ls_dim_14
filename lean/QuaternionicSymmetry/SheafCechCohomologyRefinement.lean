import QuaternionicSymmetry.SheafCechCohomologyComparison
import QuaternionicSymmetry.SheafCechRefinement

/-! Refining an actual open cover leaves the constructed class in genuine
derived H¹ unchanged. -/

namespace QuaternionicSymmetry.SheafCechCohomologyRefinement

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open SheafCechOneCocycle SheafCechRefinement SheafCechTwistedPresheafSequence
open SheafCechExtension DerivedExtensionClassComparison
noncomputable section

variable {B : Type} [TopologicalSpace B] {ι κ : Type}
  {A : TopCat.Sheaf AddCommGrpCat (TopCat.of B)}
  {U : ι → Opens B} {V : κ → Opens B}
  (c : OneCocycle A U) (α : κ → ι) (hV : ∀ a, V a ≤ U (α a))

theorem inclusionNat_refinementNat :
    inclusionNat c ≫ refinementNat c α hV = inclusionNat (refinedCocycle c α hV) := by
  apply NatTrans.ext
  funext W
  apply AddCommGrpCat.ext
  intro s
  exact sectionMap_inclusion c α hV W.unop s

theorem refinementNat_projectionNat :
    refinementNat c α hV ≫ projectionNat (refinedCocycle c α hV) = projectionNat c := by
  apply NatTrans.ext
  funext W
  apply AddCommGrpCat.ext
  intro s
  rfl

def extensionMiddleMap :
    (extensionComplex c).X₂ ⟶ (extensionComplex (refinedCocycle c α hV)).X₂ :=
  (sheafification (B := B)).map (refinementNat c α hV)

theorem extensionMiddleMap_inclusion :
    (extensionComplex c).f ≫ extensionMiddleMap c α hV =
      (extensionComplex (refinedCocycle c α hV)).f := by
  change ((originalSheafIso (A := A)).inv ≫
    (sheafification (B := B)).map (inclusionNat c)) ≫
      (sheafification (B := B)).map (refinementNat c α hV) =
    (originalSheafIso (A := A)).inv ≫
      (sheafification (B := B)).map (inclusionNat (refinedCocycle c α hV))
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, inclusionNat_refinementNat]

theorem extensionMiddleMap_projection :
    extensionMiddleMap c α hV ≫ (extensionComplex (refinedCocycle c α hV)).g =
      (extensionComplex c).g := by
  change (sheafification (B := B)).map (refinementNat c α hV) ≫
    (sheafification (B := B)).map (projectionNat (refinedCocycle c α hV)) =
    (sheafification (B := B)).map (projectionNat c)
  rw [← CategoryTheory.Functor.map_comp, refinementNat_projectionNat]

theorem cohomologyClass_refinement
    (hUcover : ∀ x : B, ∃ i, x ∈ U i) (hVcover : ∀ x : B, ∃ a, x ∈ V a) :
    cohomologyClass c hUcover = cohomologyClass (refinedCocycle c α hV) hVcover := by
  exact extClass_eq_of_middle_map
    (extensionComplex c).f (extensionComplex c).g (extensionComplex c).zero
    (extensionComplex (refinedCocycle c α hV)).f
    (extensionComplex (refinedCocycle c α hV)).g
    (extensionComplex (refinedCocycle c α hV)).zero
    (extensionComplex_shortExact c hUcover)
    (extensionComplex_shortExact (refinedCocycle c α hV) hVcover)
    (extensionMiddleMap c α hV) (extensionMiddleMap_inclusion c α hV)
    (extensionMiddleMap_projection c α hV)

end
end QuaternionicSymmetry.SheafCechCohomologyRefinement
