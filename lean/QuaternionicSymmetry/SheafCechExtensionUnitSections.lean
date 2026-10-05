import QuaternionicSymmetry.SheafCechExtension
import QuaternionicSymmetry.IntegralSheafLocalUnitLift

/-! Canonical local unit lifts in the actual sheafified extension of a
Čech cocycle. Their differences are the original coefficient sections,
with the literal kernel inclusion and quotient map. -/

namespace QuaternionicSymmetry.SheafCechExtensionUnitSections

open CategoryTheory TopologicalSpace Opposite
open AbelianSheafCohomology SheafCechOneCocycle SheafCechExtension
open SheafCechTwistedSections SheafCechTwistedSectionMaps
open SheafCechTwistedPresheafSequence IntegralSheafLocalUnitLift
noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type}
  {A : TopCat.Sheaf AddCommGrpCat (TopCat.of B)} {U : ι → Opens B}
  (c : OneCocycle A U)

theorem originalSheafIso_inv_val : (originalSheafIso (A := A)).inv.val =
    toSheafify (Opens.grothendieckTopology (TopCat.of B)) A.val := by
  let J := Opens.grothendieckTopology (TopCat.of B)
  have hleft : (originalSheafIso (A := A)).inv.val ≫
      (originalSheafIso (A := A)).hom.val = 𝟙 A.val :=
    congrArg (fun f => f.val) (originalSheafIso (A := A)).inv_hom_id
  have hright : toSheafify J A.val ≫
      (originalSheafIso (A := A)).hom.val = 𝟙 A.val :=
    (sheafificationAdjunction J AddCommGrpCat).right_triangle_components A
  exact (cancel_mono (originalSheafIso (A := A)).hom.val).mp (hleft.trans hright.symm)

abbrev toExtension : twistedPresheaf c ⟶ (extensionComplex c).X₂.val :=
  toSheafify (Opens.grothendieckTopology (TopCat.of B)) (twistedPresheaf c)

theorem inclusion_toExtension : inclusionNat c ≫ toExtension c =
    (extensionComplex c).f.val := by
  change inclusionNat c ≫ toExtension c =
    (originalSheafIso (A := A)).inv.val ≫
      ((sheafification (B := B)).map (inclusionNat c)).val
  rw [originalSheafIso_inv_val]
  exact toSheafify_naturality (Opens.grothendieckTopology (TopCat.of B)) (inclusionNat c)

theorem toExtension_projection : toExtension c ≫ (extensionComplex c).g.val =
    projectionNat c ≫ toSheafify (Opens.grothendieckTopology (TopCat.of B))
      (constantIntegerPresheaf (B := B)) :=
  (toSheafify_naturality (Opens.grothendieckTopology (TopCat.of B)) (projectionNat c)).symm

def unitLift (i : ι) (V : Opens B) (hi : V ≤ U i) :
    (extensionComplex c).X₂.val.obj (op V) :=
  (toExtension c).app (op V) (localLift c i V hi 1)

theorem unitLift_restrict (i : ι) {V W : Opens B} (hWV : W ≤ V) (hi : V ≤ U i) :
    restrict (extensionComplex c).X₂ hWV (unitLift c i V hi) =
      unitLift c i W (hWV.trans hi) := by
  have h := congrArg (fun k => k (localLift c i V hi 1))
    ((toExtension c).naturality (homOfLE hWV).op)
  change (toExtension c).app (op W) (restriction c hWV (localLift c i V hi 1)) =
    restrict (extensionComplex c).X₂ hWV (unitLift c i V hi) at h
  rw [localLift_restrict] at h
  exact h.symm

theorem unitLift_projection (i : ι) (V : Opens B) (hi : V ≤ U i) :
    (extensionComplex c).g.val.app (op V) (unitLift c i V hi) = unitSection V :=
  congrArg (fun k => k.app (op V) (localLift c i V hi 1)) (toExtension_projection c)

theorem localLift_one_sub (i j : ι) (V : Opens B) (hi : V ≤ U i) (hj : V ≤ U j) :
    localLift c i V hi 1 - localLift c j V hj 1 = inclusion c V (c.value i j V hi hj) := by
  apply Subtype.ext
  apply Prod.ext
  · change (1 : ℤ) - 1 = 0
    exact sub_self _
  · funext k
    change (1 : ℤ) • c.value i k (V ⊓ U k) _ _ -
      (1 : ℤ) • c.value j k (V ⊓ U k) _ _ =
      restrict A inf_le_left (c.value i j V hi hj)
    rw [one_zsmul, one_zsmul, c.naturality]
    have h := c.cocycle i j k (V ⊓ U k) (inf_le_left.trans hi)
      (inf_le_left.trans hj) inf_le_right
    rw [← h]
    abel

theorem unitLift_sub (i j : ι) (V : Opens B) (hi : V ≤ U i) (hj : V ≤ U j) :
    unitLift c i V hi - unitLift c j V hj =
      (extensionComplex c).f.val.app (op V) (c.value i j V hi hj) := by
  change ((toExtension c).app (op V)).hom (localLift c i V hi 1) -
    ((toExtension c).app (op V)).hom (localLift c j V hj 1) = _
  rw [← map_sub, localLift_one_sub]
  exact congrArg (fun k => k.app (op V) (c.value i j V hi hj)) (inclusion_toExtension c)

end
end QuaternionicSymmetry.SheafCechExtensionUnitSections
