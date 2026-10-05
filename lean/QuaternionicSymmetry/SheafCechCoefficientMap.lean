import QuaternionicSymmetry.SheafCechTwistedPresheafSequence
import QuaternionicSymmetry.SheafShortExactSections

/-! Actual coefficient morphisms carry sheaf cocycles and their twisted
sections naturally, keeping the integer quotient unchanged. -/

namespace QuaternionicSymmetry.SheafCechCoefficientMap

open CategoryTheory TopologicalSpace Opposite
open AbelianSheafCohomology SheafCechOneCocycle SheafShortExactSections
open SheafCechTwistedSections SheafCechTwistedSectionMaps SheafCechTwistedPresheafSequence
noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type}
  {A D : AbelianSheaves B} (f : A ⟶ D) {U : ι → Opens B} (c : OneCocycle A U)

def mappedCocycle : OneCocycle D U where
  value i j V hi hj := f.val.app (op V) (c.value i j V hi hj)
  naturality i j V W hWV hi hj := by
    rw [← map_restrict, c.naturality]
  cocycle i j k V hi hj hk := by
    change (f.val.app (op V)).hom _ + (f.val.app (op V)).hom _ = _
    rw [← map_add, c.cocycle]

def sectionMap (V : Opens B) :
    SheafCechTwistedSections.sections c V →+
      SheafCechTwistedSections.sections (mappedCocycle f c) V where
  toFun s := ⟨⟨s.1.1, fun i => f.val.app (op (V ⊓ U i)) (s.1.2 i)⟩, by
    intro i j
    change restrict D _ (f.val.app _ _) - restrict D _ (f.val.app _ _) = _
    rw [← map_restrict, ← map_restrict]
    change (f.val.app _).hom _ - (f.val.app _).hom _ = s.1.1 • (f.val.app _).hom _
    rw [← map_sub, ← map_zsmul]
    exact congrArg (fun a => f.val.app _ a) (sections_compat c s i j)⟩
  map_zero' := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext i
      exact map_zero (f.val.app _).hom
  map_add' s t := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext i
      exact map_add (f.val.app _).hom _ _

theorem sectionMap_restrict {V W : Opens B} (hWV : W ≤ V)
    (s : SheafCechTwistedSections.sections c V) :
    restriction (mappedCocycle f c) hWV (sectionMap f c V s) =
      sectionMap f c W (restriction c hWV s) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · funext i
    exact (map_restrict f (inf_le_inf_right (U i) hWV) (s.1.2 i)).symm

theorem sectionMap_inclusion (V : Opens B) (a : A.val.obj (op V)) :
    sectionMap f c V (inclusion c V a) =
      inclusion (mappedCocycle f c) V (f.val.app (op V) a) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · funext i
    exact map_restrict f inf_le_left a

def coefficientNat : twistedPresheaf c ⟶ twistedPresheaf (mappedCocycle f c) where
  app V := AddCommGrpCat.ofHom (sectionMap f c V.unop)
  naturality V W k := by
    apply AddCommGrpCat.ext
    intro s
    exact (sectionMap_restrict f c k.unop.le s).symm

theorem inclusionNat_coefficientNat :
    inclusionNat c ≫ coefficientNat f c = f.val ≫ inclusionNat (mappedCocycle f c) := by
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.ext
  intro a
  exact sectionMap_inclusion f c V.unop a

theorem coefficientNat_projectionNat :
    coefficientNat f c ≫ projectionNat (mappedCocycle f c) = projectionNat c := by
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.ext
  intro s
  rfl

end
end QuaternionicSymmetry.SheafCechCoefficientMap
