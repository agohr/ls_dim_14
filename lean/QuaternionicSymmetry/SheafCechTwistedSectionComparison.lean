import QuaternionicSymmetry.SheafCechTwistedSectionMaps
import QuaternionicSymmetry.SheafCechCocycleComparison

/-! On a fixed cover, an actual Čech coboundary comparison gives a
natural map of the constructed twisted-section presheaves, preserving the
coefficient inclusion and integer projection. -/

namespace QuaternionicSymmetry.SheafCechTwistedSectionComparison

open CategoryTheory TopologicalSpace Opposite SheafCechOneCocycle
open SheafCechCocycleComparison SheafCechTwistedSections
open SheafCechTwistedSectionMaps
noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type}
  {A : TopCat.Sheaf AddCommGrpCat (TopCat.of B)} {U : ι → Opens B}
  {c d : OneCocycle A U} (e : Comparison c d)

def sectionMap (V : Opens B) : sections c V →+ sections d V where
  toFun s := ⟨⟨s.1.1, fun i => s.1.2 i +
    s.1.1 • e.value i i (V ⊓ U i) inf_le_right inf_le_right⟩, by
    intro i j
    change (restrict A _).hom (_ + _) - (restrict A _).hom (_ + _) = _
    rw [map_add, map_add, map_zsmul, map_zsmul, e.naturality, e.naturality]
    let W := overlap (U := U) V i j
    have hi : W ≤ U i := inf_le_left.trans inf_le_right
    have hj : W ≤ U j := inf_le_right
    have hc := sections_compat c s i j
    have he := e.compatibility i j i j W hi hj hi hj
    have hd : c.value i j W hi hj +
        (e.value j j W hj hj - e.value i i W hi hi) = d.value i j W hi hj := by
      calc
        _ = (c.value i j W hi hj + e.value j j W hj hj) -
            e.value i i W hi hi := by abel
        _ = _ := by rw [he]; abel
    calc
      _ = (restrict A _ (s.1.2 j) - restrict A _ (s.1.2 i)) +
          s.1.1 • (e.value j j W hj hj - e.value i i W hi hi) := by
            rw [zsmul_sub]
            abel
      _ = _ := by rw [hc, ← smul_add, hd]⟩
  map_zero' := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext i
      change (0 : A.val.obj (op (V ⊓ U i))) + (0 : ℤ) • _ = 0
      rw [zero_zsmul, add_zero]
  map_add' s t := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext i
      change (s.1.2 i + t.1.2 i) + (s.1.1 + t.1.1) • _ = _
      rw [add_zsmul]
      change (s.1.2 i + t.1.2 i) + (_ + _) =
        (s.1.2 i + _) + (t.1.2 i + _)
      abel

theorem sectionMap_restrict {V W : Opens B} (hWV : W ≤ V) (s : sections c V) :
    restriction d hWV (sectionMap e V s) =
      sectionMap e W (restriction c hWV s) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · funext i
    change (restrict A _).hom (_ + _) = _
    rw [map_add, map_zsmul, e.naturality]
    rfl

theorem sectionMap_inclusion (V : Opens B) (s : A.val.obj (op V)) :
    sectionMap e V (inclusion c V s) = inclusion d V s := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · funext i
    change _ + (0 : ℤ) • _ = _
    rw [zero_zsmul, add_zero]
    rfl

theorem projection_sectionMap (V : Opens B) (s : sections c V) :
    projection d V (sectionMap e V s) = projection c V s := rfl

def comparisonNat : twistedPresheaf c ⟶ twistedPresheaf d where
  app V := AddCommGrpCat.ofHom (sectionMap e V.unop)
  naturality V W f := by
    apply AddCommGrpCat.ext
    intro s
    exact (sectionMap_restrict e f.unop.le s).symm

end
end QuaternionicSymmetry.SheafCechTwistedSectionComparison
