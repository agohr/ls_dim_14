import QuaternionicSymmetry.SheafCechTwistedSections

/-! The kernel inclusion, integer projection, and actual local integer
lifts in the twisted-section presheaf of a Čech one-cocycle. -/

namespace QuaternionicSymmetry.SheafCechTwistedSectionMaps

open CategoryTheory TopologicalSpace Opposite SheafCechOneCocycle
open SheafCechTwistedSections
noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type}
  {A : TopCat.Sheaf AddCommGrpCat (TopCat.of B)} {U : ι → Opens B}
  (c : OneCocycle A U)

def inclusion (V : Opens B) : A.val.obj (op V) →+ sections c V where
  toFun s := ⟨⟨0, fun i => restrict A (show V ⊓ U i ≤ V from inf_le_left) s⟩, by
    intro i j
    change restrict A _ (restrict A _ s) - restrict A _ (restrict A _ s) =
      (0 : ℤ) • _
    rw [restrict_restrict, restrict_restrict, zero_zsmul]
    exact sub_self _⟩
  map_zero' := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext i
      exact map_zero (restrict A _).hom
  map_add' s t := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext i
      exact map_add (restrict A _).hom _ _

def projection (V : Opens B) : sections c V →+ ℤ where
  toFun s := s.1.1
  map_zero' := rfl
  map_add' _ _ := rfl

theorem projection_inclusion (V : Opens B) (s : A.val.obj (op V)) :
    projection c V (inclusion c V s) = 0 := rfl

theorem inclusion_restrict {V W : Opens B} (hWV : W ≤ V)
    (s : A.val.obj (op V)) :
    restriction c hWV (inclusion c V s) = inclusion c W (restrict A hWV s) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · funext i
    change restrict A _ (restrict A _ s) = restrict A _ (restrict A _ s)
    rw [restrict_restrict, restrict_restrict]

theorem projection_restrict {V W : Opens B} (hWV : W ≤ V) (s : sections c V) :
    projection c W (restriction c hWV s) = projection c V s := rfl

/-- On an open contained in one cover member, every constant integer
has a genuine lift, using the supplied cocycle's actual sections. -/
def localLift (a : ι) (V : Opens B) (ha : V ≤ U a) : ℤ →+ sections c V where
  toFun n := ⟨⟨n, fun i => n • c.value a i (V ⊓ U i)
      (inf_le_left.trans ha) inf_le_right⟩, by
    intro i j
    change (restrict A _).hom (n • _) - (restrict A _).hom (n • _) = n • _
    rw [map_zsmul, map_zsmul, c.naturality, c.naturality, ← zsmul_sub]
    apply congrArg (fun x => n • x)
    have h := c.cocycle a i j (overlap (U := U) V i j)
      (inf_le_left.trans (inf_le_left.trans ha))
      (inf_le_left.trans inf_le_right) inf_le_right
    calc
      _ = (c.value a i (overlap (U := U) V i j) _ _ +
          c.value i j (overlap (U := U) V i j) _ _) -
          c.value a i (overlap (U := U) V i j) _ _ := by rw [h]
      _ = _ := by abel⟩
  map_zero' := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext i
      exact zero_zsmul _
  map_add' n m := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext i
      exact add_zsmul _ _ _

theorem projection_localLift (a : ι) (V : Opens B) (ha : V ≤ U a) (n : ℤ) :
    projection c V (localLift c a V ha n) = n := rfl

theorem localLift_restrict (a : ι) {V W : Opens B} (hWV : W ≤ V)
    (ha : V ≤ U a) (n : ℤ) :
    restriction c hWV (localLift c a V ha n) =
      localLift c a W (hWV.trans ha) n := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · funext i
    change (restrict A _).hom (n • _) = n • _
    rw [map_zsmul, c.naturality]

end
end QuaternionicSymmetry.SheafCechTwistedSectionMaps
