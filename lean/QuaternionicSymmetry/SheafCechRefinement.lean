import QuaternionicSymmetry.SheafCechTwistedSectionMaps

/-! Restrict a genuine cocycle to a refinement and construct the natural
map of its actual integer-twisted section presheaves. -/

namespace QuaternionicSymmetry.SheafCechRefinement

open CategoryTheory TopologicalSpace Opposite SheafCechOneCocycle
open SheafCechTwistedSections SheafCechTwistedSectionMaps
noncomputable section

variable {B : Type} [TopologicalSpace B] {ι κ : Type}
  {A : TopCat.Sheaf AddCommGrpCat (TopCat.of B)}
  {U : ι → Opens B} {V : κ → Opens B}
  (c : OneCocycle A U) (α : κ → ι) (hV : ∀ a, V a ≤ U (α a))

def refinedCocycle : OneCocycle A V where
  value a b W ha hb := c.value (α a) (α b) W (ha.trans (hV a)) (hb.trans (hV b))
  naturality a b W T hTW ha hb := c.naturality (α a) (α b) W T hTW _ _
  cocycle a b d W ha hb hd := c.cocycle (α a) (α b) (α d) W _ _ _

def sectionMap (W : Opens B) : sections c W →+ sections (refinedCocycle c α hV) W where
  toFun s := ⟨⟨s.1.1, fun a =>
    restrict A (inf_le_inf_left W (hV a)) (s.1.2 (α a))⟩, by
    intro a b
    let T := overlap (U := V) W a b
    have hT : T ≤ overlap (U := U) W (α a) (α b) :=
      le_inf (le_inf (inf_le_left.trans inf_le_left)
        (inf_le_left.trans (inf_le_right.trans (hV a))))
        (inf_le_right.trans (hV b))
    have h := congrArg (fun t => restrict A hT t) (sections_compat c s (α a) (α b))
    change (restrict A hT).hom (_ - _) = (restrict A hT).hom (_ • _) at h
    rw [map_sub, map_zsmul, c.naturality] at h
    change restrict A hT (restrict A _ (s.1.2 (α b))) -
      restrict A hT (restrict A _ (s.1.2 (α a))) = _ at h
    rw [restrict_restrict, restrict_restrict] at h
    change restrict A _ (restrict A _ (s.1.2 (α b))) -
      restrict A _ (restrict A _ (s.1.2 (α a))) = _
    rw [restrict_restrict, restrict_restrict]
    exact h⟩
  map_zero' := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext a
      exact map_zero (restrict A _).hom
  map_add' s t := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext a
      exact map_add (restrict A _).hom _ _

theorem sectionMap_restrict {W T : Opens B} (hTW : T ≤ W) (s : sections c W) :
    restriction (refinedCocycle c α hV) hTW (sectionMap c α hV W s) =
      sectionMap c α hV T (restriction c hTW s) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · funext a
    change restrict A _ (restrict A _ (s.1.2 (α a))) =
      restrict A _ (restrict A _ (s.1.2 (α a)))
    rw [restrict_restrict, restrict_restrict]

theorem sectionMap_inclusion (W : Opens B) (s : A.val.obj (op W)) :
    sectionMap c α hV W (inclusion c W s) =
      inclusion (refinedCocycle c α hV) W s := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · funext a
    exact restrict_restrict A _ _ s

theorem projection_sectionMap (W : Opens B) (s : sections c W) :
    projection (refinedCocycle c α hV) W (sectionMap c α hV W s) = projection c W s := rfl

def refinementNat : twistedPresheaf c ⟶ twistedPresheaf (refinedCocycle c α hV) where
  app W := AddCommGrpCat.ofHom (sectionMap c α hV W.unop)
  naturality W T f := by
    apply AddCommGrpCat.ext
    intro s
    exact (sectionMap_restrict c α hV f.unop.le s).symm

end
end QuaternionicSymmetry.SheafCechRefinement
