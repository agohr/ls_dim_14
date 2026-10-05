import QuaternionicSymmetry.CategoryPullbackProductOverlapIso

/-! Inverse projection formulas for the base-change overlap comparison. -/

namespace QuaternionicSymmetry.CategoryPullbackProductOverlapInverseProjections

open CategoryTheory CategoryTheory.Limits
open CategoryPullbackProductOverlapIso
noncomputable section

universe u
variable {C : Type u} [Category C] [HasPullbacks C]
variable {T X S U V : C}

theorem baseChangedOverlapIso_inv_left_base (f : T ⟶ S) (g : X ⟶ S)
    (u : U ⟶ X) (v : V ⟶ X) :
    (baseChangedOverlapIso f g u v).inv ≫
        pullback.fst (baseChangedOpenMap f g u) (baseChangedOpenMap f g v) ≫
        pullback.fst f (u ≫ g) =
      pullback.fst f (overlapToOriginal u v ≫ g) := by
  simp [baseChangedOverlapIso, baseChangeToProductOverlap]

theorem baseChangedOverlapIso_inv_left_chart (f : T ⟶ S) (g : X ⟶ S)
    (u : U ⟶ X) (v : V ⟶ X) :
    (baseChangedOverlapIso f g u v).inv ≫
        pullback.fst (baseChangedOpenMap f g u) (baseChangedOpenMap f g v) ≫
        pullback.snd f (u ≫ g) =
      pullback.snd f (overlapToOriginal u v ≫ g) ≫ pullback.fst u v := by
  simp [baseChangedOverlapIso, baseChangeToProductOverlap]

theorem baseChangedOverlapIso_inv_right_chart (f : T ⟶ S) (g : X ⟶ S)
    (u : U ⟶ X) (v : V ⟶ X) :
    (baseChangedOverlapIso f g u v).inv ≫
        pullback.snd (baseChangedOpenMap f g u) (baseChangedOpenMap f g v) ≫
        pullback.snd f (v ≫ g) =
      pullback.snd f (overlapToOriginal u v ≫ g) ≫ pullback.snd u v := by
  simp [baseChangedOverlapIso, baseChangeToProductOverlap]

end
end QuaternionicSymmetry.CategoryPullbackProductOverlapInverseProjections
