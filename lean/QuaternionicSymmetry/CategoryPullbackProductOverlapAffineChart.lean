import QuaternionicSymmetry.CategoryPullbackProductOverlapIsoTransport

/-! Composite typed chart-restriction identity after identifying a
pairwise original-cover overlap with an affine object. -/

namespace QuaternionicSymmetry.CategoryPullbackProductOverlapAffineChart

open CategoryTheory CategoryTheory.Limits
open CategoryPullbackProductOverlapIso
open CategoryPullbackProductOverlapChartNaturality
open CategoryPullbackProductOverlapIsoTransport
noncomputable section

universe u
variable {C : Type u} [Category C] [HasPullbacks C]
variable {T X S U V B W : C}

instance overlapAffineBaseChange_isIso (f : T ⟶ S) (g : X ⟶ S)
    (u : U ⟶ X) (v : V ⟶ X) (e : pullback u v ≅ W) :
    IsIso (overlapAffineBaseChange f g u v e) := by
  dsimp [overlapAffineBaseChange]
  infer_instance

theorem affineOverlap_leftChart_natural
    (f : T ⟶ S) (g : X ⟶ S) (u : U ⟶ X) (v : V ⟶ X)
    (e : pullback u v ≅ W) (k : U ⟶ B) (b : B ⟶ S)
    (h : k ≫ b = u ≫ g)
    (β : W ⟶ B) (hβ : β = e.inv ≫ pullback.fst u v ≫ k) :
    (baseChangedOverlapIso f g u v ≪≫
        asIso (overlapAffineBaseChange f g u v e)).inv ≫
      pullback.fst (baseChangedOpenMap f g u) (baseChangedOpenMap f g v) ≫
      leftChartBaseChange f g u k b h =
    affineLeftChartBaseChange f g u v e k b h β hβ := by
  simp only [Iso.trans_inv, Category.assoc]
  rw [baseChangedOverlapIso_inv_leftChart_natural]
  rw [← overlapAffineBaseChange_left_natural f g u v e k b h β hβ]
  simp

theorem affineOverlap_rightChart_natural
    (f : T ⟶ S) (g : X ⟶ S) (u : U ⟶ X) (v : V ⟶ X)
    (e : pullback u v ≅ W) (k : V ⟶ B) (b : B ⟶ S)
    (h : k ≫ b = v ≫ g)
    (β : W ⟶ B) (hβ : β = e.inv ≫ pullback.snd u v ≫ k) :
    (baseChangedOverlapIso f g u v ≪≫
        asIso (overlapAffineBaseChange f g u v e)).inv ≫
      pullback.snd (baseChangedOpenMap f g u) (baseChangedOpenMap f g v) ≫
      rightChartBaseChange f g v k b h =
    affineRightChartBaseChange f g u v e k b h β hβ := by
  simp only [Iso.trans_inv, Category.assoc]
  rw [baseChangedOverlapIso_inv_rightChart_natural]
  rw [← overlapAffineBaseChange_right_natural f g u v e k b h β hβ]
  simp

end
end QuaternionicSymmetry.CategoryPullbackProductOverlapAffineChart
