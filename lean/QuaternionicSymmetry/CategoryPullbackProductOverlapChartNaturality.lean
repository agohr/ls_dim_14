import QuaternionicSymmetry.CategoryPullbackProductOverlapInverseProjections

/-! A base-changed product-cover overlap restricts to the left chart by
the base change of its original-overlap restriction. This is the small
categorical square needed before affine tensor-product naturality. -/

namespace QuaternionicSymmetry.CategoryPullbackProductOverlapChartNaturality

open CategoryTheory CategoryTheory.Limits
open CategoryPullbackProductOverlapIso
open CategoryPullbackProductOverlapInverseProjections
noncomputable section

universe u
variable {C : Type u} [Category C] [HasPullbacks C]
variable {T X S U V B : C}

def leftChartBaseChange (f : T ⟶ S) (g : X ⟶ S)
    (u : U ⟶ X) (k : U ⟶ B) (b : B ⟶ S)
    (h : k ≫ b = u ≫ g) : pullback f (u ≫ g) ⟶ pullback f b :=
  pullback.map f (u ≫ g) f b (𝟙 _) k (𝟙 _) (by simp) (by simpa using h.symm)

def overlapLeftChartBaseChange (f : T ⟶ S) (g : X ⟶ S)
    (u : U ⟶ X) (v : V ⟶ X)
    (k : U ⟶ B) (b : B ⟶ S) (h : k ≫ b = u ≫ g) :
    pullback f (overlapToOriginal u v ≫ g) ⟶ pullback f b :=
  pullback.map f (overlapToOriginal u v ≫ g) f b
    (𝟙 _) (pullback.fst u v ≫ k) (𝟙 _) (by simp)
    (by simpa only [overlapToOriginal, Category.assoc, Category.comp_id] using
      congrArg (fun q => pullback.fst u v ≫ q) h.symm)

theorem baseChangedOverlapIso_inv_leftChart_natural
    (f : T ⟶ S) (g : X ⟶ S) (u : U ⟶ X) (v : V ⟶ X)
    (k : U ⟶ B) (b : B ⟶ S) (h : k ≫ b = u ≫ g) :
    (baseChangedOverlapIso f g u v).inv ≫
        pullback.fst (baseChangedOpenMap f g u) (baseChangedOpenMap f g v) ≫
        leftChartBaseChange f g u k b h =
      overlapLeftChartBaseChange f g u v k b h := by
  apply pullback.hom_ext
  · simp [leftChartBaseChange, overlapLeftChartBaseChange,
      baseChangedOverlapIso_inv_left_base, Category.assoc]
  · simpa only [leftChartBaseChange, overlapLeftChartBaseChange,
      Category.assoc, pullback.lift_snd, Category.id_comp] using
      congrArg (fun q => q ≫ k)
        (baseChangedOverlapIso_inv_left_chart f g u v)

def rightChartBaseChange (f : T ⟶ S) (g : X ⟶ S)
    (v : V ⟶ X) (k : V ⟶ B) (b : B ⟶ S)
    (h : k ≫ b = v ≫ g) : pullback f (v ≫ g) ⟶ pullback f b :=
  pullback.map f (v ≫ g) f b (𝟙 _) k (𝟙 _) (by simp) (by simpa using h.symm)

def overlapRightChartBaseChange (f : T ⟶ S) (g : X ⟶ S)
    (u : U ⟶ X) (v : V ⟶ X)
    (k : V ⟶ B) (b : B ⟶ S) (h : k ≫ b = v ≫ g) :
    pullback f (overlapToOriginal u v ≫ g) ⟶ pullback f b :=
  pullback.map f (overlapToOriginal u v ≫ g) f b
    (𝟙 _) (pullback.snd u v ≫ k) (𝟙 _) (by simp)
    (by
      calc
        (overlapToOriginal u v ≫ g) ≫ 𝟙 S =
            (pullback.fst u v ≫ u) ≫ g := by simp [overlapToOriginal]
        _ = (pullback.snd u v ≫ v) ≫ g := by
          simpa only [Category.assoc] using congrArg (fun q => q ≫ g)
            (pullback.condition : pullback.fst u v ≫ u = pullback.snd u v ≫ v)
        _ = (pullback.snd u v ≫ k) ≫ b := by simp [h, Category.assoc])

theorem baseChangedOverlapIso_inv_rightChart_natural
    (f : T ⟶ S) (g : X ⟶ S) (u : U ⟶ X) (v : V ⟶ X)
    (k : V ⟶ B) (b : B ⟶ S) (h : k ≫ b = v ≫ g) :
    (baseChangedOverlapIso f g u v).inv ≫
        pullback.snd (baseChangedOpenMap f g u) (baseChangedOpenMap f g v) ≫
        rightChartBaseChange f g v k b h =
      overlapRightChartBaseChange f g u v k b h := by
  apply pullback.hom_ext
  · simp [rightChartBaseChange, overlapRightChartBaseChange,
      baseChangedOverlapIso, baseChangeToProductOverlap, Category.assoc]
  · simpa only [rightChartBaseChange, overlapRightChartBaseChange,
      Category.assoc, pullback.lift_snd, Category.id_comp] using
      congrArg (fun q => q ≫ k)
        (baseChangedOverlapIso_inv_right_chart f g u v)

end
end QuaternionicSymmetry.CategoryPullbackProductOverlapChartNaturality
