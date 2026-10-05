import QuaternionicSymmetry.CategoryPullbackProductOverlapChartNaturality

/-! Transport of the generic overlap chart restriction through an
isomorphism identifying the original overlap with an affine object. -/

namespace QuaternionicSymmetry.CategoryPullbackProductOverlapIsoTransport

open CategoryTheory CategoryTheory.Limits
open CategoryPullbackProductOverlapIso
open CategoryPullbackProductOverlapChartNaturality
noncomputable section

universe u
variable {C : Type u} [Category C] [HasPullbacks C]
variable {T X S U V B W : C}

def overlapAffineBaseChange (f : T ⟶ S) (g : X ⟶ S)
    (u : U ⟶ X) (v : V ⟶ X)
    (e : pullback u v ≅ W) :
    pullback f (overlapToOriginal u v ≫ g) ⟶
      pullback f (e.inv ≫ overlapToOriginal u v ≫ g) :=
  pullback.map f (overlapToOriginal u v ≫ g)
    f (e.inv ≫ overlapToOriginal u v ≫ g)
    (𝟙 _) e.hom (𝟙 _) (by simp) (by simp)

def affineLeftChartBaseChange (f : T ⟶ S) (g : X ⟶ S)
    (u : U ⟶ X) (v : V ⟶ X)
    (e : pullback u v ≅ W) (k : U ⟶ B) (b : B ⟶ S)
    (h : k ≫ b = u ≫ g)
    (β : W ⟶ B) (hβ : β = e.inv ≫ pullback.fst u v ≫ k) :
    pullback f (e.inv ≫ overlapToOriginal u v ≫ g) ⟶ pullback f b :=
  pullback.map f (e.inv ≫ overlapToOriginal u v ≫ g) f b
    (𝟙 _) β (𝟙 _) (by simp) (by
      rw [hβ]
      simpa only [overlapToOriginal, Category.assoc, Category.comp_id] using
        congrArg (fun q => e.inv ≫ pullback.fst u v ≫ q) h.symm)

theorem overlapAffineBaseChange_left_natural
    (f : T ⟶ S) (g : X ⟶ S) (u : U ⟶ X) (v : V ⟶ X)
    (e : pullback u v ≅ W) (k : U ⟶ B) (b : B ⟶ S)
    (h : k ≫ b = u ≫ g)
    (β : W ⟶ B) (hβ : β = e.inv ≫ pullback.fst u v ≫ k) :
    (overlapAffineBaseChange f g u v e) ≫
        affineLeftChartBaseChange f g u v e k b h β hβ =
      overlapLeftChartBaseChange f g u v k b h := by
  apply pullback.hom_ext
  · simp [overlapAffineBaseChange, affineLeftChartBaseChange,
      overlapLeftChartBaseChange, Category.assoc]
  · simp [overlapAffineBaseChange, affineLeftChartBaseChange,
      overlapLeftChartBaseChange, hβ, Category.assoc]

def affineRightChartBaseChange (f : T ⟶ S) (g : X ⟶ S)
    (u : U ⟶ X) (v : V ⟶ X)
    (e : pullback u v ≅ W) (k : V ⟶ B) (b : B ⟶ S)
    (h : k ≫ b = v ≫ g)
    (β : W ⟶ B) (hβ : β = e.inv ≫ pullback.snd u v ≫ k) :
    pullback f (e.inv ≫ overlapToOriginal u v ≫ g) ⟶ pullback f b :=
  pullback.map f (e.inv ≫ overlapToOriginal u v ≫ g) f b
    (𝟙 _) β (𝟙 _) (by simp) (by
      rw [hβ]
      calc
        (e.inv ≫ overlapToOriginal u v ≫ g) ≫ 𝟙 S =
            e.inv ≫ (pullback.fst u v ≫ u) ≫ g := by
              simp [overlapToOriginal, Category.assoc]
        _ = e.inv ≫ (pullback.snd u v ≫ v) ≫ g := by
              simpa only [Category.assoc] using congrArg
                (fun q => e.inv ≫ q ≫ g)
                (pullback.condition : pullback.fst u v ≫ u = pullback.snd u v ≫ v)
        _ = (e.inv ≫ pullback.snd u v ≫ k) ≫ b := by simp [h, Category.assoc])

theorem overlapAffineBaseChange_right_natural
    (f : T ⟶ S) (g : X ⟶ S) (u : U ⟶ X) (v : V ⟶ X)
    (e : pullback u v ≅ W) (k : V ⟶ B) (b : B ⟶ S)
    (h : k ≫ b = v ≫ g)
    (β : W ⟶ B) (hβ : β = e.inv ≫ pullback.snd u v ≫ k) :
    (overlapAffineBaseChange f g u v e) ≫
        affineRightChartBaseChange f g u v e k b h β hβ =
      overlapRightChartBaseChange f g u v k b h := by
  apply pullback.hom_ext
  · simp [overlapAffineBaseChange, affineRightChartBaseChange,
      overlapRightChartBaseChange, Category.assoc]
  · simp [overlapAffineBaseChange, affineRightChartBaseChange,
      overlapRightChartBaseChange, hβ, Category.assoc]

end
end QuaternionicSymmetry.CategoryPullbackProductOverlapIsoTransport
