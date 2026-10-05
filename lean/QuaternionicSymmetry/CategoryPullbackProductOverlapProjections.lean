import QuaternionicSymmetry.CategoryPullbackProductOverlapIso

/-! Projection formulas for the genuine base-change comparison of pairwise
open-cover overlaps. These identify both original chart restrictions on the
same product overlap and are the categorical inputs for scheme gluing. -/

namespace QuaternionicSymmetry.CategoryPullbackProductOverlapProjections

open CategoryTheory CategoryTheory.Limits
open CategoryPullbackProductOverlapIso
noncomputable section

universe u
variable {C : Type u} [Category C] [HasPullbacks C]
variable {T X S U V : C}

theorem baseChangedOverlapIso_hom_fst (f : T ⟶ S) (g : X ⟶ S)
    (u : U ⟶ X) (v : V ⟶ X) :
    (baseChangedOverlapIso f g u v).hom ≫
        pullback.fst f (overlapToOriginal u v ≫ g) =
      pullback.fst (baseChangedOpenMap f g u) (baseChangedOpenMap f g v) ≫
        pullback.fst f (u ≫ g) := by
  simp [baseChangedOverlapIso, productOverlapToBaseChange]

theorem baseChangedOverlapIso_hom_overlap_fst
    (f : T ⟶ S) (g : X ⟶ S) (u : U ⟶ X) (v : V ⟶ X) :
    (baseChangedOverlapIso f g u v).hom ≫
        pullback.snd f (overlapToOriginal u v ≫ g) ≫ pullback.fst u v =
      pullback.fst (baseChangedOpenMap f g u) (baseChangedOpenMap f g v) ≫
        pullback.snd f (u ≫ g) := by
  simp [baseChangedOverlapIso, productOverlapToBaseChange]

theorem baseChangedOverlapIso_hom_overlap_snd
    (f : T ⟶ S) (g : X ⟶ S) (u : U ⟶ X) (v : V ⟶ X) :
    (baseChangedOverlapIso f g u v).hom ≫
        pullback.snd f (overlapToOriginal u v ≫ g) ≫ pullback.snd u v =
      pullback.snd (baseChangedOpenMap f g u) (baseChangedOpenMap f g v) ≫
        pullback.snd f (v ≫ g) := by
  simp [baseChangedOverlapIso, productOverlapToBaseChange]

end
end QuaternionicSymmetry.CategoryPullbackProductOverlapProjections
