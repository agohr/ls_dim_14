import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-! A base-changed cover's pairwise intersection is the base change of
the original pairwise intersection. This is the categorical comparison
needed to read scheme product-cover overlaps as affine tensor products. -/

namespace QuaternionicSymmetry.CategoryPullbackProductOverlapIso

open CategoryTheory CategoryTheory.Limits
noncomputable section

universe u
variable {C : Type u} [Category C] [HasPullbacks C]
variable {T X S U V : C}

def baseChangedOpenMap (f : T ⟶ S) (g : X ⟶ S) (u : U ⟶ X) :
    pullback f (u ≫ g) ⟶ pullback f g :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ u) (by
    simpa only [Category.assoc] using (pullback.condition :
      pullback.fst f (u ≫ g) ≫ f = pullback.snd f (u ≫ g) ≫ (u ≫ g)))

def overlapToOriginal (u : U ⟶ X) (v : V ⟶ X) :
    pullback u v ⟶ X := pullback.fst u v ≫ u

def productOverlapToBaseChange (f : T ⟶ S) (g : X ⟶ S)
    (u : U ⟶ X) (v : V ⟶ X) :
    pullback (baseChangedOpenMap f g u) (baseChangedOpenMap f g v) ⟶
      pullback f (overlapToOriginal u v ≫ g) := by
  let P := pullback (baseChangedOpenMap f g u) (baseChangedOpenMap f g v)
  let t : P ⟶ T := pullback.fst _ _ ≫ pullback.fst f (u ≫ g)
  let uv : P ⟶ pullback u v := pullback.lift
    (pullback.fst _ _ ≫ pullback.snd f (u ≫ g))
    (pullback.snd _ _ ≫ pullback.snd f (v ≫ g)) (by
      have h : pullback.fst (baseChangedOpenMap f g u)
          (baseChangedOpenMap f g v) ≫ baseChangedOpenMap f g u =
        pullback.snd (baseChangedOpenMap f g u)
          (baseChangedOpenMap f g v) ≫ baseChangedOpenMap f g v :=
        pullback.condition
      simpa only [baseChangedOpenMap, pullback.lift_snd, Category.assoc] using
        congrArg (fun q => q ≫ pullback.snd f g) h)
  exact pullback.lift t uv (by
    simp only [t, uv, overlapToOriginal, ← Category.assoc, pullback.lift_fst]
    simpa only [Category.assoc] using congrArg
      (fun q => pullback.fst (baseChangedOpenMap f g u)
        (baseChangedOpenMap f g v) ≫ q)
      (pullback.condition :
        pullback.fst f (u ≫ g) ≫ f = pullback.snd f (u ≫ g) ≫ (u ≫ g)))

def baseChangeToProductOverlap (f : T ⟶ S) (g : X ⟶ S)
    (u : U ⟶ X) (v : V ⟶ X) :
    pullback f (overlapToOriginal u v ≫ g) ⟶
      pullback (baseChangedOpenMap f g u) (baseChangedOpenMap f g v) := by
  let Q := pullback f (overlapToOriginal u v ≫ g)
  let pu : Q ⟶ pullback f (u ≫ g) := pullback.lift
    (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.fst u v) (by
      simpa only [overlapToOriginal, Category.assoc] using
        (pullback.condition : pullback.fst f (overlapToOriginal u v ≫ g) ≫ f =
          pullback.snd f (overlapToOriginal u v ≫ g) ≫
            (overlapToOriginal u v ≫ g)))
  let pv : Q ⟶ pullback f (v ≫ g) := pullback.lift
    (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd u v) (by
      calc
        pullback.fst f (overlapToOriginal u v ≫ g) ≫ f =
            pullback.snd f (overlapToOriginal u v ≫ g) ≫
              (pullback.fst u v ≫ u) ≫ g := by
                simpa only [overlapToOriginal, Category.assoc] using
                  (pullback.condition : pullback.fst f (overlapToOriginal u v ≫ g) ≫ f =
                    pullback.snd f (overlapToOriginal u v ≫ g) ≫
                      (overlapToOriginal u v ≫ g))
        _ = pullback.snd f (overlapToOriginal u v ≫ g) ≫
              (pullback.snd u v ≫ v) ≫ g := by
                simpa only [Category.assoc] using congrArg
                  (fun q => pullback.snd f (overlapToOriginal u v ≫ g) ≫ q ≫ g)
                  (pullback.condition : pullback.fst u v ≫ u = pullback.snd u v ≫ v)
        _ = _ := by simp [Category.assoc])
  exact pullback.lift pu pv (by
    apply pullback.hom_ext
    · simp [pu, pv, baseChangedOpenMap]
    · simp only [pu, pv, baseChangedOpenMap]
      simp only [Category.assoc]
      simp only [pullback.lift_snd]
      simp only [← Category.assoc, pullback.lift_snd]
      simpa only [Category.assoc] using congrArg
        (fun q => pullback.snd f (overlapToOriginal u v ≫ g) ≫ q)
        (pullback.condition : pullback.fst u v ≫ u = pullback.snd u v ≫ v))

def baseChangedOverlapIso (f : T ⟶ S) (g : X ⟶ S)
    (u : U ⟶ X) (v : V ⟶ X) :
    pullback (baseChangedOpenMap f g u) (baseChangedOpenMap f g v) ≅
      pullback f (overlapToOriginal u v ≫ g) where
  hom := productOverlapToBaseChange f g u v
  inv := baseChangeToProductOverlap f g u v
  hom_inv_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp [productOverlapToBaseChange, baseChangeToProductOverlap,
          baseChangedOpenMap, Category.assoc]
      · simp [productOverlapToBaseChange, baseChangeToProductOverlap,
          baseChangedOpenMap, Category.assoc]
    · apply pullback.hom_ext
      · have h : pullback.fst (baseChangedOpenMap f g u)
            (baseChangedOpenMap f g v) ≫ baseChangedOpenMap f g u =
          pullback.snd (baseChangedOpenMap f g u)
            (baseChangedOpenMap f g v) ≫ baseChangedOpenMap f g v :=
          pullback.condition
        simpa [productOverlapToBaseChange, baseChangeToProductOverlap,
          baseChangedOpenMap, Category.assoc] using
          congrArg (fun q => q ≫ pullback.fst f g) h
      · simp [productOverlapToBaseChange, baseChangeToProductOverlap,
          baseChangedOpenMap, Category.assoc]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp [productOverlapToBaseChange, baseChangeToProductOverlap,
        baseChangedOpenMap, Category.assoc]
    · apply pullback.hom_ext
      · simp [productOverlapToBaseChange, baseChangeToProductOverlap,
          baseChangedOpenMap, Category.assoc]
      · simp [productOverlapToBaseChange, baseChangeToProductOverlap,
          baseChangedOpenMap, Category.assoc]

end
end QuaternionicSymmetry.CategoryPullbackProductOverlapIso
