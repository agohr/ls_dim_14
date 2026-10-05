import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-! Changing the displayed structural arrow of a pullback by a proved
equality does not change its induced second-factor map. This isolates the
`Spec ℂ` equality cast in the actual product-overlap calculation. -/

namespace QuaternionicSymmetry.CategoryPullbackSecondFactorStructureTransport

open CategoryTheory CategoryTheory.Limits
noncomputable section

universe u
variable {C : Type u} [Category C] [HasPullbacks C]
variable {T S W B : C}

def secondFactorMap (f : T ⟶ S) (w : W ⟶ S)
    (b : B ⟶ S) (β : W ⟶ B) (h : β ≫ b = w) :
    pullback f w ⟶ pullback f b :=
  pullback.map f w f b (𝟙 _) β (𝟙 _) (by simp) (by simpa using h.symm)

theorem secondFactorMap_structureTransport (f : T ⟶ S)
    (w w' : W ⟶ S) (hw : w = w')
    (b : B ⟶ S) (β : W ⟶ B) (h : β ≫ b = w) :
    (pullback.congrHom rfl hw).hom ≫
        secondFactorMap f w' b β (h.trans hw) =
      secondFactorMap f w b β h := by
  apply pullback.hom_ext
  · simp [secondFactorMap, pullback.congrHom, Category.assoc]
  · simp [secondFactorMap, pullback.congrHom, Category.assoc]

end
end QuaternionicSymmetry.CategoryPullbackSecondFactorStructureTransport
