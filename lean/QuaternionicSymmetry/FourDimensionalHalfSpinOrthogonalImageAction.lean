import QuaternionicSymmetry.FourDimensionalHalfSpinTwoSidedProjectiveDescent

/-! An explicit projective half-spin action of the actual orthogonal image
of the two-sided quaternionic representation. A preimage pair is chosen
only to evaluate its checked complex matrix; independence of that pair is
the preceding kernel/sign theorem. Identifying this image with all `SO(4)`
remains separate. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinOrthogonalImageAction

open scoped Quaternion
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinTwoSidedOrthogonal
  FourDimensionalHalfSpinTwoSidedProjectiveDescent

noncomputable section

def orthogonalImage : Subgroup (ℍ ≃ₗᵢ[ℝ] ℍ) :=
  twoSidedHom.range

def imageLift (g : orthogonalImage) : unitary ℍ × unitary ℍ :=
  Classical.choose g.2

theorem imageLift_spec (g : orthogonalImage) :
    twoSidedHom (imageLift g) = g.1 :=
  Classical.choose_spec g.2

/-- Actual complex projective matrix action of an orthogonal image element. -/
def imageProjectiveAction (g : orthogonalImage)
    (p : ProjectiveSpinor) : ProjectiveSpinor :=
  projectiveHalfSpin (imageLift g).1 p

theorem imageProjectiveAction_lift (q r : unitary ℍ)
    (p : ProjectiveSpinor) :
    imageProjectiveAction
      (⟨twoSidedIsometry q r, ⟨(q,r), rfl⟩⟩ : orthogonalImage) p =
      projectiveHalfSpin q p := by
  unfold imageProjectiveAction
  have heq : twoSidedIsometry (imageLift
      (⟨twoSidedIsometry q r, ⟨(q,r), rfl⟩⟩ : orthogonalImage)).1
      (imageLift
      (⟨twoSidedIsometry q r, ⟨(q,r), rfl⟩⟩ : orthogonalImage)).2 =
      twoSidedIsometry q r := by
    exact imageLift_spec _
  exact congrFun (projectiveHalfSpin_eq_of_twoSided_eq _ _ _ _ heq) p

instance : MulAction orthogonalImage ProjectiveSpinor where
  smul := imageProjectiveAction
  one_smul p := by
    change imageProjectiveAction 1 p = p
    have hsame : twoSidedIsometry (imageLift (1 : orthogonalImage)).1
        (imageLift (1 : orthogonalImage)).2 = twoSidedIsometry 1 1 := by
      change twoSidedHom (imageLift (1 : orthogonalImage)) =
        twoSidedHom ((1 : unitary ℍ),(1 : unitary ℍ))
      rw [imageLift_spec]
      exact (map_one twoSidedHom).symm
    rw [show imageProjectiveAction (1 : orthogonalImage) p =
        projectiveHalfSpin (1 : unitary ℍ) p from
      congrFun (projectiveHalfSpin_eq_of_twoSided_eq _ _ _ _ hsame) p]
    rw [projectiveHalfSpin_one]
    rfl
  mul_smul g h p := by
    change imageProjectiveAction (g*h) p =
      imageProjectiveAction g (imageProjectiveAction h p)
    have hsame : twoSidedIsometry (imageLift (g*h)).1 (imageLift (g*h)).2 =
        twoSidedIsometry ((imageLift g).1 * (imageLift h).1)
          ((imageLift g).2 * (imageLift h).2) := by
      change twoSidedHom (imageLift (g*h)) =
        twoSidedHom (imageLift g * imageLift h)
      rw [imageLift_spec, map_mul, imageLift_spec, imageLift_spec]
      rfl
    unfold imageProjectiveAction
    rw [show projectiveHalfSpin (imageLift (g*h)).1 =
      projectiveHalfSpin ((imageLift g).1 * (imageLift h).1) from
        projectiveHalfSpin_eq_of_twoSided_eq _ _ _ _ hsame]
    rw [projectiveHalfSpin_mul]
    rfl

end
end QuaternionicSymmetry.FourDimensionalHalfSpinOrthogonalImageAction
