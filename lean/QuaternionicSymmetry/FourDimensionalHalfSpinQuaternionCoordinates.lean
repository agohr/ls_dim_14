import QuaternionicSymmetry.FourDimensionalHalfSpinProjective

/-! The checked local half-spin matrix is literally left multiplication on
quaternions when the latter are written as `z₀ + j z₁`.  This coordinate
intertwiner is needed for the projective Hopf map and its sign/orientation. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinQuaternionCoordinates

open scoped Quaternion Matrix
open FourDimensionalHalfSpinMatrix FourDimensionalHalfSpinProjective

/-- Recover a quaternion from the two complex half-spin coordinates. -/
def fromSpinor (v : Spinor) : ℍ :=
  ⟨(v 0).re, (v 0).im, (v 1).re, -(v 1).im⟩

@[simp] theorem first_fromSpinor (v : Spinor) :
    first (fromSpinor v) = v 0 := by
  apply Complex.ext <;> rfl

@[simp] theorem second_fromSpinor (v : Spinor) :
    second (fromSpinor v) = v 1 := by
  apply Complex.ext <;> simp [second, fromSpinor]

theorem fromSpinor_injective : Function.Injective fromSpinor := by
  intro v w h
  funext i
  fin_cases i
  · exact (first_fromSpinor v).symm.trans
      ((congrArg first h).trans (first_fromSpinor w))
  · exact (second_fromSpinor v).symm.trans
      ((congrArg second h).trans (second_fromSpinor w))

theorem fromSpinor_surjective : Function.Surjective fromSpinor := by
  intro q
  refine ⟨![first q, second q], ?_⟩
  ext <;> simp [fromSpinor, first, second]

/-- Real-linear coordinate equivalence underlying the local spinor model. -/
def spinorQuaternionEquiv : Spinor ≃ₗ[ℝ] ℍ where
  toFun := fromSpinor
  invFun q := ![first q,second q]
  left_inv v := by
    funext i
    fin_cases i <;> simp
  right_inv q := by
    ext <;> simp [fromSpinor, first, second]
  map_add' v w := by
    ext <;> simp [fromSpinor] <;> abel
  map_smul' r v := by
    ext <;> simp [fromSpinor, smul_eq_mul]

private theorem matrix_apply_zero (q : ℍ) (v : Spinor) :
    (halfSpinMatrix q *ᵥ v) 0 =
      first q * v 0 - star (second q) * v 1 := by
  simp [halfSpinMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  abel

private theorem matrix_apply_one (q : ℍ) (v : Spinor) :
    (halfSpinMatrix q *ᵥ v) 1 =
      second q * v 0 + star (first q) * v 1 := by
  simp [halfSpinMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Quaternion multiplication is exactly the checked complex half-spin
matrix action, including its `j,k` sign convention. -/
theorem fromSpinor_halfSpinMatrix (q : ℍ) (v : Spinor) :
    fromSpinor (halfSpinMatrix q *ᵥ v) = q * fromSpinor v := by
  apply (spinorQuaternionEquiv.symm).injective
  funext i
  fin_cases i
  · change first (fromSpinor (halfSpinMatrix q *ᵥ v)) =
      first (q * fromSpinor v)
    rw [first_fromSpinor, matrix_apply_zero, first_mul,
      first_fromSpinor, second_fromSpinor]
  · change second (fromSpinor (halfSpinMatrix q *ᵥ v)) =
      second (q * fromSpinor v)
    rw [second_fromSpinor, matrix_apply_one, second_mul,
      first_fromSpinor, second_fromSpinor]

end QuaternionicSymmetry.FourDimensionalHalfSpinQuaternionCoordinates
