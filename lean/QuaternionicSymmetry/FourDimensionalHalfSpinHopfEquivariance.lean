import QuaternionicSymmetry.FourDimensionalHalfSpinHopfProjectiveDescent

/-! The normalized/projective Hopf map retains the literal quaternionic
conjugation action of the checked complex half-spin representation. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfEquivariance

open scoped Quaternion Matrix
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinQuaternionCoordinates
  FourDimensionalHalfSpinHopfRaw
  FourDimensionalHalfSpinHopfSphere
  FourDimensionalHalfSpinHopfNormalization
  FourDimensionalHalfSpinHopfProjectiveDescent
open QuaternionicUnitScalarIsometries

noncomputable section

theorem matrix_nonzero (q : unitary ℍ) (v : Spinor) (hv : v ≠ 0) :
    halfSpinLinearEquiv q v ≠ 0 := by
  simpa using (halfSpinLinearEquiv q).injective.ne hv

private theorem spinor_normSq_halfSpin (q : unitary ℍ) (v : Spinor) :
    Quaternion.normSq (fromSpinor (halfSpinLinearEquiv q v)) =
      Quaternion.normSq (fromSpinor v) := by
  rw [halfSpinLinearEquiv_apply, fromSpinor_halfSpinMatrix,
    map_mul, normSq_one_of_unitary, one_mul]

/-- The normalized Hopf quaternion is equivariant under the *actual*
local complex half-spin action, with explicit conjugation sign. -/
theorem hopfQuaternion_halfSpin (q : unitary ℍ) (v : Spinor) (hv : v ≠ 0) :
    hopfQuaternion (halfSpinLinearEquiv q v) (matrix_nonzero q v hv) =
      (q : ℍ) * hopfQuaternion v hv * star (q : ℍ) := by
  rw [hopfQuaternion_eq_ratio, spinor_normSq_halfSpin,
    hopfRaw_halfSpin, hopfQuaternion_eq_ratio]
  simp only [smul_mul_assoc, mul_smul_comm]

theorem hopfSphere_pureScalar_halfSpin (q : unitary ℍ)
    (v : Spinor) (hv : v ≠ 0) :
    QuaternionicUnitScalarIsometries.pureScalar
      (hopfSphere (halfSpinLinearEquiv q v) (matrix_nonzero q v hv)).1 =
      (q : ℍ) *
        QuaternionicUnitScalarIsometries.pureScalar (hopfSphere v hv).1 *
        star (q : ℍ) := by
  rw [pureScalar_hopfSphere, pureScalar_hopfSphere]
  exact hopfQuaternion_halfSpin q v hv

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfEquivariance
