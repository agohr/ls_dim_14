import QuaternionicSymmetry.FourDimensionalHalfSpinQuaternionCoordinates
import QuaternionicSymmetry.QuaternionicUnitQuaternionTransport

/-! The unnormalized Hopf quadratic map of the actual local spinor
representation, with its literal quaternionic conjugation equivariance.
Projective descent and normalized negative-Hodge comparison remain separate. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfRaw

open scoped Quaternion Matrix
open FourDimensionalHalfSpinMatrix FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinQuaternionCoordinates
open QuaternionicUnitQuaternionTransport

/-- The quaternionic Hopf quadratic expression at a nonzero spinor.  The
selected axis `basisI` fixes the source's local complex convention. -/
def hopfRaw (v : Spinor) : ℍ :=
  fromSpinor v * basisI * star (fromSpinor v)

theorem hopfRaw_re (v : Spinor) : (hopfRaw v).re = 0 := by
  exact QuaternionicUnitScalarIsometries.conjugate_imaginary
    (fromSpinor v) basisI basisI_unit.1

/-- The complex half-spin matrix action rotates the Hopf direction by
quaternionic conjugation.  This is the actual algebraic sign convention. -/
theorem hopfRaw_halfSpin (q : unitary ℍ) (v : Spinor) :
    hopfRaw (halfSpinLinearEquiv q v) =
      (q : ℍ) * hopfRaw v * star (q : ℍ) := by
  rw [hopfRaw, hopfRaw, halfSpinLinearEquiv_apply,
    fromSpinor_halfSpinMatrix, star_mul]
  simp only [mul_assoc]

theorem hopfRaw_normSq (v : Spinor) :
    Quaternion.normSq (hopfRaw v) =
      Quaternion.normSq (fromSpinor v) ^ 2 := by
  simp [hopfRaw, map_mul, Quaternion.normSq_star, basisI_unit.2,
    pow_two, mul_assoc]

end QuaternionicSymmetry.FourDimensionalHalfSpinHopfRaw
