import QuaternionicSymmetry.FourDimensionalHalfSpinHopfSurjective

/-! The local half-spin Hopf stabilizer is exactly the embedded complex
subalgebra of quaternions.  This is the explicit `U(1)` fiber calculation
needed for projective Hopf injectivity. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinComplexStabilizer

open scoped Quaternion
open FourDimensionalHalfSpinMatrix
open QuaternionicUnitQuaternionTransport

/-- A quaternion commuting with the selected imaginary `i` axis has no
`j,k` coordinates, hence is literally an embedded complex number. -/
theorem eq_complex_of_commutes_basisI (q : ℍ)
    (h : q * basisI = basisI * q) :
    q = (first q : ℍ) := by
  have hJ : q.imJ = 0 := by
    have he := congrArg (fun z : ℍ => z.imK) h
    simp [basisI, Quaternion.imK_mul] at he
    linarith
  have hK : q.imK = 0 := by
    have he := congrArg (fun z : ℍ => z.imJ) h
    simp [basisI, Quaternion.imJ_mul] at he
    linarith
  ext <;> simp [first, hJ, hK]

end QuaternionicSymmetry.FourDimensionalHalfSpinComplexStabilizer
