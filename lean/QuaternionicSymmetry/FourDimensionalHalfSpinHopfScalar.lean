import QuaternionicSymmetry.FourDimensionalHalfSpinHopfRaw

/-! The Hopf quadratic form has the exact complex-scaling law needed to
descend to the true projective spinor line; no projective quotient is
identified with a Hodge sphere by definition. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfScalar

open scoped Quaternion Matrix
open FourDimensionalHalfSpinMatrix FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinQuaternionCoordinates
open FourDimensionalHalfSpinHopfRaw

theorem fromSpinor_smul (c : ℂ) (v : Spinor) :
    fromSpinor (c • v) = fromSpinor v * (c : ℍ) := by
  ext <;>
    simp [fromSpinor, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul, Complex.mul_re,
      Complex.mul_im, smul_eq_mul] <;> ring

private theorem complex_commutes_basisI (c : ℂ) :
    (c : ℍ) * QuaternionicUnitQuaternionTransport.basisI =
      QuaternionicUnitQuaternionTransport.basisI * (c : ℍ) := by
  ext <;>
    simp [QuaternionicUnitQuaternionTransport.basisI,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul]

/-- Complex rescaling multiplies the Hopf quadratic form by its positive
real squared modulus.  Thus its normalized direction is projectively
well-defined. -/
theorem hopfRaw_smul (c : ℂ) (v : Spinor) :
    hopfRaw (c • v) = Complex.normSq c • hopfRaw v := by
  ext <;>
    simp [hopfRaw, fromSpinor, QuaternionicUnitQuaternionTransport.basisI,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul, Complex.normSq_apply, Complex.mul_re,
      Complex.mul_im, smul_eq_mul] <;> ring

end QuaternionicSymmetry.FourDimensionalHalfSpinHopfScalar
