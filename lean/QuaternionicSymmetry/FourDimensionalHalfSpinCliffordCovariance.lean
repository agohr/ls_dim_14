import QuaternionicSymmetry.FourDimensionalHalfSpinCliffordActual

/-! The literal quaternionic Clifford matrix is equivariant for both
unit-quaternion factors of the independently checked two-sided orthogonal
action. Thus its source spinor uses the left factor and its target spinor
uses the right factor, fixing the local chirality convention algebraically.
No global spin lift is assumed. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinCliffordCovariance

open scoped Quaternion Matrix
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinMatrix
  FourDimensionalHalfSpinQuaternionCoordinates
  FourDimensionalHalfSpinCliffordActual

noncomputable section

theorem cliffordMultiply_smul (x : ℍ) (c : ℂ) (v : Spinor) :
    cliffordMultiply x (c • v) = c • cliffordMultiply x v := by
  exact Matrix.mulVec_smul (halfSpinMatrix (star x)) c v

theorem cliffordMultiply_twoSided (q r : unitary ℍ)
    (x : ℍ) (v : Spinor) :
    cliffordMultiply ((q : ℍ) * x * star (r : ℍ))
        (halfSpinLinearEquiv q v) =
      halfSpinLinearEquiv r (cliffordMultiply x v) := by
  apply fromSpinor_injective
  simp only [halfSpinLinearEquiv_apply,
    fromSpinor_cliffordMultiply, fromSpinor_halfSpinMatrix]
  rw [star_mul, star_mul, star_star]
  calc
    ((r : ℍ) * (star x * star (q : ℍ))) *
        ((q : ℍ) * fromSpinor v) =
      (r : ℍ) * (star x * ((star (q : ℍ) * (q : ℍ)) * fromSpinor v)) := by
        simp only [mul_assoc]
    _ = (r : ℍ) * (star x * fromSpinor v) := by
      rw [q.property.1, one_mul]

end
end QuaternionicSymmetry.FourDimensionalHalfSpinCliffordCovariance
