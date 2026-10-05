import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveLocalAHS
import QuaternionicSymmetry.FourDimensionalHalfSpinHopfEquivariance
import QuaternionicSymmetry.FourDimensionalHalfSpinTwoSidedOrthogonal

/-! The Clifford-selected antipodal horizontal base complex structure
intertwines with the true two-sided quaternionic tangent transition and
the left half-spin action.  This fixes the chirality sign algebraically. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveChiralityOverlap

open scoped Quaternion Matrix
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinProjectiveLocalAHS
  FourDimensionalHalfSpinHopfSphere
  FourDimensionalHalfSpinHopfEquivariance
  FourDimensionalHalfSpinTwoSidedOrthogonal

noncomputable section

theorem antipodalBaseComplex_twoSided (q r : unitary ℍ)
    (v : Spinor) (hv : v ≠ 0) (x : ℍ) :
    antipodalBaseComplex (halfSpinLinearEquiv q v)
      (matrix_nonzero q v hv)
      ((q : ℍ) * x * star (r : ℍ)) =
      (q : ℍ) * (antipodalBaseComplex v hv x) * star (r : ℍ) := by
  change -(hopfQuaternion (halfSpinLinearEquiv q v)
      (matrix_nonzero q v hv) * ((q : ℍ) * x * star (r : ℍ))) =
    (q : ℍ) * (-(hopfQuaternion v hv * x)) * star (r : ℍ)
  rw [hopfQuaternion_halfSpin q v hv]
  calc
    -(((q : ℍ) * hopfQuaternion v hv * star (q : ℍ)) *
        ((q : ℍ) * x * star (r : ℍ))) =
      -((q : ℍ) * hopfQuaternion v hv *
        ((star (q : ℍ) * (q : ℍ)) * x) * star (r : ℍ)) := by
        simp only [mul_assoc]
    _ = (q : ℍ) * (-(hopfQuaternion v hv * x)) * star (r : ℍ) := by
      rw [q.property.1, one_mul]
      simp [mul_assoc]

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveChiralityOverlap
