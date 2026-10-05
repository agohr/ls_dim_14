import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondTensor
import QuaternionicSymmetry.FourDimensionalHalfSpinHopfProjectiveDescent

/-! The two affine spinor representatives `[1:z]` and `[z⁻¹:1]` have
literally equal normalized Hopf coefficients on the chart overlap. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondHopf

open scoped Quaternion Matrix
open FourDimensionalHalfSpinHopfProjectiveDescent
  FourDimensionalHalfSpinHopfSphere
  FourDimensionalHalfSpinProjective

noncomputable section

theorem invertedSpinor_eq_smul (z : ℂ) (hz : z ≠ 0) :
    (![z⁻¹,1] : Spinor) = z⁻¹ • ![1,z] := by
  funext i
  fin_cases i
  · simp
  · simp [smul_eq_mul, inv_mul_cancel₀ hz]

theorem hopfSphere_inversion (z : ℂ) (hz : z ≠ 0) :
    hopfSphere ![z⁻¹,1] (by simp) =
      hopfSphere ![1,z] (by simp) := by
  calc
    hopfSphere ![z⁻¹,1] (by simp) =
        hopfSphere (z⁻¹ • ![1,z])
          (smul_ne_zero (inv_ne_zero hz) (by simp)) := by
            congr 1
            exact invertedSpinor_eq_smul z hz
    _ = hopfSphere ![1,z] (by simp) :=
      hopfSphere_smul z⁻¹ (inv_ne_zero hz) ![1,z] (by simp)

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondHopf
