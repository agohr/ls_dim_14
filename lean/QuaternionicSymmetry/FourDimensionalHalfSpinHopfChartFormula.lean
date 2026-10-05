import QuaternionicSymmetry.FourDimensionalHalfSpinHopfDiffeomorphPackage

/-! Literal affine `[1:z]` Hopf coordinates, certifying the orientation
and vertical-complex sign of the chosen quaternionic spinor convention. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfChartFormula

open scoped Quaternion
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinQuaternionCoordinates
  FourDimensionalHalfSpinHopfRaw
  FourDimensionalHalfSpinHopfNormalization
  FourDimensionalHalfSpinHopfSphere
open QuaternionicUnitQuaternionTransport

noncomputable section

def affineZeroSpinor (z : ℂ) : Spinor := ![(1 : ℂ), z]

theorem affineZero_raw (z : ℂ) :
    hopfRaw (affineZeroSpinor z) =
      ⟨0, 1 - Complex.normSq z, -2 * z.im, -2 * z.re⟩ := by
  ext <;>
    simp [hopfRaw, affineZeroSpinor, fromSpinor, basisI,
      Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul,
      Complex.normSq_apply] <;> ring

theorem affineZero_normSq (z : ℂ) :
    Quaternion.normSq (fromSpinor (affineZeroSpinor z)) =
      1 + Complex.normSq z := by
  simp [fromSpinor, affineZeroSpinor, Quaternion.normSq_def',
    Complex.normSq_apply, pow_two]
  ring

theorem affineZero_nonzero (z : ℂ) : affineZeroSpinor z ≠ 0 := by
  intro hz
  have h := congrFun hz 0
  norm_num [affineZeroSpinor] at h

theorem affineZero_hopfQuaternion (z : ℂ) :
    hopfQuaternion (affineZeroSpinor z) (affineZero_nonzero z) =
      (1 + Complex.normSq z)⁻¹ •
        (⟨0, 1 - Complex.normSq z, -2 * z.im, -2 * z.re⟩ : ℍ) := by
  rw [hopfQuaternion_eq_ratio, affineZero_normSq, affineZero_raw]

theorem affineZero_hopfCoefficients (z : ℂ) :
    (hopfSphere (affineZeroSpinor z) (affineZero_nonzero z)).1 =
      ![(1 + Complex.normSq z)⁻¹ * (1 - Complex.normSq z),
        (1 + Complex.normSq z)⁻¹ * (-2 * z.im),
        (1 + Complex.normSq z)⁻¹ * (-2 * z.re)] := by
  change ![(hopfQuaternion (affineZeroSpinor z) (affineZero_nonzero z)).imI,
      (hopfQuaternion (affineZeroSpinor z) (affineZero_nonzero z)).imJ,
      (hopfQuaternion (affineZeroSpinor z) (affineZero_nonzero z)).imK] = _
  rw [affineZero_hopfQuaternion]
  funext i
  fin_cases i <;> simp [smul_eq_mul]

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfChartFormula
