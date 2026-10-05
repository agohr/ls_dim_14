import QuaternionicSymmetry.FourDimensionalHalfSpinHopfSphere

/-! Relate unit-quaternion normalization to the raw Hopf quadratic map.
This ratio formula is the algebraic bridge for genuine projective descent. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfNormalization

open scoped Quaternion
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinQuaternionCoordinates
  FourDimensionalHalfSpinHopfRaw
  FourDimensionalHalfSpinHopfSphere
open QuaternionicUnitQuaternionTransport

noncomputable section

theorem hopfQuaternion_eq_ratio (v : Spinor) (hv : v ≠ 0) :
    hopfQuaternion v hv =
      (Quaternion.normSq (fromSpinor v))⁻¹ • hopfRaw v := by
  let h := fromSpinor v
  have hh : h ≠ 0 := by
    intro hz
    apply hv
    apply fromSpinor_injective
    simpa [h, fromSpinor] using hz
  have hn : ‖h‖ ≠ 0 := norm_ne_zero_iff.mpr hh
  change ((normalize h hh : unitary ℍ) : ℍ) * basisI *
      star ((normalize h hh : unitary ℍ) : ℍ) =
    (Quaternion.normSq h)⁻¹ • (h * basisI * star h)
  rw [normalize_coe]
  simp only [smul_mul_assoc]
  rw [Quaternion.normSq_eq_norm_mul_self]
  simp [mul_inv_rev, smul_smul, mul_assoc]

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfNormalization
