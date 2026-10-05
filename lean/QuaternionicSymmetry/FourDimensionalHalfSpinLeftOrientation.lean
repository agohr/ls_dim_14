import QuaternionicSymmetry.FourDimensionalHalfSpinRightOrientation

/-! Left unit-quaternion multiplication is conjugate, by the real-linear
quaternionic involution, to right unit-quaternion multiplication. The
checked determinant-conjugation identity transfers the positive
orientation sign without a second four-by-four calculation. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinLeftOrientation

open scoped Quaternion
open FourDimensionalHalfSpinTwoSidedOrthogonal
  FourDimensionalHalfSpinRightOrientation
  QuaternionicProjectiveStandardHilbertStructure

noncomputable section

def quaternionStarEquiv : ℍ ≃ₗ[ℝ] ℍ where
  toFun := star
  invFun := star
  map_add' a b := by simp
  map_smul' r a := by simp [Quaternion.star_smul]
  left_inv a := star_star a
  right_inv a := star_star a

theorem left_eq_star_right_star (q : unitary ℍ) :
    (leftUnitIsometry q).toLinearEquiv =
      (quaternionStarEquiv.symm.trans
        (rightUnitIsometry q).toLinearEquiv).trans quaternionStarEquiv := by
  apply LinearEquiv.ext
  intro w
  change (q : ℍ) * w = star (star w * star (q : ℍ))
  rw [star_mul, star_star, star_star]

theorem leftUnitIsometry_det_pos (q : unitary ℍ) :
    0 < LinearMap.det (leftUnitIsometry q : ℍ →ₗ[ℝ] ℍ) := by
  have hdet := LinearEquiv.det_conj
    (rightUnitIsometry q).toLinearEquiv quaternionStarEquiv
  rw [← left_eq_star_right_star q] at hdet
  have heq := congrArg Units.val hdet
  simpa only [LinearEquiv.coe_det] using
    (show 0 < (LinearEquiv.det (leftUnitIsometry q).toLinearEquiv : ℝ) from by
      rw [heq]
      simpa only [LinearEquiv.coe_det] using rightUnitIsometry_det_pos q)

end
end QuaternionicSymmetry.FourDimensionalHalfSpinLeftOrientation
