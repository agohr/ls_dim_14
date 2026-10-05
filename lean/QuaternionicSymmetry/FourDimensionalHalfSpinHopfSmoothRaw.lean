import QuaternionicSymmetry.FourDimensionalHalfSpinHopfContinuous

/-! The normalized Hopf formula is genuinely real-smooth in ambient spinor
coordinates away from the zero vector. This is independent of projective
descent and of any transported smooth structure on the target sphere. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfSmoothRaw

open scoped Quaternion ContDiff
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinQuaternionCoordinates
  FourDimensionalHalfSpinHopfRaw
  FourDimensionalHalfSpinHopfNormalization

noncomputable section

private theorem contDiff_fromSpinor :
    ContDiff ℝ ∞ (fromSpinor : Spinor → ℍ) :=
  spinorQuaternionEquiv.toLinearMap.toContinuousLinearMap.contDiff

private def starLinear : ℍ →ₗ[ℝ] ℍ where
  toFun := star
  map_add' a b := by simp
  map_smul' r a := by simp [Quaternion.star_smul]

private theorem contDiff_star : ContDiff ℝ ∞ (star : ℍ → ℍ) :=
  starLinear.toContinuousLinearMap.contDiff

theorem contDiff_hopfRaw : ContDiff ℝ ∞ hopfRaw := by
  unfold hopfRaw
  exact (contDiff_fromSpinor.mul contDiff_const).mul
    (contDiff_star.comp contDiff_fromSpinor)

theorem contDiffAt_hopfQuaternion (v : Spinor) (hv : v ≠ 0) :
    ContDiffAt ℝ ∞
      (fun w : Spinor =>
        (Quaternion.normSq (fromSpinor w))⁻¹ • hopfRaw w) v := by
  have hq : ContDiffAt ℝ ∞ (fromSpinor : Spinor → ℍ) v :=
    contDiff_fromSpinor.contDiffAt
  have hnz : fromSpinor v ≠ 0 := by
    intro hz
    apply hv
    apply fromSpinor_injective
    simpa [fromSpinor] using hz
  have hnorm : ContDiffAt ℝ ∞
      (fun w : Spinor => ‖fromSpinor w‖) v :=
    (contDiffAt_norm ℝ hnz).comp v hq
  have hnormSq : ContDiffAt ℝ ∞
      (fun w : Spinor => Quaternion.normSq (fromSpinor w)) v := by
    convert hnorm.pow 2 using 1
    funext w
    exact (Quaternion.normSq_eq_norm_mul_self (fromSpinor w)).trans (by ring)
  have hn : Quaternion.normSq (fromSpinor v) ≠ 0 :=
    (Quaternion.normSq_ne_zero).mpr hnz
  exact (hnormSq.inv hn).smul contDiff_hopfRaw.contDiffAt

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfSmoothRaw
