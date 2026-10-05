import QuaternionicSymmetry.FourDimensionalHalfSpinHopfNormalizedPath

/-! The normalized Hopf direction has the same infinitesimal adjoint
action under a pure-imaginary left-spinor rotation as the raw quadratic
Hopf expression. The normalization denominator has zero first variation. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfNormalizedDerivative

open scoped Quaternion ContDiff
open FourDimensionalHalfSpinHopfNormalizedPath
  FourDimensionalHalfSpinHopfInfinitesimal
  QuaternionicUnitQuaternionTransport
  QuaternionicUnitScalarIsometries

noncomputable section

private def starLinear : ℍ →ₗ[ℝ] ℍ where
  toFun := star
  map_add' p q := by simp
  map_smul' r p := by simp [Quaternion.star_smul]

theorem normalizedQuaternionHopf_differentiableAt (q : ℍ) (hq : q ≠ 0) :
    DifferentiableAt ℝ normalizedQuaternionHopf q := by
  have hnorm : DifferentiableAt ℝ
      (fun v : ℍ => Quaternion.normSq v) q := by
    have hcont : ContDiffAt ℝ ∞ (fun v : ℍ => ‖v‖) q :=
      contDiffAt_norm ℝ hq
    have hnorm0 : DifferentiableAt ℝ (fun v : ℍ => ‖v‖) q :=
      hcont.differentiableAt (by simp)
    have h := hnorm0.pow 2
    convert h using 1
    funext v
    simpa only [Pi.pow_apply] using
      (Quaternion.normSq_eq_norm_mul_self v).trans (by ring : ‖v‖ * ‖v‖ = ‖v‖ ^ 2)
  have hnz : Quaternion.normSq q ≠ 0 :=
    (Quaternion.normSq_ne_zero).mpr hq
  have hstar : DifferentiableAt ℝ (star : ℍ → ℍ) q :=
    starLinear.toContinuousLinearMap.differentiableAt
  have hhopf : DifferentiableAt ℝ quaternionHopf q := by
    unfold quaternionHopf
    exact (differentiableAt_id.mul_const basisI).mul hstar
  exact (hnorm.inv hnz).smul hhopf

theorem normalizedQuaternionHopf_left_infinitesimal
    (a q : ℍ) (ha : a.re = 0) (hq : q ≠ 0) :
    fderiv ℝ normalizedQuaternionHopf q (a*q) =
      a * normalizedQuaternionHopf q - normalizedQuaternionHopf q * a := by
  let H := normalizedQuaternionHopf q
  have hA : HasDerivAt (fun t : ℝ => (1 : ℍ) + t • a) a 0 := by
    convert (hasDerivAt_const (0 : ℝ) (1 : ℍ)).add
      ((hasDerivAt_id (0 : ℝ)).smul_const a) using 1 <;> simp
  have hB : HasDerivAt (fun t : ℝ => (1 : ℍ) - t • a) (-a) 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) (1 : ℍ)).sub
      ((hasDerivAt_id (0 : ℝ)).smul_const a)
  have hnum : HasDerivAt
      (fun t : ℝ => ((1 : ℍ) + t • a) * H * ((1 : ℍ) - t • a))
      (a*H-H*a) 0 := by
    convert (hA.mul_const H).mul hB using 1 <;> simp [H, sub_eq_add_neg]
  have hsq : HasDerivAt
      (fun t : ℝ => 1 + t^2 * Quaternion.normSq a) 0 0 := by
    convert (hasDerivAt_const (0 : ℝ) (1 : ℝ)).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const
        (Quaternion.normSq a)) using 1 <;> simp
  have hden : HasDerivAt
      (fun t : ℝ => (Quaternion.normSq ((1 : ℍ) + t • a))⁻¹) 0 0 := by
    have hden' : HasDerivAt
        (fun t : ℝ => (1 + t^2 * Quaternion.normSq a)⁻¹) 0 0 := by
      simpa using hsq.inv (by norm_num : (1 : ℝ) + 0^2 * Quaternion.normSq a ≠ 0)
    simpa only [pureQuaternion_path_normSq a ha] using hden'
  have hpath : HasDerivAt
      (fun t : ℝ => normalizedQuaternionHopf (((1 : ℍ) + t • a) * q))
      (a*H-H*a) 0 := by
    have h := hden.smul hnum
    convert h using 1
    · funext t
      exact normalizedQuaternionHopf_path a q ha t
    · simp [H]
  have hcurve : HasDerivAt
      (fun t : ℝ => ((1 : ℍ) + t • a) * q) (a*q) 0 := by
    simpa using hA.mul_const q
  have hchain : HasDerivAt
      (fun t : ℝ => normalizedQuaternionHopf (((1 : ℍ) + t • a) * q))
      (fderiv ℝ normalizedQuaternionHopf q (a*q)) 0 := by
    have hAt : HasFDerivAt normalizedQuaternionHopf
        (fderiv ℝ normalizedQuaternionHopf q) (((1 : ℍ) + (0 : ℝ) • a) * q) := by
      simpa using (normalizedQuaternionHopf_differentiableAt q hq).hasFDerivAt
    exact hAt.comp_hasDerivAt 0 hcurve
  exact hchain.deriv.symm.trans hpath.deriv

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfNormalizedDerivative
