import QuaternionicSymmetry.FourDimensionalHalfSpinLieProjection
import QuaternionicSymmetry.FourDimensionalHalfSpinHopfRaw
import QuaternionicSymmetry.QuaternionicProjectiveLineMaurer

/-! The infinitesimal Hopf action of the independently extracted left-spinor
connection agrees with the rank-three adjoint action.  The calculation is on
the actual quaternionic spinor model and precedes projective descent. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfInfinitesimal

open scoped Quaternion
open QuaternionicUnitQuaternionTransport
  QuaternionicUnitScalarIsometries
  FourDimensionalHalfSpinLieProjection
  QuaternionicProjectiveLineMaurer

noncomputable section

def quaternionHopf (v : ℍ) : ℍ := v * basisI * star v

theorem quaternionHopf_fderiv (v w : ℍ) :
    fderiv ℝ quaternionHopf v w =
      w * basisI * star v + v * basisI * star w := by
  have hleft : DifferentiableAt ℝ (fun z : ℍ => z * basisI) v :=
    differentiableAt_id.mul_const _
  have hstar : DifferentiableAt ℝ (fun z : ℍ => star z) v := by
    let f : ℍ →ₗ[ℝ] ℍ :=
      { toFun := star
        map_add' a b := by simp
        map_smul' r a := by simp [Quaternion.star_smul] }
    exact f.toContinuousLinearMap.differentiableAt
  have hd := fderiv_fun_mul' hleft hstar
  change fderiv ℝ quaternionHopf v = _ at hd
  rw [hd]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, op_smul_eq_mul]
  have hmul : fderiv ℝ (fun z : ℍ => z * basisI) v w = w * basisI := by
    let L : ℍ →L[ℝ] ℍ := ((ContinuousLinearMap.mul ℝ ℍ).flip basisI)
    change fderiv ℝ L v w = L w
    rw [L.fderiv]
  have hs : fderiv ℝ (fun z : ℍ => star z) v w = star w := by
    simpa using fderiv_star (fun z : ℍ => z) v differentiableAt_id w
  rw [hmul, hs]
  abel

/-- Infinitesimal left-quaternion action on the Hopf quadratic expression is
the literal commutator action. -/
theorem quaternionHopf_left_infinitesimal (a v : ℍ) (ha : a.re = 0) :
    fderiv ℝ quaternionHopf v (a * v) =
      a * quaternionHopf v - quaternionHopf v * a := by
  rw [quaternionHopf_fderiv]
  have hstar : star a = -a := Quaternion.star_eq_neg.mpr ha
  rw [star_mul, hstar]
  simp only [quaternionHopf]
  noncomm_ring

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfInfinitesimal
