import QuaternionicSymmetry.FourDimensionalHalfSpinTwoSidedOrthogonal
import QuaternionicSymmetry.QuaternionicUnitQuaternionTransport

/-! The kernel of the concrete two-sided quaternionic orthogonal action is
exactly the simultaneous central sign. Thus the candidate projective
half-spin action is well-defined on the image of the real orthogonal map,
without any global spin lift. Surjectivity onto `SO(4)` is separate. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinTwoSidedKernel

open scoped Quaternion
open FourDimensionalHalfSpinTwoSidedOrthogonal
  FourDimensionalHalfSpinProjective
  QuaternionicUnitQuaternionTransport

noncomputable section

private theorem central_real (q : ℍ)
    (hi : q * basisI = basisI * q)
    (hj : q * basisJ = basisJ * q) : q = (q.re : ℍ) := by
  have hJ : q.imJ = 0 := by
    have h := congrArg (fun z : ℍ => z.imK) hi
    simp [Quaternion.imK_mul, basisI] at h
    linarith
  have hK : q.imK = 0 := by
    have h := congrArg (fun z : ℍ => z.imJ) hi
    simp [Quaternion.imJ_mul, basisI] at h
    linarith
  have hI : q.imI = 0 := by
    have h := congrArg (fun z : ℍ => z.imK) hj
    simp [Quaternion.imK_mul, basisJ] at h
    linarith
  ext <;> simp [hI,hJ,hK]

theorem twoSidedHom_kernel_sign (q r : unitary ℍ)
    (h : twoSidedHom (q,r) = 1) :
    ((q : ℍ) = 1 ∧ (r : ℍ) = 1) ∨
      ((q : ℍ) = -1 ∧ (r : ℍ) = -1) := by
  have hw (w : ℍ) : (q : ℍ) * w * star (r : ℍ) = w := by
    have he := congrArg (fun T : ℍ ≃ₗᵢ[ℝ] ℍ => T w) h
    change twoSidedIsometry q r w = w at he
    rw [twoSidedIsometry_apply] at he
    exact he
  have hqr : (q : ℍ) = r := by
    have h1 := hw 1
    have he := congrArg (fun z : ℍ => z * (r : ℍ)) h1
    simpa [mul_assoc, (Unitary.mem_iff.mp r.property).1] using he
  have hcomm (w : ℍ) : (q : ℍ) * w = w * q := by
    have htw : (q : ℍ) * w * star (q : ℍ) = w := by
      simpa only [← hqr] using hw w
    calc
      (q : ℍ) * w = ((q : ℍ) * w) *
          (star (q : ℍ) * (q : ℍ)) := by
            rw [(Unitary.mem_iff.mp q.property).1, mul_one]
      _ = ((q : ℍ) * w * star (q : ℍ)) * (q : ℍ) := by
            simp only [mul_assoc]
      _ = w * q := by rw [htw]
  have hreal := central_real (q : ℍ) (hcomm basisI) (hcomm basisJ)
  have hn : q.1.re ^ 2 = 1 := by
    have hunit := QuaternionicUnitScalarIsometries.normSq_one_of_unitary q
    rw [hreal, Quaternion.normSq_coe] at hunit
    exact hunit
  rcases sq_eq_one_iff.mp hn with hr | hr
  · left
    have hq : (q : ℍ) = 1 := by simpa [hr] using hreal
    exact ⟨hq, hqr.symm.trans hq⟩
  · right
    have hq : (q : ℍ) = -1 := by simpa [hr] using hreal
    exact ⟨hq, hqr.symm.trans hq⟩

end
end QuaternionicSymmetry.FourDimensionalHalfSpinTwoSidedKernel
