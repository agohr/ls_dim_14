import QuaternionicSymmetry.FourDimensionalHalfSpinTwoSidedKernel

/-! The literal projective half-spin matrix action depends only on the
underlying two-sided real orthogonal isometry, because the only ambiguity
in the quaternion pair is the simultaneous central sign. This gives the
actual projective descent on the image of the two-sided map, pending its
separate identification with all of `SO(4)`. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinTwoSidedProjectiveDescent

open scoped Quaternion Matrix
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinMatrix
  FourDimensionalHalfSpinTwoSidedOrthogonal
  FourDimensionalHalfSpinTwoSidedKernel

noncomputable section

theorem projectiveHalfSpin_one :
    projectiveHalfSpin (1 : unitary ℍ) = id := by
  funext p
  induction p using Projectivization.ind with
  | h v hv =>
    rw [projectiveHalfSpin_mk]
    change Projectivization.mk ℂ (halfSpinLinearEquiv 1 v) _ =
      Projectivization.mk ℂ v hv
    congr 1
    simpa only [map_one] using
      congrArg (fun A : Spinor ≃ₗ[ℂ] Spinor => A v)
        (show halfSpinLinearEquiv (1 : unitary ℍ) = 1 by
          apply LinearEquiv.ext
          intro w
          rw [halfSpinLinearEquiv_apply]
          change halfSpinMatrix (1 : ℍ) *ᵥ w = w
          rw [halfSpinMatrix_one]
          simp)

private theorem projectiveHalfSpin_sign (q : unitary ℍ)
    (hq : (q : ℍ) = 1 ∨ (q : ℍ) = -1) :
    projectiveHalfSpin q = id := by
  rcases hq with hq | hq
  · have h : q = 1 := Subtype.ext hq
    simpa [h] using projectiveHalfSpin_one
  · have h : q = -1 := Subtype.ext hq
    simpa [h] using projectiveHalfSpin_neg_one

theorem projectiveHalfSpin_eq_of_twoSided_eq
    (q r q' r' : unitary ℍ)
    (h : twoSidedIsometry q r = twoSidedIsometry q' r') :
    projectiveHalfSpin q = projectiveHalfSpin q' := by
  let p : unitary ℍ × unitary ℍ := (q,r)
  let p' : unitary ℍ × unitary ℍ := (q',r')
  have hker : twoSidedHom (p⁻¹ * p') = 1 := by
    rw [map_mul, map_inv]
    change (twoSidedIsometry q r)⁻¹ * twoSidedIsometry q' r' = 1
    rw [← h]
    group
  have hsign := twoSidedHom_kernel_sign
    (p⁻¹ * p').1 (p⁻¹ * p').2 hker
  have hleft : ((q⁻¹ * q' : unitary ℍ) : ℍ) = 1 ∨
      ((q⁻¹ * q' : unitary ℍ) : ℍ) = -1 := by
    simpa [p,p'] using hsign.imp (fun h => h.1) (fun h => h.1)
  have hk := projectiveHalfSpin_sign (q⁻¹ * q') hleft
  have hcomp := projectiveHalfSpin_mul q (q⁻¹ * q')
  rw [mul_inv_cancel_left] at hcomp
  rw [hk, Function.comp_id] at hcomp
  exact hcomp.symm

end
end QuaternionicSymmetry.FourDimensionalHalfSpinTwoSidedProjectiveDescent
