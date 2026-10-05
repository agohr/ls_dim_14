import QuaternionicSymmetry.FourDimensionalHalfSpinNormalizerHolomorphic
import QuaternionicSymmetry.QuaternionicProjectiveStandardHilbertStructure

/-! The literal two-sided unit-quaternion action on the real four-space
`ℍ`: `(q,r)` sends `w` to `q w r*`. This is an actual orthogonal action,
not yet a proof that it exhausts `SO(4)`. The half-spin projective action
uses the left factor. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinTwoSidedOrthogonal

open scoped Quaternion
open QuaternionicUnitScalarIsometries
  QuaternionicProjectiveStandardHilbertStructure
  FourDimensionalHalfSpinProjective

noncomputable section

private theorem unit_norm (q : unitary ℍ) : ‖(q : ℍ)‖ = 1 := by
  have hn := Quaternion.normSq_eq_norm_mul_self (q : ℍ)
  rw [normSq_one_of_unitary] at hn
  nlinarith [norm_nonneg (q : ℍ)]

def rightUnitIsometry (r : unitary ℍ) : ℍ ≃ₗᵢ[ℝ] ℍ where
  toFun w := w * star (r : ℍ)
  invFun w := w * (r : ℍ)
  map_add' a b := add_mul a b _
  map_smul' s w := by
    simp only [Algebra.smul_def]
    simp [mul_assoc]
  left_inv w := by
    change (w * star (r : ℍ)) * (r : ℍ) = w
    rw [mul_assoc, (Unitary.mem_iff.mp r.property).1, mul_one]
  right_inv w := by
    change (w * (r : ℍ)) * star (r : ℍ) = w
    rw [mul_assoc, (Unitary.mem_iff.mp r.property).2, mul_one]
  norm_map' w := by
    change ‖w * star (r : ℍ)‖ = ‖w‖
    rw [norm_mul, Quaternion.norm_star, unit_norm r, mul_one]

@[simp] theorem rightUnitIsometry_apply (r : unitary ℍ) (w : ℍ) :
    rightUnitIsometry r w = w * star (r : ℍ) := rfl

def twoSidedIsometry (q r : unitary ℍ) : ℍ ≃ₗᵢ[ℝ] ℍ :=
  leftUnitIsometry q * rightUnitIsometry r

@[simp] theorem twoSidedIsometry_apply (q r : unitary ℍ) (w : ℍ) :
    twoSidedIsometry q r w = (q : ℍ) * w * star (r : ℍ) := by
  change (q : ℍ) * (w * star (r : ℍ)) = _
  rw [mul_assoc]

theorem twoSidedIsometry_mul (q r q' r' : unitary ℍ) :
    twoSidedIsometry (q*q') (r*r') =
      twoSidedIsometry q r * twoSidedIsometry q' r' := by
  apply LinearIsometryEquiv.ext
  intro w
  simp only [LinearIsometryEquiv.mul_def, LinearIsometryEquiv.trans_apply,
    twoSidedIsometry_apply, Submonoid.coe_mul, star_mul]
  simp only [mul_assoc]

def twoSidedHom :
    (unitary ℍ × unitary ℍ) →* (ℍ ≃ₗᵢ[ℝ] ℍ) where
  toFun p := twoSidedIsometry p.1 p.2
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro w
    simp [twoSidedIsometry_apply]
  map_mul' p q := by
    exact twoSidedIsometry_mul p.1 p.2 q.1 q.2

theorem simultaneous_neg_one_trivial :
    twoSidedHom ((-1 : unitary ℍ), (-1 : unitary ℍ)) = 1 := by
  apply LinearIsometryEquiv.ext
  intro w
  change twoSidedIsometry (-1 : unitary ℍ) (-1 : unitary ℍ) w = w
  rw [twoSidedIsometry_apply]
  change (-1 : ℍ) * w * star (-1 : ℍ) = w
  simp

theorem simultaneous_neg_one_projective_trivial (p : ProjectiveSpinor) :
    projectiveHalfSpin (-1 : unitary ℍ) p = p := by
  exact congrFun projectiveHalfSpin_neg_one p

end
end QuaternionicSymmetry.FourDimensionalHalfSpinTwoSidedOrthogonal
