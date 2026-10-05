import Mathlib.Analysis.Quaternion
import Mathlib.Tactic

open scoped Quaternion
open Quaternion

/-!
# A concrete quaternionic line

This file records only algebraic facts about the real quaternion line.  The
right actions below are actual right multiplications in `ℍ`; no quaternionic
structure or geometric conclusion is postulated.
-/

namespace QuaternionicSymmetry
namespace QuaternionicLine

noncomputable section

/-- The three standard imaginary units in `ℍ`. -/
def unitI : ℍ := ⟨0, 1, 0, 0⟩
def unitJ : ℍ := ⟨0, 0, 1, 0⟩
def unitK : ℍ := ⟨0, 0, 0, 1⟩

@[simp] theorem unitI_sq : unitI * unitI = (-1 : ℍ) := by
  ext <;> norm_num [unitI]

@[simp] theorem unitJ_sq : unitJ * unitJ = (-1 : ℍ) := by
  ext <;> norm_num [unitJ]

@[simp] theorem unitK_sq : unitK * unitK = (-1 : ℍ) := by
  ext <;> norm_num [unitK]

@[simp] theorem unitI_mul_unitJ : unitI * unitJ = unitK := by
  ext <;> norm_num [unitI, unitJ, unitK]

@[simp] theorem unitJ_mul_unitI : unitJ * unitI = -unitK := by
  ext <;> norm_num [unitI, unitJ, unitK]

@[simp] theorem unitJ_mul_unitK : unitJ * unitK = unitI := by
  ext <;> norm_num [unitI, unitJ, unitK]

@[simp] theorem unitK_mul_unitJ : unitK * unitJ = -unitI := by
  ext <;> norm_num [unitI, unitJ, unitK]

@[simp] theorem unitK_mul_unitI : unitK * unitI = unitJ := by
  ext <;> norm_num [unitI, unitJ, unitK]

@[simp] theorem unitI_mul_unitK : unitI * unitK = -unitJ := by
  ext <;> norm_num [unitI, unitJ, unitK]

@[simp] theorem norm_unitI : ‖unitI‖ = (1 : ℝ) := by
  rw [norm_eq_sqrt_real_inner, Quaternion.inner_self]
  simp [Quaternion.normSq_def', unitI]

@[simp] theorem norm_unitJ : ‖unitJ‖ = (1 : ℝ) := by
  rw [norm_eq_sqrt_real_inner, Quaternion.inner_self]
  simp [Quaternion.normSq_def', unitJ]

@[simp] theorem norm_unitK : ‖unitK‖ = (1 : ℝ) := by
  rw [norm_eq_sqrt_real_inner, Quaternion.inner_self]
  simp [Quaternion.normSq_def', unitK]

/-- Right multiplication by a quaternion, as a real-linear map. -/
def rightMul (q : ℍ) : ℍ →ₗ[ℝ] ℍ := LinearMap.mulRight ℝ q

@[simp] theorem rightMul_apply (q x : ℍ) : rightMul q x = x * q := rfl

private theorem rightMul_unitI_bijective : Function.Bijective (rightMul unitI) := by
  have hinv : Function.LeftInverse (rightMul (-unitI)) (rightMul unitI) := by
    intro x
    change (x * unitI) * (-unitI) = x
    simp [mul_assoc, mul_neg, unitI_sq]
  have hinv' : Function.RightInverse (rightMul (-unitI)) (rightMul unitI) := by
    intro x
    change (x * (-unitI)) * unitI = x
    simp [mul_assoc, mul_neg, unitI_sq]
  exact ⟨hinv.injective, hinv'.surjective⟩

private theorem rightMul_unitJ_bijective : Function.Bijective (rightMul unitJ) := by
  have hinv : Function.LeftInverse (rightMul (-unitJ)) (rightMul unitJ) := by
    intro x
    change (x * unitJ) * (-unitJ) = x
    simp [mul_assoc, mul_neg, unitJ_sq]
  have hinv' : Function.RightInverse (rightMul (-unitJ)) (rightMul unitJ) := by
    intro x
    change (x * (-unitJ)) * unitJ = x
    simp [mul_assoc, mul_neg, unitJ_sq]
  exact ⟨hinv.injective, hinv'.surjective⟩

private theorem rightMul_unitK_bijective : Function.Bijective (rightMul unitK) := by
  have hinv : Function.LeftInverse (rightMul (-unitK)) (rightMul unitK) := by
    intro x
    change (x * unitK) * (-unitK) = x
    simp [mul_assoc, mul_neg, unitK_sq]
  have hinv' : Function.RightInverse (rightMul (-unitK)) (rightMul unitK) := by
    intro x
    change (x * (-unitK)) * unitK = x
    simp [mul_assoc, mul_neg, unitK_sq]
  exact ⟨hinv.injective, hinv'.surjective⟩

/-- The actual real-linear right multiplication isometries by `i,j,k`. -/
noncomputable def rightI : ℍ ≃ₗᵢ[ℝ] ℍ :=
  LinearIsometryEquiv.mk
    (LinearEquiv.ofBijective (rightMul unitI) rightMul_unitI_bijective)
    (fun x => by simp [rightMul, norm_mul])

noncomputable def rightJ : ℍ ≃ₗᵢ[ℝ] ℍ :=
  LinearIsometryEquiv.mk
    (LinearEquiv.ofBijective (rightMul unitJ) rightMul_unitJ_bijective)
    (fun x => by simp [rightMul, norm_mul])

noncomputable def rightK : ℍ ≃ₗᵢ[ℝ] ℍ :=
  LinearIsometryEquiv.mk
    (LinearEquiv.ofBijective (rightMul unitK) rightMul_unitK_bijective)
    (fun x => by simp [rightMul, norm_mul])

@[simp] theorem rightI_apply (x : ℍ) : rightI x = x * unitI := rfl
@[simp] theorem rightJ_apply (x : ℍ) : rightJ x = x * unitJ := rfl
@[simp] theorem rightK_apply (x : ℍ) : rightK x = x * unitK := rfl

@[simp] theorem rightI_sq_apply (x : ℍ) : rightI (rightI x) = -x := by
  change (x * unitI) * unitI = -x
  rw [mul_assoc, unitI_sq]
  simp

@[simp] theorem rightJ_sq_apply (x : ℍ) : rightJ (rightJ x) = -x := by
  change (x * unitJ) * unitJ = -x
  rw [mul_assoc, unitJ_sq]
  simp

@[simp] theorem rightK_sq_apply (x : ℍ) : rightK (rightK x) = -x := by
  change (x * unitK) * unitK = -x
  rw [mul_assoc, unitK_sq]
  simp

@[simp] theorem rightI_rightJ_apply (x : ℍ) : rightI (rightJ x) = -rightJ (rightI x) := by
  change (x * unitJ) * unitI = -((x * unitI) * unitJ)
  rw [mul_assoc, mul_assoc, unitJ_mul_unitI, unitI_mul_unitJ]
  simp

@[simp] theorem rightJ_rightK_apply (x : ℍ) : rightJ (rightK x) = -rightK (rightJ x) := by
  change (x * unitK) * unitJ = -((x * unitJ) * unitK)
  rw [mul_assoc, mul_assoc, unitK_mul_unitJ, unitJ_mul_unitK]
  simp

@[simp] theorem rightK_rightI_apply (x : ℍ) : rightK (rightI x) = -rightI (rightK x) := by
  change (x * unitI) * unitK = -((x * unitK) * unitI)
  rw [mul_assoc, mul_assoc, unitI_mul_unitK, unitK_mul_unitI]
  simp

/-- A general purely imaginary quaternion in the standard three-dimensional span. -/
def imaginary (a b c : ℝ) : ℍ := a • unitI + b • unitJ + c • unitK

/-- Left multiplication by the imaginary quaternion `a i + b j + c k`. -/
def leftAction (a b c : ℝ) : ℍ →ₗ[ℝ] ℍ := LinearMap.mulLeft ℝ (imaginary a b c)

@[simp] theorem leftAction_apply (a b c : ℝ) (x : ℍ) : leftAction a b c x = imaginary a b c * x := rfl

@[simp] theorem leftAction_commutes_rightI (a b c : ℝ) (x : ℍ) :
    leftAction a b c (rightI x) = rightI (leftAction a b c x) := by
  change imaginary a b c * (x * unitI) = (imaginary a b c * x) * unitI
  rw [mul_assoc]

@[simp] theorem leftAction_commutes_rightJ (a b c : ℝ) (x : ℍ) :
    leftAction a b c (rightJ x) = rightJ (leftAction a b c x) := by
  change imaginary a b c * (x * unitJ) = (imaginary a b c * x) * unitJ
  rw [mul_assoc]

@[simp] theorem leftAction_commutes_rightK (a b c : ℝ) (x : ℍ) :
    leftAction a b c (rightK x) = rightK (leftAction a b c x) := by
  change imaginary a b c * (x * unitK) = (imaginary a b c * x) * unitK
  rw [mul_assoc]

@[simp] theorem star_imaginary (a b c : ℝ) : star (imaginary a b c) = -imaginary a b c := by
  ext <;> simp [imaginary, unitI, unitJ, unitK]

/-- Left multiplication by a purely imaginary quaternion is skew-adjoint. -/
theorem leftAction_skew_adjoint (a b c : ℝ) (x y : ℍ) :
    inner ℝ (leftAction a b c x) y = -(inner ℝ x (leftAction a b c y)) := by
  rw [Quaternion.inner_def, Quaternion.inner_def, leftAction_apply, leftAction_apply,
    StarMul.star_mul, star_imaginary]
  simp only [mul_neg, Quaternion.re_neg, Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul]
  ring

end
end QuaternionicLine
end QuaternionicSymmetry
