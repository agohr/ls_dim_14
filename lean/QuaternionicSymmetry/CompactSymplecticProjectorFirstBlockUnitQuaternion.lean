import QuaternionicSymmetry.CompactSymplecticProjectorFirstBlockHalfSpin
import QuaternionicSymmetry.QuaternionicUnitQuaternionTransport

/-! The quaternion extracted from an actual first compact-symplectic block
has squared norm one, allowing the checked Hopf-equivariance theorem to be
applied directly to stabilizer elements. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorFirstBlockUnitQuaternion

open Matrix
open CompactSymplecticStabilizerBlockPair
open CompactSymplecticProjectorBaseQuaternionAction
open CompactSymplecticProjectorFirstBlockHalfSpin
open scoped Quaternion Matrix

noncomputable section

private abbrev BMat := Matrix (Fin 2) (Fin 2) ℂ

theorem firstBlockQuaternion_normSq_one (A : FirstBlockGroup) :
    Quaternion.normSq (firstBlockQuaternion A) = 1 := by
  let B : BMat := A.1.1
  have hunit : B * Bᴴ = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff).mp A.1.property
    simpa [B, Matrix.star_eq_conjTranspose] using h
  have h00 := congrArg (fun M : BMat => M 0 0) hunit
  have hab : Complex.normSq (B 0 0) + Complex.normSq (B 0 1) = 1 := by
    apply Complex.ofReal_injective
    simpa [B, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Complex.ofReal_add,
      Complex.normSq_eq_conj_mul_self, Complex.star_def,
      mul_comm] using h00
  have hq : Quaternion.normSq (firstBlockQuaternion A) =
      Complex.normSq (B 0 0) + Complex.normSq (B 0 1) := by
    simp [firstBlockQuaternion, Quaternion.normSq_def',
      Complex.normSq_apply, B]
    ring
  exact hq.trans hab

def firstBlockUnitQuaternion (A : FirstBlockGroup) : unitary ℍ :=
  QuaternionicUnitQuaternionTransport.ofNormSqOne
    (firstBlockQuaternion A) (firstBlockQuaternion_normSq_one A)

@[simp] theorem firstBlockUnitQuaternion_coe (A : FirstBlockGroup) :
    ((firstBlockUnitQuaternion A : unitary ℍ) : ℍ) =
      firstBlockQuaternion A := rfl

end
end QuaternionicSymmetry.CompactSymplecticProjectorFirstBlockUnitQuaternion
