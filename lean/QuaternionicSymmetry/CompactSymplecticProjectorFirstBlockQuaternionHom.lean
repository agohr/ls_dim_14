import QuaternionicSymmetry.CompactSymplecticProjectorFirstBlockHopfAction

/-! The checked first-block-to-unit-quaternion correspondence respects
multiplication, giving the genuine Sp(1) action needed to form the associated
CP¹ and twistor-sphere bundles over the projector quotient. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorFirstBlockQuaternionHom

open Matrix
open CompactSymplecticStabilizerBlockPair
open CompactSymplecticProjectorFirstBlockHalfSpin
open CompactSymplecticProjectorFirstBlockUnitQuaternion
open FourDimensionalHalfSpinMatrix
open scoped Quaternion Matrix

noncomputable section

theorem halfSpinMatrix_injective : Function.Injective halfSpinMatrix := by
  intro p q hpq
  have h00 := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hpq
  have h10 := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) hpq
  have hf : first p = first q := by simpa [halfSpinMatrix] using h00
  have hs : second p = second q := by simpa [halfSpinMatrix] using h10
  apply Quaternion.ext
  · exact congrArg Complex.re hf
  · exact congrArg Complex.im hf
  · exact congrArg Complex.re hs
  · have h := congrArg Complex.im hs
    simpa [second] using congrArg Neg.neg h

def firstBlockUnitQuaternionHom : FirstBlockGroup →* unitary ℍ where
  toFun := firstBlockUnitQuaternion
  map_one' := by
    apply Subtype.ext
    apply halfSpinMatrix_injective
    calc
      halfSpinMatrix ((firstBlockUnitQuaternion (1 : FirstBlockGroup) : unitary ℍ) : ℍ) =
          (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
            rw [firstBlockUnitQuaternion_coe, firstBlock_halfSpinMatrix]
            rfl
      _ = halfSpinMatrix (1 : ℍ) := halfSpinMatrix_one.symm
  map_mul' A B := by
    apply Subtype.ext
    apply halfSpinMatrix_injective
    calc
      halfSpinMatrix ((firstBlockUnitQuaternion (A * B) : unitary ℍ) : ℍ) =
          ((A * B).1.1 : Matrix (Fin 2) (Fin 2) ℂ) := by
            rw [firstBlockUnitQuaternion_coe, firstBlock_halfSpinMatrix]
      _ = (A.1.1 : Matrix (Fin 2) (Fin 2) ℂ) *
          (B.1.1 : Matrix (Fin 2) (Fin 2) ℂ) := rfl
      _ = halfSpinMatrix
          (((firstBlockUnitQuaternion A : unitary ℍ) : ℍ) *
            ((firstBlockUnitQuaternion B : unitary ℍ) : ℍ)) := by
            rw [halfSpinMatrix_mul]
            rw [firstBlockUnitQuaternion_coe, firstBlockUnitQuaternion_coe,
              firstBlock_halfSpinMatrix, firstBlock_halfSpinMatrix]

@[simp] theorem firstBlockUnitQuaternionHom_apply (A : FirstBlockGroup) :
    firstBlockUnitQuaternionHom A = firstBlockUnitQuaternion A := rfl

end
end QuaternionicSymmetry.CompactSymplecticProjectorFirstBlockQuaternionHom
