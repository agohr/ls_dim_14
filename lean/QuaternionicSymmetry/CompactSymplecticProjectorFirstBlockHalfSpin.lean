import QuaternionicSymmetry.CompactSymplecticProjectorFirstBlockQuaternionUnit
import QuaternionicSymmetry.FourDimensionalHalfSpinMatrix
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! The actual first two-by-two compact symplectic stabilizer block is
literally the checked half-spin matrix of its quaternionic scalar. This is
the representation bridge needed for stabilizer-independent Hopf descent. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorFirstBlockHalfSpin

open Matrix
open CompactSymplecticStabilizerBlockPair
open CompactSymplecticStabilizerFormBlocks
open CompactSymplecticProjectorQuaternionicRow
open CompactSymplecticProjectorBaseQuaternionAction
open FourDimensionalHalfSpinMatrix
open scoped Quaternion Matrix

noncomputable section

private abbrev BMat := Matrix (Fin 2) (Fin 2) ℂ

theorem firstBlock_det_one (A : FirstBlockGroup) :
    Matrix.det (A.1.1 : BMat) = 1 := by
  let B : BMat := A.1.1
  have h := congrArg (fun M : BMat => M 0 1) A.2
  have hs : -(B 1 0 * B 0 1) + B 0 0 * B 1 1 = 1 := by
    simpa [B, Matrix.mul_apply, Fin.sum_univ_two,
      firstBlockJ_zero_zero, firstBlockJ_zero_one,
      firstBlockJ_one_zero, firstBlockJ_one_one] using h
  have hdet : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 1 := by
    linear_combination hs
  simpa [B, Matrix.det_fin_two] using hdet

private theorem firstBlock_adjugate_eq_conjTranspose (A : FirstBlockGroup) :
    Matrix.adjugate (A.1.1 : BMat) = (A.1.1 : BMat)ᴴ := by
  let B : BMat := A.1.1
  have hunit : Bᴴ * B = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff').mp A.1.property
    simpa [B, Matrix.star_eq_conjTranspose] using h
  have hadj : B * Matrix.adjugate B = 1 := by
    rw [Matrix.mul_adjugate, firstBlock_det_one A]
    simp
  have heq : Bᴴ = Matrix.adjugate B := by
    calc
      Bᴴ = Bᴴ * (B * Matrix.adjugate B) := by rw [hadj, mul_one]
      _ = (Bᴴ * B) * Matrix.adjugate B := by rw [mul_assoc]
      _ = Matrix.adjugate B := by rw [hunit, one_mul]
  exact heq.symm

theorem firstBlock_lower_entries (A : FirstBlockGroup) :
    (A.1.1 : BMat) 1 0 = -star ((A.1.1 : BMat) 0 1) ∧
    (A.1.1 : BMat) 1 1 = star ((A.1.1 : BMat) 0 0) := by
  let B : BMat := A.1.1
  have h := firstBlock_adjugate_eq_conjTranspose A
  have h01 := congrArg (fun M : BMat => M 0 1) h
  have h00 := congrArg (fun M : BMat => M 0 0) h
  have hc : B 1 0 = -star (B 0 1) := by
    have hc' : -(B 0 1) = star (B 1 0) := by
      simpa [B, Matrix.adjugate_fin_two, Matrix.conjTranspose_apply] using h01
    have hc'' := congrArg Star.star hc'
    simpa using hc''.symm
  have hd : B 1 1 = star (B 0 0) := by
    simpa [B, Matrix.adjugate_fin_two, Matrix.conjTranspose_apply] using h00
  exact ⟨hc,hd⟩

theorem firstBlock_halfSpinMatrix (A : FirstBlockGroup) :
    halfSpinMatrix (firstBlockQuaternion A) = (A.1.1 : BMat) := by
  obtain ⟨hc,hd⟩ := firstBlock_lower_entries A
  let B : BMat := A.1.1
  have hfirst : first (firstBlockQuaternion A) = B 0 0 := by
    apply Complex.ext <;> simp [first, firstBlockQuaternion, B]
  have hsecond : second (firstBlockQuaternion A) = -star (B 0 1) := by
    apply Complex.ext <;> simp [second, firstBlockQuaternion, B]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [halfSpinMatrix, hfirst, hsecond, B, hc, hd]

end
end QuaternionicSymmetry.CompactSymplecticProjectorFirstBlockHalfSpin
