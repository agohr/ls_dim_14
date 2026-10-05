import QuaternionicSymmetry.CompactSymplecticProjectorIsotropyBlocks

/-! Explicit compact-symplectic first-block units realizing the genuine
quaternionic base-tangent operators under the checked isotropy action. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorFirstBlockUnits

open Matrix
open CompactSymplecticStabilizerFormBlocks
open CompactSymplecticStabilizerBlockPair
open CompactSymplecticProjectorQuaternionicRow
noncomputable section

private def iMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.I, 0; 0, -Complex.I]

private def jMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -1; 1, 0]

private theorem iMatrix_unitary : iMatrix ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [iMatrix, Matrix.star_eq_conjTranspose, Matrix.mul_apply,
      Fin.sum_univ_two]

private theorem jMatrix_unitary : jMatrix ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jMatrix, Matrix.star_eq_conjTranspose, Matrix.mul_apply,
      Fin.sum_univ_two]

private theorem iMatrix_preserves_form :
    iMatrixᵀ * firstBlockJ * iMatrix = firstBlockJ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [iMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      firstBlockJ_zero_zero, firstBlockJ_zero_one,
      firstBlockJ_one_zero, firstBlockJ_one_one]

private theorem jMatrix_preserves_form :
    jMatrixᵀ * firstBlockJ * jMatrix = firstBlockJ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      firstBlockJ_zero_zero, firstBlockJ_zero_one,
      firstBlockJ_one_zero, firstBlockJ_one_one]

/-- The literal unit quaternion `i` in the checked first Sp(1) block. -/
def firstI : FirstBlockGroup :=
  ⟨⟨iMatrix, iMatrix_unitary⟩, iMatrix_preserves_form⟩

/-- The literal unit quaternion `j`, with its sign chosen so that its
action on the first row matches `QuaternionicMatrixModel.standardJ`. -/
def firstJ : FirstBlockGroup :=
  ⟨⟨jMatrix, jMatrix_unitary⟩, jMatrix_preserves_form⟩

theorem firstI_matrix : (firstI.1.1 : Matrix (Fin 2) (Fin 2) ℂ) = iMatrix := rfl
theorem firstJ_matrix : (firstJ.1.1 : Matrix (Fin 2) (Fin 2) ℂ) = jMatrix := rfl

theorem firstI_row (n : ℕ) (B : Matrix (Fin 2) (Fin n ⊕ Fin n) ℂ)
    (c : Fin n ⊕ Fin n) : (iMatrix * B) 0 c = Complex.I * B 0 c := by
  simp [iMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem firstJ_row (n : ℕ) (B : Matrix (Fin 2) (Fin n ⊕ Fin n) ℂ)
    (c : Fin n ⊕ Fin n) : (jMatrix * B) 0 c = -B 1 c := by
  simp [jMatrix, Matrix.mul_apply, Fin.sum_univ_two]

end
end QuaternionicSymmetry.CompactSymplecticProjectorFirstBlockUnits
