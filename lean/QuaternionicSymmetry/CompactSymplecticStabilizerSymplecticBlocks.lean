import QuaternionicSymmetry.CompactSymplecticStabilizerFormBlocks

/-! A genuine element of the first-projector stabilizer preserves the
alternating form on each of its two diagonal blocks. -/

namespace QuaternionicSymmetry.CompactSymplecticStabilizerSymplecticBlocks

open Matrix CompactSymplecticHaar CompactSymplecticProjectiveQuotient
open CompactSymplecticStabilizerIndex CompactSymplecticStabilizerDiagonal
open CompactSymplecticStabilizerFormBlocks
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev J (n : ℕ) := Fin n ⊕ Fin n
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

theorem blockMatrix_preserves_form (n : ℕ) (u : G n) :
    (blockMatrix n u)ᵀ * blockStandardJ n * blockMatrix n u =
      blockStandardJ n := by
  classical
  have h := congrArg (Matrix.reindexAlgEquiv ℂ ℂ (blockIndexEquiv n)) u.2
  rw [Matrix.reindexAlgEquiv_mul, Matrix.reindexAlgEquiv_mul] at h
  simpa only [Matrix.reindexAlgEquiv_apply,
    Matrix.transpose_reindex, blockMatrix, blockStandardJ] using h

theorem symplectic_diagonal_blocks (n : ℕ) (u : G n)
    (hu : u ∈ firstPairStabilizer n) :
    (blockMatrix n u).toBlocks₁₁ᵀ * firstBlockJ *
      (blockMatrix n u).toBlocks₁₁ = firstBlockJ ∧
    (blockMatrix n u).toBlocks₂₂ᵀ * standardJ n *
      (blockMatrix n u).toBlocks₂₂ = standardJ n := by
  classical
  have h := blockMatrix_preserves_form n u
  rw [blockMatrix_eq_fromBlocks n u hu,
    blockStandardJ_eq_fromBlocks] at h
  simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at h
  constructor
  · have h₁₁ := congrArg Matrix.toBlocks₁₁ h
    simpa only [Matrix.toBlocks_fromBlocks₁₁, mul_assoc] using h₁₁
  · have h₂₂ := congrArg Matrix.toBlocks₂₂ h
    simpa only [Matrix.toBlocks_fromBlocks₂₂, mul_assoc] using h₂₂

end
end QuaternionicSymmetry.CompactSymplecticStabilizerSymplecticBlocks
