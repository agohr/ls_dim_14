import QuaternionicSymmetry.CompactSymplecticStabilizerDiagonal

/-! The two actual diagonal blocks of a projector-stabilizing compact
symplectic matrix are unitary. The remaining symplectic-preservation split
is proved separately. -/

namespace QuaternionicSymmetry.CompactSymplecticStabilizerUnitaryBlocks

open Matrix CompactSymplecticHaar CompactSymplecticProjectiveQuotient
open CompactSymplecticStabilizerIndex CompactSymplecticStabilizerDiagonal
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev J (n : ℕ) := Fin n ⊕ Fin n
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

theorem blockMatrix_unitary (n : ℕ) (u : G n) :
    blockMatrix n u ∈ Matrix.unitaryGroup (Fin 2 ⊕ J n) ℂ := by
  classical
  have hu : (u.1 : Matrix (I n) (I n) ℂ) ∈ Matrix.unitaryGroup (I n) ℂ := u.1.property
  rw [Matrix.mem_unitaryGroup_iff'] at hu ⊢
  have h := congrArg (Matrix.reindexAlgEquiv ℂ ℂ (blockIndexEquiv n)) hu
  rw [Matrix.reindexAlgEquiv_mul] at h
  simpa only [Matrix.star_eq_conjTranspose, Matrix.reindexAlgEquiv_apply,
    Matrix.reindexAlgEquiv_mul, Matrix.conjTranspose_reindex, map_one,
    blockMatrix] using h

theorem unitary_diagonal_blocks (n : ℕ) (u : G n)
    (hu : u ∈ firstPairStabilizer n) :
    (blockMatrix n u).toBlocks₁₁ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
    (blockMatrix n u).toBlocks₂₂ ∈ Matrix.unitaryGroup (J n) ℂ := by
  classical
  have hunit := blockMatrix_unitary n u
  rw [Matrix.mem_unitaryGroup_iff'] at hunit
  rw [blockMatrix_eq_fromBlocks n u hu] at hunit
  simp only [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
    add_zero, zero_add] at hunit
  rw [← Matrix.fromBlocks_one (l := Fin 2) (m := J n)] at hunit
  constructor
  · rw [Matrix.mem_unitaryGroup_iff']
    have h := congrArg Matrix.toBlocks₁₁ hunit
    simpa only [Matrix.toBlocks_fromBlocks₁₁,
      Matrix.star_eq_conjTranspose] using h
  · rw [Matrix.mem_unitaryGroup_iff']
    have h := congrArg Matrix.toBlocks₂₂ hunit
    simpa only [Matrix.toBlocks_fromBlocks₂₂,
      Matrix.star_eq_conjTranspose] using h

end
end QuaternionicSymmetry.CompactSymplecticStabilizerUnitaryBlocks
