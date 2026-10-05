import QuaternionicSymmetry.CompactSymplecticStabilizerIndex

/-! The first-projector stabilizer is literally block diagonal after the
explicit reindexing of the two complex halves. -/

namespace QuaternionicSymmetry.CompactSymplecticStabilizerDiagonal

open Matrix CompactSymplecticHaar CompactSymplecticProjectiveQuotient
open CompactSymplecticStabilizerBlocks CompactSymplecticStabilizerIndex
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev J (n : ℕ) := Fin n ⊕ Fin n
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

/-- The actual matrix in coordinates split into the first quaternionic pair
and the remaining `n` quaternionic pairs. -/
def blockMatrix (n : ℕ) (u : G n) :
    Matrix (Fin 2 ⊕ J n) (Fin 2 ⊕ J n) ℂ :=
  (u.1 : Matrix (I n) (I n) ℂ).reindex (blockIndexEquiv n) (blockIndexEquiv n)

private theorem firstPair_preimage_left (n : ℕ) (i : Fin 2) :
    InFirstPair n ((blockIndexEquiv n).symm (Sum.inl i)) := by
  apply (blockIndexEquiv_firstPair_iff n _).2
  exact ⟨i, (blockIndexEquiv n).apply_symm_apply _⟩

private theorem not_firstPair_preimage_right (n : ℕ) (i : J n) :
    ¬InFirstPair n ((blockIndexEquiv n).symm (Sum.inr i)) := by
  intro h
  obtain ⟨j, hj⟩ := (blockIndexEquiv_firstPair_iff n _).1 h
  simpa using hj

theorem mem_stabilizer_iff_block_off_diagonal_zero (n : ℕ) (u : G n) :
    u ∈ firstPairStabilizer n ↔
      (blockMatrix n u).toBlocks₁₂ = 0 ∧
      (blockMatrix n u).toBlocks₂₁ = 0 := by
  classical
  rw [mem_firstPairStabilizer_iff_mixed_zero]
  constructor
  · rintro ⟨h₁₂, h₂₁⟩
    constructor
    · ext i j
      have h := h₁₂ ((blockIndexEquiv n).symm (Sum.inl i))
        ((blockIndexEquiv n).symm (Sum.inr j))
        (firstPair_preimage_left n i) (not_firstPair_preimage_right n j)
      simpa [blockMatrix] using h
    · ext i j
      have h := h₂₁ ((blockIndexEquiv n).symm (Sum.inr i))
        ((blockIndexEquiv n).symm (Sum.inl j))
        (not_firstPair_preimage_right n i) (firstPair_preimage_left n j)
      simpa [blockMatrix] using h
  · rintro ⟨h₁₂, h₂₁⟩
    constructor
    · intro i j hi hj
      obtain ⟨a, ha⟩ := (blockIndexEquiv_firstPair_iff n i).1 hi
      have hb : ∃ b : J n, blockIndexEquiv n j = Sum.inr b := by
        cases he : blockIndexEquiv n j with
        | inl a => exact False.elim (hj ((blockIndexEquiv_firstPair_iff n j).2 ⟨a, he⟩))
        | inr b => exact ⟨b, rfl⟩
      obtain ⟨b, hb⟩ := hb
      have hz := congrArg (fun M : Matrix (Fin 2) (J n) ℂ => M a b) h₁₂
      have hi' : i = (blockIndexEquiv n).symm (Sum.inl a) := by
        rw [← (blockIndexEquiv n).symm_apply_apply i, ha]
      have hj' : j = (blockIndexEquiv n).symm (Sum.inr b) := by
        rw [← (blockIndexEquiv n).symm_apply_apply j, hb]
      rw [hi', hj']
      simpa only [blockMatrix, Matrix.toBlocks₁₂, Matrix.reindex_apply,
        Matrix.zero_apply] using hz
    · intro i j hi hj
      obtain ⟨b, hb⟩ := (blockIndexEquiv_firstPair_iff n j).1 hj
      have ha : ∃ a : J n, blockIndexEquiv n i = Sum.inr a := by
        cases he : blockIndexEquiv n i with
        | inl b => exact False.elim (hi ((blockIndexEquiv_firstPair_iff n i).2 ⟨b, he⟩))
        | inr a => exact ⟨a, rfl⟩
      obtain ⟨a, ha⟩ := ha
      have hz := congrArg (fun M : Matrix (J n) (Fin 2) ℂ => M a b) h₂₁
      have hi' : i = (blockIndexEquiv n).symm (Sum.inr a) := by
        rw [← (blockIndexEquiv n).symm_apply_apply i, ha]
      have hj' : j = (blockIndexEquiv n).symm (Sum.inl b) := by
        rw [← (blockIndexEquiv n).symm_apply_apply j, hb]
      rw [hi', hj']
      simpa only [blockMatrix, Matrix.toBlocks₂₁, Matrix.reindex_apply,
        Matrix.zero_apply] using hz

/-- The matrix of an actual stabilizer element reconstructs exactly from
its two diagonal blocks, with no unproved block-structure premise. -/
theorem blockMatrix_eq_fromBlocks (n : ℕ) (u : G n)
    (hu : u ∈ firstPairStabilizer n) :
    blockMatrix n u =
      Matrix.fromBlocks (blockMatrix n u).toBlocks₁₁ 0 0
        (blockMatrix n u).toBlocks₂₂ := by
  obtain ⟨h₁₂, h₂₁⟩ := (mem_stabilizer_iff_block_off_diagonal_zero n u).1 hu
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks (blockMatrix n u)]
  rw [h₁₂, h₂₁]

end
end QuaternionicSymmetry.CompactSymplecticStabilizerDiagonal
