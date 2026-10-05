import QuaternionicSymmetry.CompactSymplecticStabilizerBlockPair

/-! Constructing the inverse block matrix from arbitrary independent
unitary-symplectic blocks. No classification or dimension result is used. -/

namespace QuaternionicSymmetry.CompactSymplecticStabilizerBlockSurjection

open Matrix CompactSymplecticHaar CompactSymplecticProjectiveQuotient
open CompactSymplecticStabilizerIndex CompactSymplecticStabilizerDiagonal
open CompactSymplecticStabilizerFormBlocks CompactSymplecticStabilizerBlockPair
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev J (n : ℕ) := Fin n ⊕ Fin n
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

def assemble (n : ℕ) (a : FirstBlockGroup)
    (b : CompactSymplecticHaar.Group n) :
    Matrix (Fin 2 ⊕ J n) (Fin 2 ⊕ J n) ℂ :=
  Matrix.fromBlocks (a.1.1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0
    (b.1.1 : Matrix (J n) (J n) ℂ)

theorem assemble_unitary (n : ℕ) (a : FirstBlockGroup)
    (b : CompactSymplecticHaar.Group n) :
    assemble n a b ∈ Matrix.unitaryGroup (Fin 2 ⊕ J n) ℂ := by
  classical
  have ha : (a.1.1 : Matrix (Fin 2) (Fin 2) ℂ) ∈
      Matrix.unitaryGroup (Fin 2) ℂ := a.1.property
  have hb : (b.1.1 : Matrix (J n) (J n) ℂ) ∈
      Matrix.unitaryGroup (J n) ℂ := b.1.property
  rw [Matrix.mem_unitaryGroup_iff'] at ha hb ⊢
  rw [Matrix.star_eq_conjTranspose] at ha hb
  rw [← Matrix.fromBlocks_one (l := Fin 2) (m := J n)]
  simp only [assemble, Matrix.star_eq_conjTranspose,
    Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  simp [Matrix.conjTranspose_zero, ha, hb]

theorem assemble_preserves_form (n : ℕ) (a : FirstBlockGroup)
    (b : CompactSymplecticHaar.Group n) :
    (assemble n a b)ᵀ * blockStandardJ n * assemble n a b =
      blockStandardJ n := by
  classical
  have ha : (a.1.1 : Matrix (Fin 2) (Fin 2) ℂ)ᵀ * firstBlockJ *
      (a.1.1 : Matrix (Fin 2) (Fin 2) ℂ) = firstBlockJ := a.2
  have hb : (b.1.1 : Matrix (J n) (J n) ℂ)ᵀ * standardJ n *
      (b.1.1 : Matrix (J n) (J n) ℂ) = standardJ n := b.2
  rw [blockStandardJ_eq_fromBlocks]
  simp only [assemble, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  simp [Matrix.transpose_zero, ha, hb]

/-- The inverse-reindexed assembled matrix on the original complex index. -/
def originalMatrix (n : ℕ) (a : FirstBlockGroup)
    (b : CompactSymplecticHaar.Group n) : Matrix (I n) (I n) ℂ :=
  (assemble n a b).reindex (blockIndexEquiv n).symm
    (blockIndexEquiv n).symm

theorem originalMatrix_reindexed (n : ℕ) (a : FirstBlockGroup)
    (b : CompactSymplecticHaar.Group n) :
    (originalMatrix n a b).reindex (blockIndexEquiv n)
      (blockIndexEquiv n) = assemble n a b := by
  simp [originalMatrix]

theorem originalMatrix_unitary (n : ℕ) (a : FirstBlockGroup)
    (b : CompactSymplecticHaar.Group n) :
    originalMatrix n a b ∈ Matrix.unitaryGroup (I n) ℂ := by
  classical
  have h := assemble_unitary n a b
  rw [Matrix.mem_unitaryGroup_iff'] at h ⊢
  have h' := congrArg (Matrix.reindexAlgEquiv ℂ ℂ
    (blockIndexEquiv n).symm) h
  rw [Matrix.reindexAlgEquiv_mul] at h'
  simpa only [Matrix.reindexAlgEquiv_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_reindex, map_one, originalMatrix] using h'

theorem originalMatrix_preserves_form (n : ℕ) (a : FirstBlockGroup)
    (b : CompactSymplecticHaar.Group n) :
    (originalMatrix n a b)ᵀ * standardJ (n + 1) *
      originalMatrix n a b = standardJ (n + 1) := by
  classical
  have h := assemble_preserves_form n a b
  have h' := congrArg (Matrix.reindexAlgEquiv ℂ ℂ
    (blockIndexEquiv n).symm) h
  rw [Matrix.reindexAlgEquiv_mul, Matrix.reindexAlgEquiv_mul] at h'
  simpa [Matrix.reindexAlgEquiv_apply, Matrix.transpose_reindex,
    originalMatrix, blockStandardJ, Matrix.reindex_apply] using h'

/-- Each pair of genuine compact-symplectic blocks assembles into a
genuine member of the projector stabilizer. -/
def fromBlockPair (n : ℕ) (p : FirstBlockGroup × CompactSymplecticHaar.Group n) :
    firstPairStabilizer n := by
  let U : Matrix.unitaryGroup (I n) ℂ :=
    ⟨originalMatrix n p.1 p.2, originalMatrix_unitary n p.1 p.2⟩
  let g : G n := ⟨U, originalMatrix_preserves_form n p.1 p.2⟩
  have hblock : blockMatrix n g = assemble n p.1 p.2 :=
    originalMatrix_reindexed n p.1 p.2
  have hK : g ∈ firstPairStabilizer n := by
    apply (mem_stabilizer_iff_block_off_diagonal_zero n g).2
    rw [hblock]
    simp [assemble]
  exact ⟨g, hK⟩

theorem blockPair_fromBlockPair (n : ℕ)
    (p : FirstBlockGroup × CompactSymplecticHaar.Group n) :
    blockPair n (fromBlockPair n p) = p := by
  apply Prod.ext
  · apply Subtype.ext
    apply Subtype.ext
    change (blockMatrix n (fromBlockPair n p).1).toBlocks₁₁ = p.1.1.1
    rw [show blockMatrix n (fromBlockPair n p).1 = assemble n p.1 p.2 from
      originalMatrix_reindexed n p.1 p.2]
    rfl
  · apply Subtype.ext
    apply Subtype.ext
    change (blockMatrix n (fromBlockPair n p).1).toBlocks₂₂ = p.2.1.1
    rw [show blockMatrix n (fromBlockPair n p).1 = assemble n p.1 p.2 from
      originalMatrix_reindexed n p.1 p.2]
    rfl

theorem blockPairHom_surjective (n : ℕ) :
    Function.Surjective (blockPairHom n) := by
  intro p
  exact ⟨fromBlockPair n p, blockPair_fromBlockPair n p⟩

/-- The exact, internally proved block-product decomposition of the actual
projector stabilizer. The first factor is the standard two-dimensional
alternating-form stabilizer in reindexed coordinates. -/
def stabilizerBlockProductEquiv (n : ℕ) :
    firstPairStabilizer n ≃*
      FirstBlockGroup × CompactSymplecticHaar.Group n :=
  MulEquiv.ofBijective (blockPairHom n)
    ⟨blockPairHom_injective n, blockPairHom_surjective n⟩

end
end QuaternionicSymmetry.CompactSymplecticStabilizerBlockSurjection
