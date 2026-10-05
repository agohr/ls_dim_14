import QuaternionicSymmetry.CompactSymplecticStabilizerSymplecticBlocks

/-! The actual stabilizer embeds into the product of compact symplectic
groups carried by the first quaternionic pair and its complement. The
first factor is expressed in the exactly reindexed `Fin 2` coordinates;
identifying this with `Group 1` is a separate finite-index equivalence. -/

namespace QuaternionicSymmetry.CompactSymplecticStabilizerBlockPair

open Matrix CompactSymplecticHaar CompactSymplecticProjectiveQuotient
open CompactSymplecticStabilizerDiagonal
open CompactSymplecticStabilizerUnitaryBlocks
open CompactSymplecticStabilizerFormBlocks
open CompactSymplecticStabilizerSymplecticBlocks
noncomputable section

private abbrev J (n : ℕ) := Fin n ⊕ Fin n
private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)
private abbrev K (n : ℕ) := firstPairStabilizer n

/-- The genuine two-dimensional compact symplectic block, with no
dimension convention imposed by a source theorem. -/
abbrev FirstBlockGroup := CompactSymplecticHaar.stabilizer firstBlockJ

/-- Both restrictions of a stabilizer matrix are themselves unitary and
preserve their actual alternating forms. -/
def blockPair (n : ℕ) (u : K n) : FirstBlockGroup × CompactSymplecticHaar.Group n := by
  let hunit := unitary_diagonal_blocks n u.1 u.2
  let hsymp := symplectic_diagonal_blocks n u.1 u.2
  exact (⟨⟨(blockMatrix n u.1).toBlocks₁₁, hunit.1⟩, hsymp.1⟩,
    ⟨⟨(blockMatrix n u.1).toBlocks₂₂, hunit.2⟩, hsymp.2⟩)

theorem blockPair_injective (n : ℕ) : Function.Injective (blockPair n) := by
  intro u v huv
  have hfirst := congrArg (fun p : FirstBlockGroup × CompactSymplecticHaar.Group n =>
    (p.1.1 : Matrix (Fin 2) (Fin 2) ℂ)) huv
  have hsecond := congrArg (fun p : FirstBlockGroup × CompactSymplecticHaar.Group n =>
    (p.2.1 : Matrix (J n) (J n) ℂ)) huv
  change (blockMatrix n u.1).toBlocks₁₁ =
    (blockMatrix n v.1).toBlocks₁₁ at hfirst
  change (blockMatrix n u.1).toBlocks₂₂ =
    (blockMatrix n v.1).toBlocks₂₂ at hsecond
  have hmat : blockMatrix n u.1 = blockMatrix n v.1 := by
    rw [blockMatrix_eq_fromBlocks n u.1 u.2,
      blockMatrix_eq_fromBlocks n v.1 v.2, hfirst, hsecond]
  have horig : (u.1.1.1 : Matrix (I n) (I n) ℂ) =
      (v.1.1.1 : Matrix (I n) (I n) ℂ) := by
    have h := congrArg (Matrix.reindexAlgEquiv ℂ ℂ
      (CompactSymplecticStabilizerIndex.blockIndexEquiv n).symm) hmat
    simpa [blockMatrix] using h
  apply Subtype.ext
  apply Subtype.ext
  exact Subtype.ext horig

private theorem blockMatrix_mul (n : ℕ) (u v : K n) :
    blockMatrix n (u * v).1 = blockMatrix n u.1 * blockMatrix n v.1 := by
  classical
  change (Matrix.reindexAlgEquiv ℂ ℂ
      (CompactSymplecticStabilizerIndex.blockIndexEquiv n))
      ((u.1.1.1 : Matrix (I n) (I n) ℂ) * v.1.1.1) =
    (Matrix.reindexAlgEquiv ℂ ℂ
      (CompactSymplecticStabilizerIndex.blockIndexEquiv n)) u.1.1.1 *
    (Matrix.reindexAlgEquiv ℂ ℂ
      (CompactSymplecticStabilizerIndex.blockIndexEquiv n)) v.1.1.1
  exact map_mul (Matrix.reindexAlgEquiv ℂ ℂ
    (CompactSymplecticStabilizerIndex.blockIndexEquiv n)) _ _

theorem blockPair_upper_mul (n : ℕ) (u v : K n) :
    (blockMatrix n (u * v).1).toBlocks₁₁ =
      (blockMatrix n u.1).toBlocks₁₁ *
        (blockMatrix n v.1).toBlocks₁₁ := by
  rw [blockMatrix_mul]
  rw [blockMatrix_eq_fromBlocks n u.1 u.2,
    blockMatrix_eq_fromBlocks n v.1 v.2]
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, Matrix.toBlocks_fromBlocks₁₁]

theorem blockPair_lower_mul (n : ℕ) (u v : K n) :
    (blockMatrix n (u * v).1).toBlocks₂₂ =
      (blockMatrix n u.1).toBlocks₂₂ *
        (blockMatrix n v.1).toBlocks₂₂ := by
  rw [blockMatrix_mul]
  rw [blockMatrix_eq_fromBlocks n u.1 u.2,
    blockMatrix_eq_fromBlocks n v.1 v.2]
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, Matrix.toBlocks_fromBlocks₂₂]

theorem blockPair_one (n : ℕ) : blockPair n 1 = 1 := by
  classical
  apply Prod.ext
  · apply Subtype.ext
    apply Subtype.ext
    change (blockMatrix n (1 : G n)).toBlocks₁₁ = 1
    have h : blockMatrix n (1 : G n) = 1 := by
      change (Matrix.reindexAlgEquiv ℂ ℂ
        (CompactSymplecticStabilizerIndex.blockIndexEquiv n)) 1 = 1
      exact map_one _
    rw [h, ← Matrix.fromBlocks_one (l := Fin 2) (m := J n)]
    rfl
  · apply Subtype.ext
    apply Subtype.ext
    change (blockMatrix n (1 : G n)).toBlocks₂₂ = 1
    have h : blockMatrix n (1 : G n) = 1 := by
      change (Matrix.reindexAlgEquiv ℂ ℂ
        (CompactSymplecticStabilizerIndex.blockIndexEquiv n)) 1 = 1
      exact map_one _
    rw [h, ← Matrix.fromBlocks_one (l := Fin 2) (m := J n)]
    rfl

theorem blockPair_mul (n : ℕ) (u v : K n) :
    blockPair n (u * v) = blockPair n u * blockPair n v := by
  apply Prod.ext
  · apply Subtype.ext
    apply Subtype.ext
    exact blockPair_upper_mul n u v
  · apply Subtype.ext
    apply Subtype.ext
    exact blockPair_lower_mul n u v

/-- The block restriction is an actual injective group homomorphism. -/
def blockPairHom (n : ℕ) :
    K n →* FirstBlockGroup × CompactSymplecticHaar.Group n where
  toFun := blockPair n
  map_one' := blockPair_one n
  map_mul' := blockPair_mul n

theorem blockPairHom_injective (n : ℕ) :
    Function.Injective (blockPairHom n) := blockPair_injective n

end
end QuaternionicSymmetry.CompactSymplecticStabilizerBlockPair
