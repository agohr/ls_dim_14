import QuaternionicSymmetry.CompactSymplecticProjectorTwistorGroupFiberLinear
import QuaternionicSymmetry.CompactSymplecticProjectorFirstBlockHopfAction

/-! The actual projector stabilizer matrix preserves the embedded first
complex two-plane and acts there by its checked first Sp(1) block. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStabilizerFiberLinear

open Matrix CompactSymplecticProjectorTwistorGroupFiberLinear
open CompactSymplecticStabilizerBlockPair
open CompactSymplecticStabilizerDiagonal
open CompactSymplecticStabilizerIndex
open CompactSymplecticStabilizerBlocks
open CompactSymplecticProjectorFirstBlockHopfAction

noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)
private abbrev K (n : ℕ) :=
  CompactSymplecticProjectiveQuotient.firstPairStabilizer n

theorem stabilizer_mulVec_firstPair (n : ℕ) (k : K n)
    (z : Fin 2 → ℂ) :
    (k.1.1.1 : Matrix (I n) (I n) ℂ) *ᵥ firstPairEmbedding n z =
      firstPairEmbedding n
        (((blockPair n k).1.1.1 : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ z) := by
  classical
  have hsum (i : I n) :
      ((k.1.1.1 : Matrix (I n) (I n) ℂ) *ᵥ firstPairEmbedding n z) i =
      (k.1.1.1 : Matrix (I n) (I n) ℂ) i (Sum.inl 0) * z 0 +
      (k.1.1.1 : Matrix (I n) (I n) ℂ) i (Sum.inr 0) * z 1 := by
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Fin.sum_univ_succ, firstPairEmbedding]
  have hzero := (mem_firstPairStabilizer_iff_mixed_zero n k.1).mp k.2
  funext i
  rw [hsum]
  cases i with
  | inl j =>
      refine Fin.cases ?_ (fun t => ?_) j
      · simp [firstPairEmbedding, Matrix.mulVec, dotProduct,
          Fin.sum_univ_succ, blockPair, blockMatrix,
          blockIndexEquiv, Matrix.toBlocks₁₁, Matrix.reindex_apply,
          Fin.cases_succ]
      · have hz0 := hzero.2 (Sum.inl t.succ) (Sum.inl 0)
          (by simp [InFirstPair]) (by simp [InFirstPair])
        have hz1 := hzero.2 (Sum.inl t.succ) (Sum.inr 0)
          (by simp [InFirstPair]) (by simp [InFirstPair])
        simp [firstPairEmbedding, hz0, hz1]
  | inr j =>
      refine Fin.cases ?_ (fun t => ?_) j
      · have hidx :
            Fin.cases (Sum.inl (0 : Fin (n + 1)))
              (fun _ : Fin 1 => Sum.inr (0 : Fin (n + 1))) (1 : Fin 2) =
                (Sum.inr (0 : Fin (n + 1)) : I n) := by
          change Fin.cases (Sum.inl (0 : Fin (n + 1)))
            (fun _ : Fin 1 => Sum.inr (0 : Fin (n + 1)))
              ((0 : Fin 1).succ) = Sum.inr 0
          exact Fin.cases_succ _
        simp [firstPairEmbedding, Matrix.mulVec, dotProduct,
          Fin.sum_univ_succ, blockPair, blockMatrix,
          blockIndexEquiv, Matrix.toBlocks₁₁, Matrix.reindex_apply]
          <;> simpa only [hidx]
      · have hz0 := hzero.2 (Sum.inr t.succ) (Sum.inl 0)
          (by simp [InFirstPair]) (by simp [InFirstPair])
        have hz1 := hzero.2 (Sum.inr t.succ) (Sum.inr 0)
          (by simp [InFirstPair]) (by simp [InFirstPair])
        simp [firstPairEmbedding, hz0, hz1]

end
end QuaternionicSymmetry.CompactSymplecticProjectorStabilizerFiberLinear
