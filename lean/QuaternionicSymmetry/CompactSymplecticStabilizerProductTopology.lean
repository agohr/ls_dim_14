import QuaternionicSymmetry.CompactSymplecticStabilizerProduct
import Mathlib.Topology.Homeomorph.Lemmas

/-! The matrix block-product identification is compatible with the actual
compact-group topology, not merely an abstract group isomorphism. -/

namespace QuaternionicSymmetry.CompactSymplecticStabilizerProductTopology

open Matrix CompactSymplecticHaar CompactSymplecticProjectiveQuotient
open CompactSymplecticStabilizerIndex CompactSymplecticStabilizerDiagonal
open CompactSymplecticStabilizerBlockPair
open CompactSymplecticStabilizerBlockSurjection
open CompactSymplecticFirstBlockGroup
open CompactSymplecticStabilizerProduct
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev J (n : ℕ) := Fin n ⊕ Fin n
private abbrev K (n : ℕ) := firstPairStabilizer n

private theorem continuous_rawMatrix (n : ℕ) :
    Continuous (fun u : K n => (u.1.1.1 : Matrix (I n) (I n) ℂ)) := by
  exact (continuous_subtype_val : Continuous
    (fun q : Matrix.unitaryGroup (I n) ℂ => (q.1 : Matrix (I n) (I n) ℂ))).comp
    ((continuous_subtype_val : Continuous
      (fun g : CompactSymplecticHaar.Group (n + 1) =>
        (g.1 : Matrix.unitaryGroup (I n) ℂ))).comp
      (continuous_subtype_val : Continuous
        (fun u : K n => (u.1 : CompactSymplecticHaar.Group (n + 1)))))

theorem continuous_blockMatrix (n : ℕ) :
    Continuous (fun u : K n => blockMatrix n u.1) := by
  exact (continuous_rawMatrix n).matrix_reindex
    (blockIndexEquiv n) (blockIndexEquiv n)

theorem continuous_blockPair (n : ℕ) :
    Continuous (blockPair n) := by
  have h := continuous_blockMatrix n
  apply Continuous.prodMk
  · apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    simpa only [Matrix.toBlocks₁₁] using
      h.matrix_submatrix Sum.inl Sum.inl
  · apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    simpa only [Matrix.toBlocks₂₂] using
      h.matrix_submatrix Sum.inr Sum.inr

private theorem continuous_firstBlock_inverse :
    Continuous (fun u : FirstBlockGroup => firstBlockGroupEquiv.symm u) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  have h : Continuous (fun u : FirstBlockGroup =>
      (u.1.1 : Matrix (Fin 2) (Fin 2) ℂ)) :=
    (continuous_subtype_val : Continuous
      (fun q : Matrix.unitaryGroup (Fin 2) ℂ =>
        (q.1 : Matrix (Fin 2) (Fin 2) ℂ))).comp
      (continuous_subtype_val : Continuous
        (fun u : FirstBlockGroup => (u.1 : Matrix.unitaryGroup (Fin 2) ℂ)))
  exact h.matrix_reindex
    CompactSymplecticFirstBlockCoordinates.pairIndexEquiv.symm
    CompactSymplecticFirstBlockCoordinates.pairIndexEquiv.symm

/-- The concrete matrix stabilizer and the actual two compact symplectic
factors are homeomorphic. Lie-chart compatibility remains to be checked. -/
def stabilizerProductHomeomorph (n : ℕ) :
    firstPairStabilizer n ≃ₜ
      CompactSymplecticHaar.Group 1 × CompactSymplecticHaar.Group n := by
  let e := stabilizerProductEquiv n
  have he : Continuous e := by
    have hfirst : Continuous (fun u : K n =>
        firstBlockGroupEquiv.symm (blockPair n u).1) :=
      continuous_firstBlock_inverse.comp
        (continuous_fst.comp (continuous_blockPair n))
    have hsecond : Continuous (fun u : K n => (blockPair n u).2) :=
      continuous_snd.comp (continuous_blockPair n)
    change Continuous (fun u : K n =>
      (firstBlockGroupEquiv.symm (blockPair n u).1, (blockPair n u).2))
    exact hfirst.prodMk hsecond
  letI : CompactSpace (K n) :=
    isCompact_iff_compactSpace.mp (isClosed_firstPairStabilizer n).isCompact
  exact Continuous.homeoOfEquivCompactToT2 he

end
end QuaternionicSymmetry.CompactSymplecticStabilizerProductTopology
