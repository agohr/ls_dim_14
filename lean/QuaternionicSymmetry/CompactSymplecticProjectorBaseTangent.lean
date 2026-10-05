import QuaternionicSymmetry.CompactSymplecticProjectorPointSymmetry
import QuaternionicSymmetry.CompactSymplecticStabilizerFormBlocks

/-! Concrete first-pair/complement matrix coordinates for the genuine
projector tangent image. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorBaseTangent

open Matrix Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbit
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticStabilizerIndex
open CompactSymplecticProjectorTangentConstraints
open CompactSymplecticClosedSubgroupSource
open CompactSymplecticHomogeneousAtlasSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section
set_option maxHeartbeats 1000000

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev J (n : ℕ) := Fin n ⊕ Fin n
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ
private abbrev BlockMat (n : ℕ) := Matrix (Fin 2 ⊕ J n) (Fin 2 ⊕ J n) ℂ
private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

/-- The identity coset is the base projector point. -/
def baseCoset (n : ℕ) : ProjectiveCarrier n :=
  ((1 : G n) : ProjectiveCarrier n)

theorem baseCoset_projector (n : ℕ) :
    quotientOrbitProjector n (baseCoset n) = firstPairProjector n := by
  simp [baseCoset, quotientOrbitProjector_mk, orbitProjector]

/-- The same explicit reindexing as the checked stabilizer product. -/
def baseBlockMatrix (n : ℕ) (X : Mat n) : BlockMat n :=
  X.reindex (blockIndexEquiv n) (blockIndexEquiv n)

private theorem fin_cases_one {α : Type*} (a b : α) :
    Fin.cases a (fun _ : Fin 1 => b) (1 : Fin 2) = b := by
  change Fin.cases a (fun _ : Fin 1 => b) ((0 : Fin 1).succ) = b
  rfl

/-- The distinguished quaternionic-line projector is exactly the first
diagonal block in these coordinates. -/
theorem baseBlockProjector (n : ℕ) :
    baseBlockMatrix n (firstPairProjector n) =
      Matrix.fromBlocks (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0
        (0 : Matrix (J n) (J n) ℂ) := by
  classical
  ext (i | i) (j | j)
  · fin_cases i <;> fin_cases j <;>
      simp [baseBlockMatrix, blockIndexEquiv, firstPairProjector,
        Matrix.reindex_apply, Matrix.fromBlocks,
        fin_cases_one]
  · fin_cases i <;> rcases j with j | j <;>
      simp [baseBlockMatrix, blockIndexEquiv, firstPairProjector,
        Matrix.reindex_apply, Matrix.fromBlocks,
        fin_cases_one, (Fin.succ_ne_zero j).symm]
  · rcases i with i | i <;> fin_cases j <;>
      simp [baseBlockMatrix, blockIndexEquiv, firstPairProjector,
        Matrix.reindex_apply, Matrix.fromBlocks,
        fin_cases_one]
  · rcases i with i | i <;> rcases j with j | j <;>
      simp [baseBlockMatrix, blockIndexEquiv, firstPairProjector,
        Matrix.reindex_apply, Matrix.fromBlocks, Matrix.diagonal_apply]

/-- The linearized idempotency equation forces both diagonal blocks to
vanish in the concrete first-pair/complement splitting. -/
theorem baseBlock_diagonal_zero (n : ℕ) (X : Mat n)
    (hX : firstPairProjector n * X + X * firstPairProjector n = X) :
    (baseBlockMatrix n X).toBlocks₁₁ = 0 ∧
      (baseBlockMatrix n X).toBlocks₂₂ = 0 := by
  let Y := baseBlockMatrix n X
  have hRe := congrArg
    (Matrix.reindexAlgEquiv ℂ ℂ (blockIndexEquiv n)) hX
  simp only [map_add, map_mul] at hRe
  change (baseBlockMatrix n (firstPairProjector n)) * Y +
    Y * (baseBlockMatrix n (firstPairProjector n)) = Y at hRe
  rw [baseBlockProjector] at hRe
  have hDecomp : Y = Matrix.fromBlocks Y.toBlocks₁₁ Y.toBlocks₁₂
      Y.toBlocks₂₁ Y.toBlocks₂₂ := (Matrix.fromBlocks_toBlocks Y).symm
  rw [hDecomp] at hRe
  simp only [Matrix.fromBlocks_multiply, Matrix.fromBlocks_add,
    Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add] at hRe
  constructor
  · have h := congrArg Matrix.toBlocks₁₁ hRe
    simp only [Matrix.toBlocks_fromBlocks₁₁] at h
    exact add_eq_right.mp h
  · have h := congrArg Matrix.toBlocks₂₂ hRe
    simpa only [Matrix.toBlocks_fromBlocks₂₂] using h.symm

/-- The lower mixed block of a reindexed Hermitian matrix is the adjoint
of its upper mixed block. -/
theorem baseBlock_lower_eq_adjoint (n : ℕ) (X : Mat n)
    (hSelf : Xᴴ = X) :
    (baseBlockMatrix n X).toBlocks₂₁ =
      (baseBlockMatrix n X).toBlocks₁₂ᴴ := by
  have hY : (baseBlockMatrix n X)ᴴ = baseBlockMatrix n X := by
    simp only [baseBlockMatrix, Matrix.conjTranspose_reindex, hSelf]
  ext i j
  have h := congrArg (fun Y : BlockMat n => Y (Sum.inr i) (Sum.inl j)) hY
  simpa only [Matrix.toBlocks₂₁, Matrix.toBlocks₁₂,
    Matrix.conjTranspose_apply] using h.symm

/-- Hermitian solutions of the linearized projector equation are exactly
off-diagonal matrices, with the lower block determined by the upper. -/
theorem baseBlock_eq_offDiagonal (n : ℕ) (X : Mat n)
    (hSelf : Xᴴ = X)
    (hPeirce : firstPairProjector n * X + X * firstPairProjector n = X) :
    baseBlockMatrix n X =
      Matrix.fromBlocks 0 (baseBlockMatrix n X).toBlocks₁₂
        (baseBlockMatrix n X).toBlocks₁₂ᴴ 0 := by
  have hdiag := baseBlock_diagonal_zero n X hPeirce
  have hlower := baseBlock_lower_eq_adjoint n X hSelf
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks (baseBlockMatrix n X)]
  rw [hdiag.1, hdiag.2, hlower]

/-- The actual differential image at the identity coset has literally zero
two diagonal blocks after the checked first-pair reindexing. -/
theorem base_tangent_diagonal_zero
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) :
    letI := a.quotientCharts
    ∀ (v : TangentSpace 𝓘(ℝ, RModel q) (baseCoset n)),
      let X : Mat n := mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) (baseCoset n) v
      (baseBlockMatrix n X).toBlocks₁₁ = 0 ∧
        (baseBlockMatrix n X).toBlocks₂₂ = 0 := by
  letI := a.quotientCharts
  intro v
  apply baseBlock_diagonal_zero
  simpa only [baseCoset_projector] using
    tangent_projector_offDiagonal hDesc n d e q g a (baseCoset n) v

/-- Every genuine tangent vector at the identity coset has the explicit
Hermitian off-diagonal block form. -/
theorem base_tangent_eq_offDiagonal
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) :
    letI := a.quotientCharts
    ∀ (v : TangentSpace 𝓘(ℝ, RModel q) (baseCoset n)),
      let X : Mat n := mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) (baseCoset n) v
      baseBlockMatrix n X =
        Matrix.fromBlocks 0 (baseBlockMatrix n X).toBlocks₁₂
          (baseBlockMatrix n X).toBlocks₁₂ᴴ 0 := by
  letI := a.quotientCharts
  intro v
  apply baseBlock_eq_offDiagonal
  · exact tangent_projector_selfAdjoint hDesc n d e q g a (baseCoset n) v
  · simpa only [baseCoset_projector] using
      tangent_projector_offDiagonal hDesc n d e q g a (baseCoset n) v

end
end QuaternionicSymmetry.CompactSymplecticProjectorBaseTangent
