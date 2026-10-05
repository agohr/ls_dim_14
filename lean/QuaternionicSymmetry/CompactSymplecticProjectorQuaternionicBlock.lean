import QuaternionicSymmetry.CompactSymplecticProjectorBaseTangent

/-! The explicit quaternionic relation on the upper off-diagonal block
of a genuine projector tangent vector. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorQuaternionicBlock

open Matrix Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorTangentConstraints
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticStabilizerIndex
open CompactSymplecticStabilizerFormBlocks
open CompactSymplecticClosedSubgroupSource
open CompactSymplecticHomogeneousAtlasSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section
set_option maxHeartbeats 1000000

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev J (n : ℕ) := Fin n ⊕ Fin n
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ
private abbrev RModel (d : ℕ) := Fin d → ℝ

/-- The upper mixed block obeys the quaternionic anti-linear law.
This is an equality on actual complex matrix blocks, not a dimension count. -/
theorem upperBlock_quaternionic (n : ℕ) (X : Mat n)
    (hQuat : X * CompactSymplecticHaar.standardJ (n + 1) =
      CompactSymplecticHaar.standardJ (n + 1) * X.map star) :
    (baseBlockMatrix n X).toBlocks₁₂ * CompactSymplecticHaar.standardJ n =
      firstBlockJ * (baseBlockMatrix n X).toBlocks₁₂.map star := by
  let Y := baseBlockMatrix n X
  have hRe := congrArg
    (Matrix.reindexAlgEquiv ℂ ℂ (blockIndexEquiv n)) hQuat
  simp only [map_mul] at hRe
  change Y * blockStandardJ n = blockStandardJ n * Y.map star at hRe
  rw [blockStandardJ_eq_fromBlocks] at hRe
  have hDecomp : Y = Matrix.fromBlocks Y.toBlocks₁₁ Y.toBlocks₁₂
      Y.toBlocks₂₁ Y.toBlocks₂₂ := (Matrix.fromBlocks_toBlocks Y).symm
  rw [hDecomp] at hRe
  have h := congrArg Matrix.toBlocks₁₂ hRe
  simpa only [Matrix.fromBlocks_multiply, Matrix.fromBlocks_map,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.toBlocks_fromBlocks₁₂] using h

/-- Every true tangent at the identity coset has a quaternionic upper
mixed block in addition to the Hermitian off-diagonal normal form. -/
theorem base_tangent_upper_quaternionic
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) :
    letI := a.quotientCharts
    ∀ (v : TangentSpace 𝓘(ℝ, RModel q) (baseCoset n)),
      let X : Mat n := mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) (baseCoset n) v
      (baseBlockMatrix n X).toBlocks₁₂ * CompactSymplecticHaar.standardJ n =
        firstBlockJ * (baseBlockMatrix n X).toBlocks₁₂.map star := by
  letI := a.quotientCharts
  intro v
  apply upperBlock_quaternionic
  exact tangent_projector_commutes_quaternionicJ hDesc n d e q g a (baseCoset n) v

end
end QuaternionicSymmetry.CompactSymplecticProjectorQuaternionicBlock
