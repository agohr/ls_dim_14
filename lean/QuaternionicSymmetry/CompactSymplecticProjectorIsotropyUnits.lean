import QuaternionicSymmetry.CompactSymplecticProjectorFirstBlockUnits

/-! The explicitly constructed Sp(1) units act on the genuine base
projector tangent by the checked quaternionic row formulas. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorIsotropyUnits

open Matrix Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseTangentRange
open CompactSymplecticProjectorIsotropyBlocks
open CompactSymplecticProjectorFirstBlockUnits
open CompactSymplecticStabilizerBlockSurjection
open CompactSymplecticStabilizerBlockPair
open CompactSymplecticStabilizerDiagonal
open CompactSymplecticStabilizerIndex
open CompactSymplecticClosedSubgroupSource
open CompactSymplecticHomogeneousAtlasSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

/-- The actual Sp(n+1) element with prescribed first quaternionic-line
block and identity complementary block. -/
def firstBlockLift (n : ℕ) (A : FirstBlockGroup) :
    firstPairStabilizer n := fromBlockPair n (A, 1)

theorem firstBlockLift_upper (n : ℕ) (A : FirstBlockGroup) :
    (blockMatrix n (firstBlockLift n A).1).toBlocks₁₁ = A.1.1 := by
  have h := congrArg (fun p : FirstBlockGroup × CompactSymplecticHaar.Group n =>
    (p.1.1.1 : Matrix (Fin 2) (Fin 2) ℂ))
    (blockPair_fromBlockPair n (A, 1))
  exact h

theorem firstBlockLift_lower (n : ℕ) (A : FirstBlockGroup) :
    (blockMatrix n (firstBlockLift n A).1).toBlocks₂₂ = 1 := by
  have h := congrArg (fun p : FirstBlockGroup × CompactSymplecticHaar.Group n =>
    (p.2.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ))
    (blockPair_fromBlockPair n (A, 1))
  exact h

/-- Exact upper-block effect of the actual first-block isotropy element
on the true manifold derivative. -/
theorem firstBlockLift_tangent
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (A : FirstBlockGroup) :
    letI := a.quotientCharts
    ∀ v : TangentSpace 𝓘(ℝ, RModel q) (baseCoset n),
      ((baseTangentUpperLinear hDesc n d e q g a)
        (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
          (leftCosetAction n (firstBlockLift n A).1) (baseCoset n) v)).1 =
        (A.1.1 : Matrix (Fin 2) (Fin 2) ℂ) *
          ((baseTangentUpperLinear hDesc n d e q g a) v).1 := by
  letI := a.quotientCharts
  intro v
  have h := stabilizer_upperTangent_action hDesc n d e q g a
    (firstBlockLift n A).1 (firstBlockLift n A).2 v
  rw [firstBlockLift_upper, firstBlockLift_lower,
    Matrix.conjTranspose_one, Matrix.mul_one] at h
  exact h

end
end QuaternionicSymmetry.CompactSymplecticProjectorIsotropyUnits
