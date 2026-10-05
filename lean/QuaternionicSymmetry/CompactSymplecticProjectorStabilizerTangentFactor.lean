import QuaternionicSymmetry.CompactSymplecticProjectorBaseImaginaryRank

/-! Every actual projector-stabilizer derivative factors into the checked
first Sp(1)-block quaternion action and complementary Sp(n) action. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStabilizerTangentFactor

open Matrix Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseTangentRange
open CompactSymplecticProjectorBaseQuaternionAction
open CompactSymplecticProjectorIsotropyBlocks
open CompactSymplecticProjectorIsotropyUnits
open CompactSymplecticProjectorComplementAction
open CompactSymplecticStabilizerBlockPair
open CompactSymplecticStabilizerDiagonal
open CompactSymplecticClosedSubgroupSource
open CompactSymplecticHomogeneousAtlasSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section
set_option maxHeartbeats 1000000

private abbrev RModel (d : ℕ) := Fin d → ℝ

/-- The actual stabilizer differential, regarded as a real-linear
endomorphism of the true base manifold tangent. -/
def stabilizerTangentEnd
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (atlas : SmoothHomogeneousAtlas n d e q g)
    (u : firstPairStabilizer n) :
    letI := atlas.quotientCharts
    Module.End ℝ (TangentSpace 𝓘(ℝ, RModel q) (baseCoset n)) := by
  letI := atlas.quotientCharts
  exact (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
    (leftCosetAction n u.1) (baseCoset n)).toLinearMap

/-- The differential of an arbitrary actual stabilizer element is the
composition of its independently checked diagonal block derivatives. -/
theorem stabilizerTangentEnd_factor_blocks
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (atlas : SmoothHomogeneousAtlas n d e q g)
    (u : firstPairStabilizer n) :
    letI := atlas.quotientCharts
    stabilizerTangentEnd n d e q g atlas u =
      stabilizerTangentEnd n d e q g atlas
        (firstBlockLift n (blockPair n u).1) *
      stabilizerTangentEnd n d e q g atlas
        (complementLift n (blockPair n u).2) := by
  letI := atlas.quotientCharts
  ext v
  apply baseTangentUpperLinear_injective hDesc hImm n d e q g atlas
  apply Subtype.ext
  change ((baseTangentUpperLinear hDesc n d e q g atlas)
      (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
        (leftCosetAction n u.1) (baseCoset n) v)).1 =
    ((baseTangentUpperLinear hDesc n d e q g atlas)
      (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
        (leftCosetAction n (firstBlockLift n (blockPair n u).1).1) (baseCoset n)
        (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
          (leftCosetAction n (complementLift n (blockPair n u).2).1)
          (baseCoset n) v))).1
  rw [stabilizer_upperTangent_action hDesc n d e q g atlas u.1 u.2 v]
  rw [firstBlockLift_tangent hDesc n d e q g atlas (blockPair n u).1]
  rw [complementLift_tangent hDesc n d e q g atlas (blockPair n u).2 v]
  simp only [blockPair, Matrix.mul_assoc]

end
end QuaternionicSymmetry.CompactSymplecticProjectorStabilizerTangentFactor
