import QuaternionicSymmetry.CompactSymplecticProjectorBaseTangentRange

/-! At the actual base projector, every quaternionic-Hermitian solution
of the linearized idempotency equation is attained by the genuine
quotient-projector differential. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorBaseTangentCharacterization

open Matrix Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorQuaternionicBlock
open CompactSymplecticProjectorBaseTangentRange
open CompactSymplecticProjectorQuaternionicUpperLinear
open CompactSymplecticStabilizerIndex
open CompactSymplecticClosedSubgroupSource
open CompactSymplecticHomogeneousAtlasSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ
private abbrev RModel (d : ℕ) := Fin d → ℝ

theorem base_quaternionicHermitian_tangent_surjective
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (X : Mat n) (hSelf : Xᴴ = X)
    (hPeirce : firstPairProjector n * X + X * firstPairProjector n = X)
    (hQuat : X * CompactSymplecticHaar.standardJ (n + 1) =
      CompactSymplecticHaar.standardJ (n + 1) * X.map star) :
    letI := a.quotientCharts
    ∃ v : TangentSpace 𝓘(ℝ,RModel q) (baseCoset n),
      mfderiv 𝓘(ℝ,RModel q) 𝓘(ℝ,Mat n)
        (quotientOrbitProjector n) (baseCoset n) v = X := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  let B := (baseBlockMatrix n X).toBlocks₁₂
  have hB : B ∈ upperSubmodule n :=
    (mem_upperSubmodule_iff n B).2 (upperBlock_quaternionic n X hQuat)
  obtain ⟨v, hv⟩ := baseTangentUpperLinear_surjective
    hDesc hImm n d e q g a hq ⟨B, hB⟩
  refine ⟨v, ?_⟩
  have hvB : (baseBlockMatrix n
      (mfderiv 𝓘(ℝ,RModel q) 𝓘(ℝ,Mat n)
        (quotientOrbitProjector n) (baseCoset n) v)).toBlocks₁₂ = B := by
    exact congrArg Subtype.val hv
  have hV := base_tangent_eq_offDiagonal hDesc n d e q g a v
  have hX := baseBlock_eq_offDiagonal n X hSelf hPeirce
  have heq : baseBlockMatrix n
      (mfderiv 𝓘(ℝ,RModel q) 𝓘(ℝ,Mat n)
        (quotientOrbitProjector n) (baseCoset n) v) = baseBlockMatrix n X := by
    rw [hV, hX, hvB]
  exact (Matrix.reindexAlgEquiv ℂ ℂ (blockIndexEquiv n)).injective heq

end
end QuaternionicSymmetry.CompactSymplecticProjectorBaseTangentCharacterization
