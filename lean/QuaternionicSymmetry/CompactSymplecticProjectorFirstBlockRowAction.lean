import QuaternionicSymmetry.CompactSymplecticProjectorComplementAction

/-! Formula for an arbitrary actual Sp(1) isotropy element on the complete
quaternionic tangent row. This prepares the rank-three-span calculation. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorFirstBlockRowAction

open Matrix Manifold
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseTangentRange
open CompactSymplecticProjectorIsotropyUnits
open CompactSymplecticProjectorQuaternionicRow
open CompactSymplecticProjectorQuaternionicUpperLinear
open CompactSymplecticStabilizerBlockPair
open CompactSymplecticClosedSubgroupSource
open CompactSymplecticHomogeneousAtlasSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ

/-- On the first summand, an arbitrary actual first-block Sp(1) element
acts as `a·b + b₁·(-conj b₂)` with its literal matrix entries. -/
theorem firstBlock_tangent_row_inl
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (A : FirstBlockGroup) :
    letI := a.quotientCharts
    ∀ (v : TangentSpace 𝓘(ℝ, RModel q) (baseCoset n)) (j : Fin n),
      ((baseTangentUpperLinear hDesc n d e q g a)
        (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
          (leftCosetAction n (firstBlockLift n A).1) (baseCoset n) v)).1
            0 (Sum.inl j) =
        A.1.1 0 0 * ((baseTangentUpperLinear hDesc n d e q g a) v).1
          0 (Sum.inl j) -
        A.1.1 0 1 * star (((baseTangentUpperLinear hDesc n d e q g a) v).1
          0 (Sum.inr j)) := by
  letI := a.quotientCharts
  intro v j
  rw [firstBlockLift_tangent hDesc n d e q g a A v]
  let B := ((baseTangentUpperLinear hDesc n d e q g a) v).1
  have hB : B * CompactSymplecticHaar.standardJ n =
      CompactSymplecticStabilizerFormBlocks.firstBlockJ * B.map star :=
    (mem_upperSubmodule_iff n B).1
      (baseTangentUpperLinear hDesc n d e q g a v).2
  change (A.1.1 * B) 0 (Sum.inl j) =
    A.1.1 0 0 * B 0 (Sum.inl j) -
      A.1.1 0 1 * star (B 0 (Sum.inr j))
  rw [Matrix.mul_apply, Fin.sum_univ_two,
    quaternionic_row_one_inl n B hB j]
  ring

/-- The second summand has the complementary quaternionic sign. -/
theorem firstBlock_tangent_row_inr
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (A : FirstBlockGroup) :
    letI := a.quotientCharts
    ∀ (v : TangentSpace 𝓘(ℝ, RModel q) (baseCoset n)) (j : Fin n),
      ((baseTangentUpperLinear hDesc n d e q g a)
        (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
          (leftCosetAction n (firstBlockLift n A).1) (baseCoset n) v)).1
            0 (Sum.inr j) =
        A.1.1 0 0 * ((baseTangentUpperLinear hDesc n d e q g a) v).1
          0 (Sum.inr j) +
        A.1.1 0 1 * star (((baseTangentUpperLinear hDesc n d e q g a) v).1
          0 (Sum.inl j)) := by
  letI := a.quotientCharts
  intro v j
  rw [firstBlockLift_tangent hDesc n d e q g a A v]
  let B := ((baseTangentUpperLinear hDesc n d e q g a) v).1
  have hB : B * CompactSymplecticHaar.standardJ n =
      CompactSymplecticStabilizerFormBlocks.firstBlockJ * B.map star :=
    (mem_upperSubmodule_iff n B).1
      (baseTangentUpperLinear hDesc n d e q g a v).2
  change (A.1.1 * B) 0 (Sum.inr j) =
    A.1.1 0 0 * B 0 (Sum.inr j) +
      A.1.1 0 1 * star (B 0 (Sum.inl j))
  rw [Matrix.mul_apply, Fin.sum_univ_two,
    quaternionic_row_one_inr n B hB j]

end
end QuaternionicSymmetry.CompactSymplecticProjectorFirstBlockRowAction
