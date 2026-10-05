import QuaternionicSymmetry.CompactSymplecticProjectorIsotropyUnits

/-! Literal row formulas for the actual isotropy derivatives. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorIsotropyRows

open Matrix Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseTangentRange
open CompactSymplecticProjectorIsotropyUnits
open CompactSymplecticProjectorFirstBlockUnits
open CompactSymplecticProjectorQuaternionicRow
open CompactSymplecticProjectorQuaternionicUpperLinear
open CompactSymplecticClosedSubgroupSource
open CompactSymplecticHomogeneousAtlasSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ

/-- The genuine first-block `i` isotropy derivative multiplies every
first-row complex coordinate by `i`. -/
theorem firstI_tangent_row
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) :
    letI := a.quotientCharts
    ∀ (v : TangentSpace 𝓘(ℝ, RModel q) (baseCoset n))
      (c : Fin n ⊕ Fin n),
      ((baseTangentUpperLinear hDesc n d e q g a)
        (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
          (leftCosetAction n (firstBlockLift n firstI).1) (baseCoset n) v)).1 0 c =
        Complex.I * ((baseTangentUpperLinear hDesc n d e q g a) v).1 0 c := by
  letI := a.quotientCharts
  intro v c
  rw [firstBlockLift_tangent hDesc n d e q g a firstI v, firstI_matrix]
  exact firstI_row n _ c

/-- The genuine first-block `j` isotropy derivative has precisely the
standard quaternionic row signs, not their negatives. -/
theorem firstJ_tangent_row_inl
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) :
    letI := a.quotientCharts
    ∀ (v : TangentSpace 𝓘(ℝ, RModel q) (baseCoset n)) (j : Fin n),
      ((baseTangentUpperLinear hDesc n d e q g a)
        (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
          (leftCosetAction n (firstBlockLift n firstJ).1) (baseCoset n) v)).1
            0 (Sum.inl j) =
        star (((baseTangentUpperLinear hDesc n d e q g a) v).1 0 (Sum.inr j)) := by
  letI := a.quotientCharts
  intro v j
  rw [firstBlockLift_tangent hDesc n d e q g a firstJ v, firstJ_matrix,
    firstJ_row]
  let B := (baseTangentUpperLinear hDesc n d e q g a v).1
  have hB : B * CompactSymplecticHaar.standardJ n =
      CompactSymplecticStabilizerFormBlocks.firstBlockJ * B.map star :=
    (mem_upperSubmodule_iff n B).1
      (baseTangentUpperLinear hDesc n d e q g a v).2
  change -B 1 (Sum.inl j) = star (B 0 (Sum.inr j))
  rw [quaternionic_row_one_inl n B hB j]
  simp

theorem firstJ_tangent_row_inr
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) :
    letI := a.quotientCharts
    ∀ (v : TangentSpace 𝓘(ℝ, RModel q) (baseCoset n)) (j : Fin n),
      ((baseTangentUpperLinear hDesc n d e q g a)
        (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
          (leftCosetAction n (firstBlockLift n firstJ).1) (baseCoset n) v)).1
            0 (Sum.inr j) =
        -star (((baseTangentUpperLinear hDesc n d e q g a) v).1 0 (Sum.inl j)) := by
  letI := a.quotientCharts
  intro v j
  rw [firstBlockLift_tangent hDesc n d e q g a firstJ v, firstJ_matrix,
    firstJ_row]
  let B := (baseTangentUpperLinear hDesc n d e q g a v).1
  have hB : B * CompactSymplecticHaar.standardJ n =
      CompactSymplecticStabilizerFormBlocks.firstBlockJ * B.map star :=
    (mem_upperSubmodule_iff n B).1
      (baseTangentUpperLinear hDesc n d e q g a v).2
  change -B 1 (Sum.inr j) = -star (B 0 (Sum.inl j))
  exact congrArg Neg.neg (quaternionic_row_one_inr n B hB j)

end
end QuaternionicSymmetry.CompactSymplecticProjectorIsotropyRows
