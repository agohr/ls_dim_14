import QuaternionicSymmetry.ProjectorQuaternionicNoncommutingBlock
import QuaternionicSymmetry.CompactSymplecticProjectorBaseTangentRange
import QuaternionicSymmetry.ProjectorPeirceCurvatureBracket

/-! Two genuine tangent derivatives at the identity coset do not commute.
The explicit quaternionic upper blocks are lifted through the proved actual
base-tangent equivalence, rather than assumed to be model tangent vectors. -/

namespace QuaternionicSymmetry.ProjectorQuaternionicNoncommutingBaseTangent

open Matrix Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseTangentRange
open CompactSymplecticProjectorQuaternionicUpperLinear
open CompactSymplecticProjectorBlockFrobenius
open ProjectorQuaternionicNoncommutingBlock
open ProjectorPeirceCurvatureBracket
open CompactSymplecticClosedSubgroupSource
open CompactSymplecticHomogeneousAtlasSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ
private abbrev RModel (q : ℕ) := Fin q → ℝ

private theorem offDiagonal_commutator_ne_zero (n : ℕ)
    (B C : Matrix (Fin 2) (Fin n ⊕ Fin n) ℂ)
    (h : B * Cᴴ - C * Bᴴ ≠ 0) :
    commutator (offDiagonal B) (offDiagonal C) ≠ 0 := by
  intro hzero
  have hblock : B * Cᴴ - C * Bᴴ = 0 := by
    ext i j
    have hh := congrFun (congrFun hzero (Sum.inl i)) (Sum.inl j)
    simp only [ProjectorPeirceCurvatureBracket.commutator, offDiagonal,
      Matrix.sub_apply, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_apply₁₁, Matrix.mul_zero, Matrix.zero_mul,
      zero_add, add_zero] at hh
    exact hh
  exact h hblock

theorem actual_base_tangent_noncommuting
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) :
    letI := a.quotientCharts
    ∃ v w : TangentSpace 𝓘(ℝ,RModel q) (baseCoset n),
      ProjectorPeirceCurvatureBracket.commutator
        (show Mat n from mfderiv 𝓘(ℝ,RModel q) 𝓘(ℝ,Mat n)
          (quotientOrbitProjector n) (baseCoset n) v)
        (show Mat n from mfderiv 𝓘(ℝ,RModel q) 𝓘(ℝ,Mat n)
          (quotientOrbitProjector n) (baseCoset n) w) ≠ 0 := by
  letI := a.quotientCharts
  let B : upperSubmodule n := ⟨realBlock n hn, realBlock_quaternionic n hn⟩
  let C : upperSubmodule n := ⟨imaginaryBlock n hn, imaginaryBlock_quaternionic n hn⟩
  let v := (baseTangentUpperLinearEquiv hDesc hImm n d e q g a hq).symm B
  let w := (baseTangentUpperLinearEquiv hDesc hImm n d e q g a hq).symm C
  refine ⟨v, w, ?_⟩
  let X := mfderiv 𝓘(ℝ,RModel q) 𝓘(ℝ,Mat n)
    (quotientOrbitProjector n) (baseCoset n) v
  let Y := mfderiv 𝓘(ℝ,RModel q) 𝓘(ℝ,Mat n)
    (quotientOrbitProjector n) (baseCoset n) w
  have hB : (baseBlockMatrix n X).toBlocks₁₂ = realBlock n hn := by
    have hh := (baseTangentUpperLinearEquiv hDesc hImm n d e q g a hq).apply_symm_apply B
    exact congrArg Subtype.val hh
  have hC : (baseBlockMatrix n Y).toBlocks₁₂ = imaginaryBlock n hn := by
    have hh := (baseTangentUpperLinearEquiv hDesc hImm n d e q g a hq).apply_symm_apply C
    exact congrArg Subtype.val hh
  have hX : baseBlockMatrix n X = offDiagonal (realBlock n hn) := by
    rw [base_tangent_eq_offDiagonal hDesc n d e q g a v, hB]
    rfl
  have hY : baseBlockMatrix n Y = offDiagonal (imaginaryBlock n hn) := by
    rw [base_tangent_eq_offDiagonal hDesc n d e q g a w, hC]
    rfl
  have hblock : commutator (offDiagonal (realBlock n hn))
      (offDiagonal (imaginaryBlock n hn)) ≠ 0 :=
    offDiagonal_commutator_ne_zero n _ _
      (real_imaginary_block_commutator_nonzero n hn)
  intro hzero
  have hh := congrArg
    (Matrix.reindexAlgEquiv ℂ ℂ
      (CompactSymplecticStabilizerIndex.blockIndexEquiv n)) hzero
  have h' : commutator (baseBlockMatrix n X) (baseBlockMatrix n Y) = 0 := by
    simpa only [ProjectorPeirceCurvatureBracket.commutator,
      baseBlockMatrix, map_sub, map_mul, map_zero] using hh
  rw [hX, hY] at h'
  exact hblock h'

end
end QuaternionicSymmetry.ProjectorQuaternionicNoncommutingBaseTangent
