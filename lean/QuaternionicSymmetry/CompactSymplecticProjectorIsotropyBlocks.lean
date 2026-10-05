import QuaternionicSymmetry.CompactSymplecticProjectorBaseQuaternionic
import QuaternionicSymmetry.CompactSymplecticStabilizerProduct

/-! The actual projector stabilizer acts on the genuine base tangent's
upper mixed block by its two checked compact-symplectic diagonal blocks. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorIsotropyBlocks

open Matrix Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseTangentRange
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorSmoothAction
open CompactSymplecticProjectorAmbientMetric
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open CompactSymplecticStabilizerIndex
open CompactSymplecticStabilizerDiagonal
open CompactSymplecticStabilizerBlockPair
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev J (n : ℕ) := Fin n ⊕ Fin n
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)
private abbrev RModel (d : ℕ) := Fin d → ℝ

/-- Reindexing intertwines literal matrix conjugation with conjugation by
the reindexed actual compact-symplectic element. -/
private theorem baseBlock_conjugate (n : ℕ) (u : G n) (X : Mat n) :
    baseBlockMatrix n ((u.1 : Mat n) * X * (u.1 : Mat n)ᴴ) =
      blockMatrix n u * baseBlockMatrix n X * (blockMatrix n u)ᴴ := by
  change (Matrix.reindexAlgEquiv ℂ ℂ (blockIndexEquiv n))
      ((u.1 : Mat n) * X * (u.1 : Mat n)ᴴ) =
    (Matrix.reindexAlgEquiv ℂ ℂ (blockIndexEquiv n)) (u.1 : Mat n) *
      (Matrix.reindexAlgEquiv ℂ ℂ (blockIndexEquiv n)) X *
      ((Matrix.reindexAlgEquiv ℂ ℂ (blockIndexEquiv n)) (u.1 : Mat n))ᴴ
  rw [map_mul, map_mul]
  rfl

/-- The exact isotropy representation on upper off-diagonal blocks is
`B ↦ A B Dᴴ`, where `A` and `D` are the actual Sp(1) and Sp(n) blocks. -/
theorem stabilizer_upperBlock_action (n : ℕ)
    (u : G n) (hu : u ∈ firstPairStabilizer n)
    (X : Mat n) :
    (baseBlockMatrix n ((u.1 : Mat n) * X * (u.1 : Mat n)ᴴ)).toBlocks₁₂ =
      (blockMatrix n u).toBlocks₁₁ * (baseBlockMatrix n X).toBlocks₁₂ *
        (blockMatrix n u).toBlocks₂₂ᴴ := by
  rw [baseBlock_conjugate, blockMatrix_eq_fromBlocks n u hu]
  have hX : baseBlockMatrix n X =
      Matrix.fromBlocks (baseBlockMatrix n X).toBlocks₁₁
        (baseBlockMatrix n X).toBlocks₁₂
        (baseBlockMatrix n X).toBlocks₂₁
        (baseBlockMatrix n X).toBlocks₂₂ :=
    (Matrix.fromBlocks_toBlocks (baseBlockMatrix n X)).symm
  rw [hX]
  simp only [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, Matrix.toBlocks_fromBlocks₁₂]
  simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₂₂]

theorem stabilizer_fixes_baseCoset (n : ℕ)
    (u : G n) (hu : u ∈ firstPairStabilizer n) :
    leftCosetAction n u (baseCoset n) = baseCoset n := by
  change ((u * 1 : G n) : ProjectiveCarrier n) = ((1 : G n) : ProjectiveCarrier n)
  rw [mul_one]
  apply QuotientGroup.eq.mpr
  simpa using (firstPairStabilizer n).inv_mem hu

private theorem smooth_leftCosetAction (n d e q : ℕ)
    (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (u : G n) :
    letI := a.quotientCharts
    ContMDiff 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q) ∞
      (leftCosetAction n u) := by
  letI := g.charts
  letI := a.quotientCharts
  have hpair : ContMDiff 𝓘(ℝ, RModel q)
      (𝓘(ℝ, RModel d).prod 𝓘(ℝ, RModel q)) ∞
      (fun y : ProjectiveCarrier n => (u, y)) :=
    contMDiff_const.prodMk contMDiff_id
  exact a.actionSmooth.comp hpair

/-- On the true tangent space, the actual stabilizer differential acts on
the complete upper-block coordinate by the same `A B Dᴴ` formula. -/
theorem stabilizer_upperTangent_action
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (u : G n) (hu : u ∈ firstPairStabilizer n) :
    letI := a.quotientCharts
    ∀ v : TangentSpace 𝓘(ℝ, RModel q) (baseCoset n),
      ((baseTangentUpperLinear hDesc n d e q g a)
        (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
          (leftCosetAction n u) (baseCoset n) v)).1 =
        (blockMatrix n u).toBlocks₁₁ *
          ((baseTangentUpperLinear hDesc n d e q g a) v).1 *
            (blockMatrix n u).toBlocks₂₂ᴴ := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  intro v
  have hEq : ∀ y : ProjectiveCarrier n,
      quotientOrbitProjector n (leftCosetAction n u y) =
        conjugationCLM n u (quotientOrbitProjector n y) := by
    intro y
    simpa only [conjugationCLM_apply] using quotient_projector_equivariant n u y
  have hDer := ManifoldEquivariantPullbackPairing.mfderiv_equivariance
    (quotientOrbitProjector n) (leftCosetAction n u) (conjugationCLM n u)
    (smooth_quotientOrbitProjector_actual hDesc n d e q g a)
    (smooth_leftCosetAction n d e q g a u) hEq (baseCoset n) v
  rw [stabilizer_fixes_baseCoset n u hu] at hDer
  simp only [conjugationCLM_apply] at hDer
  have hBlock := congrArg (fun X : Mat n => (baseBlockMatrix n X).toBlocks₁₂) hDer
  simpa only [baseTangentUpperLinear, LinearMap.codRestrict_apply,
    LinearMap.comp_apply]
    using hBlock.trans (stabilizer_upperBlock_action n u hu _)

end
end QuaternionicSymmetry.CompactSymplecticProjectorIsotropyBlocks
