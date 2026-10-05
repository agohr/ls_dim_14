import QuaternionicSymmetry.CompactSymplecticProjectorBaseQuaternionicMetric

/-! The complementary compact-symplectic factor acts on the actual base
tangent from the right, while first-block quaternionic units act from the
left. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorComplementAction

open Matrix Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseTangentRange
open CompactSymplecticProjectorIsotropyBlocks
open CompactSymplecticProjectorIsotropyOperators
open CompactSymplecticProjectorIsotropyUnits
open CompactSymplecticProjectorBaseQuaternionic
open CompactSymplecticProjectorFirstBlockUnits
open CompactSymplecticStabilizerBlockSurjection
open CompactSymplecticStabilizerBlockPair
open CompactSymplecticStabilizerDiagonal
open CompactSymplecticClosedSubgroupSource
open CompactSymplecticHomogeneousAtlasSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ

def complementLift (n : ℕ) (D : CompactSymplecticHaar.Group n) :
    firstPairStabilizer n := fromBlockPair n (1, D)

theorem complementLift_upper (n : ℕ) (D : CompactSymplecticHaar.Group n) :
    (blockMatrix n (complementLift n D).1).toBlocks₁₁ = 1 := by
  have h := congrArg (fun p : FirstBlockGroup × CompactSymplecticHaar.Group n =>
    (p.1.1.1 : Matrix (Fin 2) (Fin 2) ℂ))
    (blockPair_fromBlockPair n (1, D))
  exact h

theorem complementLift_lower (n : ℕ) (D : CompactSymplecticHaar.Group n) :
    (blockMatrix n (complementLift n D).1).toBlocks₂₂ = D.1.1 := by
  have h := congrArg (fun p : FirstBlockGroup × CompactSymplecticHaar.Group n =>
    (p.2.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ))
    (blockPair_fromBlockPair n (1, D))
  exact h

/-- The actual complementary-factor differential is exactly right
multiplication by the adjoint of its checked Sp(n) block. -/
theorem complementLift_tangent
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (D : CompactSymplecticHaar.Group n) :
    letI := a.quotientCharts
    ∀ v : TangentSpace 𝓘(ℝ, RModel q) (baseCoset n),
      ((baseTangentUpperLinear hDesc n d e q g a)
        (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
          (leftCosetAction n (complementLift n D).1) (baseCoset n) v)).1 =
        ((baseTangentUpperLinear hDesc n d e q g a) v).1 * D.1.1ᴴ := by
  letI := a.quotientCharts
  intro v
  have h := stabilizer_upperTangent_action hDesc n d e q g a
    (complementLift n D).1 (complementLift n D).2 v
  rw [complementLift_upper, complementLift_lower, Matrix.one_mul] at h
  exact h

/-- The complementary Sp(n) differential commutes with the genuine
quaternionic `I`; this is matrix associativity for left and right block
actions, transferred back by the proved tangent equivalence. -/
theorem complement_derivative_commutes_baseI
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (D : CompactSymplecticHaar.Group n) :
    letI := a.quotientCharts
    ∀ v : TangentSpace 𝓘(ℝ, RModel q) (baseCoset n),
      baseI hDesc hImm n d e q g a hq
        (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
          (leftCosetAction n (complementLift n D).1) (baseCoset n) v) =
      mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
        (leftCosetAction n (complementLift n D).1) (baseCoset n)
        (baseI hDesc hImm n d e q g a hq v) := by
  letI := a.quotientCharts
  intro v
  apply baseTangentUpperLinear_injective hDesc hImm n d e q g a
  apply Subtype.ext
  rw [baseI_eq_isotropy_derivative hDesc hImm n d e q g a hq]
  rw [firstBlockLift_tangent hDesc n d e q g a firstI]
  rw [complementLift_tangent hDesc n d e q g a D]
  rw [complementLift_tangent hDesc n d e q g a D]
  rw [baseI_eq_isotropy_derivative hDesc hImm n d e q g a hq]
  rw [firstBlockLift_tangent hDesc n d e q g a firstI]
  simp only [firstI_matrix, Matrix.mul_assoc]

/-- The complementary Sp(n) differential also commutes with `J`. -/
theorem complement_derivative_commutes_baseJ
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (D : CompactSymplecticHaar.Group n) :
    letI := a.quotientCharts
    ∀ v : TangentSpace 𝓘(ℝ, RModel q) (baseCoset n),
      baseJ hDesc hImm n d e q g a hq
        (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
          (leftCosetAction n (complementLift n D).1) (baseCoset n) v) =
      mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
        (leftCosetAction n (complementLift n D).1) (baseCoset n)
        (baseJ hDesc hImm n d e q g a hq v) := by
  letI := a.quotientCharts
  intro v
  apply baseTangentUpperLinear_injective hDesc hImm n d e q g a
  apply Subtype.ext
  rw [baseJ_eq_isotropy_derivative hDesc hImm n d e q g a hq]
  rw [firstBlockLift_tangent hDesc n d e q g a firstJ]
  rw [complementLift_tangent hDesc n d e q g a D]
  rw [complementLift_tangent hDesc n d e q g a D]
  rw [baseJ_eq_isotropy_derivative hDesc hImm n d e q g a hq]
  rw [firstBlockLift_tangent hDesc n d e q g a firstJ]
  simp only [firstJ_matrix, Matrix.mul_assoc]

end
end QuaternionicSymmetry.CompactSymplecticProjectorComplementAction
