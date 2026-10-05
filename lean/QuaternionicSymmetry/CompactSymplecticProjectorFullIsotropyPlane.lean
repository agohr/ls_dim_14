import QuaternionicSymmetry.CompactSymplecticProjectorStabilizerTangentFactor

/-! Every actual Sp(n+1) projector-stabilizer differential preserves the
checked rank-three imaginary quaternionic tangent plane. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorFullIsotropyPlane

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseQuaternionAction
open CompactSymplecticProjectorBaseImaginaryPlane
open CompactSymplecticProjectorFirstBlockQuaternionUnit
open CompactSymplecticProjectorStabilizerTangentFactor
open CompactSymplecticProjectorComplementQuaternionAction
open CompactSymplecticProjectorIsotropyUnits
open CompactSymplecticProjectorComplementAction
open CompactSymplecticStabilizerBlockPair
open CompactSymplecticClosedSubgroupSource
open CompactSymplecticHomogeneousAtlasSource
open QuaternionicSymmetry.QuaternionImaginaryConjugation
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section
set_option maxHeartbeats 5000000

private abbrev RModel (d : ℕ) := Fin d → ℝ

private theorem firstBlockEnd_eq_action
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (atlas : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (A : FirstBlockGroup) :
    letI := atlas.quotientCharts
    stabilizerTangentEnd n d e q g atlas (firstBlockLift n A) =
      baseQuaternionAction hDesc hImm n d e q g atlas hq
        (firstBlockQuaternion A) := by
  letI := atlas.quotientCharts
  ext v
  exact firstBlock_derivative_eq_quaternionAction hDesc hImm n d e q g atlas hq A v

private theorem complementEnd_commutes_action
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (atlas : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (D : CompactSymplecticHaar.Group n) (r : ℍ) :
    letI := atlas.quotientCharts
    stabilizerTangentEnd n d e q g atlas (complementLift n D) *
        baseQuaternionAction hDesc hImm n d e q g atlas hq r =
      baseQuaternionAction hDesc hImm n d e q g atlas hq r *
        stabilizerTangentEnd n d e q g atlas (complementLift n D) := by
  letI := atlas.quotientCharts
  ext v
  exact complement_derivative_commutes_quaternion hDesc hImm n d e q g atlas hq D r v

/-- Full actual stabilizer intertwining: each imaginary quaternion tangent
endomorphism is carried to another member of the same checked rank-three
plane. No inverse-differential premise is used. -/
theorem fullStabilizer_preserves_imaginary
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (atlas : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (u : firstPairStabilizer n) :
    letI := atlas.quotientCharts
    ∀ S : baseImaginaryPlane hDesc hImm n d e q g atlas hq,
      ∃ S' : baseImaginaryPlane hDesc hImm n d e q g atlas hq,
        stabilizerTangentEnd n d e q g atlas u * S.1 =
          S'.1 * stabilizerTangentEnd n d e q g atlas u := by
  letI := atlas.quotientCharts
  intro S
  obtain ⟨r, hr, hSr⟩ := Submodule.mem_map.mp S.2
  let A := (blockPair n u).1
  let D := (blockPair n u).2
  let z := firstBlockQuaternion A
  have hz : z ≠ 0 := firstBlockQuaternion_ne_zero A
  let r' : ℍ := z * r * z⁻¹
  have hr' : r'.re = 0 := imaginary_conjugation z r hz
    (LinearMap.mem_ker.mp hr)
  refine ⟨⟨baseQuaternionAction hDesc hImm n d e q g atlas hq r',
    action_imaginary_mem hDesc hImm n d e q g atlas hq r' hr'⟩, ?_⟩
  rw [← hSr]
  rw [stabilizerTangentEnd_factor_blocks hDesc hImm n d e q g atlas u,
    firstBlockEnd_eq_action hDesc hImm n d e q g atlas hq A]
  change (baseQuaternionAction hDesc hImm n d e q g atlas hq z *
      stabilizerTangentEnd n d e q g atlas (complementLift n D)) *
      baseQuaternionAction hDesc hImm n d e q g atlas hq r =
    baseQuaternionAction hDesc hImm n d e q g atlas hq r' *
      (baseQuaternionAction hDesc hImm n d e q g atlas hq z *
        stabilizerTangentEnd n d e q g atlas (complementLift n D))
  rw [mul_assoc, complementEnd_commutes_action hDesc hImm n d e q g atlas hq D r]
  have hzr : r' * z = z * r := by
    simp [r', mul_assoc, inv_mul_cancel₀ hz]
  rw [← mul_assoc, ← map_mul, ← hzr, map_mul, mul_assoc]

end
end QuaternionicSymmetry.CompactSymplecticProjectorFullIsotropyPlane
