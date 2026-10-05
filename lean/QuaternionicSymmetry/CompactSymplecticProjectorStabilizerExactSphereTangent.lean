import QuaternionicSymmetry.CompactSymplecticProjectorStabilizerSphereRotation

/-! The actual stabilizer sphere rotation is not just abstractly the same
Sp(1) representation: its rotated unit coefficient gives exactly the
intertwining tangent endomorphism under the genuine isotropy differential. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStabilizerExactSphereTangent

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseQuaternionAction
open CompactSymplecticProjectorStabilizerTangentFactor
open CompactSymplecticProjectorComplementQuaternionAction
open CompactSymplecticProjectorIsotropyUnits
open CompactSymplecticProjectorComplementAction
open CompactSymplecticStabilizerBlockPair
open CompactSymplecticProjectorStabilizerSphereRotation
open CompactSymplecticProjectorStabilizerHopfAction
open CompactSymplecticClosedSubgroupSource
open CompactSymplecticHomogeneousAtlasSource
open QuaternionicUnitScalarIsometries
open ManifoldTwistorSphereBundle
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

theorem stabilizerTangentEnd_sphere_intertwining
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Nontrivial E] [FiniteDimensional ℝ E]
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (atlas : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (S : QuaternionicStructure E)
    (k : firstPairStabilizer n) (a : coefficientSphere) :
    letI := atlas.quotientCharts
    letI := sphereFiberAction n S
    stabilizerTangentEnd n d e q g atlas k *
      baseQuaternionAction hDesc hImm n d e q g atlas hq (pureScalar a.1) =
    baseQuaternionAction hDesc hImm n d e q g atlas hq
      (pureScalar ((k • a).1)) * stabilizerTangentEnd n d e q g atlas k := by
  letI := atlas.quotientCharts
  letI := sphereFiberAction n S
  let A := (blockPair n k).1
  let D := (blockPair n k).2
  let z := firstBlockQuaternion A
  have hz : z ≠ 0 := CompactSymplecticProjectorFirstBlockQuaternionUnit.firstBlockQuaternion_ne_zero A
  have hn : Quaternion.normSq z = 1 :=
    CompactSymplecticProjectorFirstBlockUnitQuaternion.firstBlockQuaternion_normSq_one A
  have hstar : star z = z⁻¹ := by
    rw [Quaternion.inv_def, hn]
    simp
  have hr : pureScalar ((k • a).1) = z * pureScalar a.1 * z⁻¹ := by
    rw [stabilizer_sphere_pureScalar n S k a, hstar]
  have hzr : (z * pureScalar a.1 * z⁻¹) * z = z * pureScalar a.1 := by
    simp [mul_assoc, inv_mul_cancel₀ hz]
  rw [hr]
  rw [stabilizerTangentEnd_factor_blocks hDesc hImm n d e q g atlas k,
    firstBlockEnd_eq_action hDesc hImm n d e q g atlas hq A]
  change (baseQuaternionAction hDesc hImm n d e q g atlas hq z *
      stabilizerTangentEnd n d e q g atlas (complementLift n D)) *
      baseQuaternionAction hDesc hImm n d e q g atlas hq (pureScalar a.1) =
    baseQuaternionAction hDesc hImm n d e q g atlas hq
      (z * pureScalar a.1 * z⁻¹) *
      (baseQuaternionAction hDesc hImm n d e q g atlas hq z *
        stabilizerTangentEnd n d e q g atlas (complementLift n D))
  let F := baseQuaternionAction hDesc hImm n d e q g atlas hq
  let C := stabilizerTangentEnd n d e q g atlas (complementLift n D)
  change (F z * C) * F (pureScalar a.1) =
    F (z * pureScalar a.1 * z⁻¹) * (F z * C)
  calc
    (F z * C) * F (pureScalar a.1) =
        F z * (F (pureScalar a.1) * C) := by
          rw [mul_assoc, complementEnd_commutes_action hDesc hImm n d e q g atlas hq D
            (pureScalar a.1)]
    _ = F (z * pureScalar a.1) * C := by rw [← mul_assoc, ← map_mul]
    _ = F ((z * pureScalar a.1 * z⁻¹) * z) * C := by rw [hzr]
    _ = F (z * pureScalar a.1 * z⁻¹) * (F z * C) := by rw [map_mul, mul_assoc]

end
end QuaternionicSymmetry.CompactSymplecticProjectorStabilizerExactSphereTangent
