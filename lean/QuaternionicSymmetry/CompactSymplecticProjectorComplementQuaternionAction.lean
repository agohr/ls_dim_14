import QuaternionicSymmetry.CompactSymplecticProjectorBaseImaginaryPlane

/-! The actual complementary Sp(n) isotropy factor centralizes the entire
quaternion scalar algebra on the genuine projector tangent. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorComplementQuaternionAction

open Manifold
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseQuaternionic
open CompactSymplecticProjectorBaseQuaternionAction
open CompactSymplecticProjectorComplementAction
open CompactSymplecticClosedSubgroupSource
open CompactSymplecticHomogeneousAtlasSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section
set_option maxHeartbeats 5000000

private abbrev RModel (d : ℕ) := Fin d → ℝ

/-- The true complementary-factor manifold derivative commutes with every
quaternion scalar, not just the chosen `I` and `J` generators. -/
theorem complement_derivative_commutes_quaternion
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (atlas : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (D : CompactSymplecticHaar.Group n) :
    letI := atlas.quotientCharts
    ∀ (r : ℍ) (v : TangentSpace 𝓘(ℝ, RModel q) (baseCoset n)),
      mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
        (leftCosetAction n (complementLift n D).1) (baseCoset n)
        (baseQuaternionAction hDesc hImm n d e q g atlas hq r v) =
      baseQuaternionAction hDesc hImm n d e q g atlas hq r
        (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
          (leftCosetAction n (complementLift n D).1) (baseCoset n) v) := by
  letI := atlas.quotientCharts
  intro r v
  let T := mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
    (leftCosetAction n (complementLift n D).1) (baseCoset n)
  have hI (w) : T (baseI hDesc hImm n d e q g atlas hq w) =
      baseI hDesc hImm n d e q g atlas hq (T w) :=
    (complement_derivative_commutes_baseI hDesc hImm n d e q g atlas hq D w).symm
  have hJ (w) : T (baseJ hDesc hImm n d e q g atlas hq w) =
      baseJ hDesc hImm n d e q g atlas hq (T w) :=
    (complement_derivative_commutes_baseJ hDesc hImm n d e q g atlas hq D w).symm
  have hK (w) : T (baseK hDesc hImm n d e q g atlas hq w) =
      baseK hDesc hImm n d e q g atlas hq (T w) := by
    change T (baseI hDesc hImm n d e q g atlas hq
      (baseJ hDesc hImm n d e q g atlas hq w)) = _
    rw [hI, hJ]
    rfl
  rw [baseQuaternionAction_apply hDesc hImm n d e q g atlas hq r v,
    baseQuaternionAction_apply hDesc hImm n d e q g atlas hq r (T v)]
  simp only [map_add, map_smul]
  rw [hI v, hJ v, hK v]

end
end QuaternionicSymmetry.CompactSymplecticProjectorComplementQuaternionAction
