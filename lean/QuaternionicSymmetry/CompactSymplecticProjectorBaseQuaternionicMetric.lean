import QuaternionicSymmetry.CompactSymplecticProjectorIsotropyOperators

/-! Metric compatibility of the actual quaternionic base-tangent
endomorphisms follows from their identification with real compact-group
isometries, not from a postulated quaternionic metric. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorBaseQuaternionicMetric

open Manifold Bundle
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseQuaternionic
open CompactSymplecticProjectorRiemannianMetric
open CompactSymplecticProjectorIsotropyOperators
open CompactSymplecticProjectorIsotropyBlocks
open CompactSymplecticProjectorIsotropyUnits
open CompactSymplecticProjectorFirstBlockUnits
open CompactSymplecticClosedSubgroupSource
open CompactSymplecticHomogeneousAtlasSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ

/-- The genuine tangent `I` is orthogonal for the actual smooth
Hilbert--Schmidt pullback metric at the base projector. -/
theorem baseI_metric_compatible
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    ∀ v w : TangentSpace 𝓘(ℝ, RModel q) (baseCoset n),
      (smoothProjectorMetric hDesc hImm n d e q g a).inner (baseCoset n)
        (baseI hDesc hImm n d e q g a hq v)
        (baseI hDesc hImm n d e q g a hq w) =
      (smoothProjectorMetric hDesc hImm n d e q g a).inner (baseCoset n) v w := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  intro v w
  rw [baseI_eq_isotropy_derivative hDesc hImm n d e q g a hq v,
    baseI_eq_isotropy_derivative hDesc hImm n d e q g a hq w]
  have h := smoothProjectorMetric_invariant hDesc hImm n d e q g a
    (firstBlockLift n firstI).1 (baseCoset n) v w
  rw [stabilizer_fixes_baseCoset n (firstBlockLift n firstI).1
    (firstBlockLift n firstI).2] at h
  exact h

/-- The genuine tangent `J` is orthogonal for the same actual metric. -/
theorem baseJ_metric_compatible
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    ∀ v w : TangentSpace 𝓘(ℝ, RModel q) (baseCoset n),
      (smoothProjectorMetric hDesc hImm n d e q g a).inner (baseCoset n)
        (baseJ hDesc hImm n d e q g a hq v)
        (baseJ hDesc hImm n d e q g a hq w) =
      (smoothProjectorMetric hDesc hImm n d e q g a).inner (baseCoset n) v w := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  intro v w
  rw [baseJ_eq_isotropy_derivative hDesc hImm n d e q g a hq v,
    baseJ_eq_isotropy_derivative hDesc hImm n d e q g a hq w]
  have h := smoothProjectorMetric_invariant hDesc hImm n d e q g a
    (firstBlockLift n firstJ).1 (baseCoset n) v w
  rw [stabilizer_fixes_baseCoset n (firstBlockLift n firstJ).1
    (firstBlockLift n firstJ).2] at h
  exact h

/-- The third actual quaternionic tangent operator is orthogonal as the
composition of the checked first two isometries. -/
theorem baseK_metric_compatible
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    ∀ v w : TangentSpace 𝓘(ℝ, RModel q) (baseCoset n),
      (smoothProjectorMetric hDesc hImm n d e q g a).inner (baseCoset n)
        (baseK hDesc hImm n d e q g a hq v)
        (baseK hDesc hImm n d e q g a hq w) =
      (smoothProjectorMetric hDesc hImm n d e q g a).inner (baseCoset n) v w := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  intro v w
  change (smoothProjectorMetric hDesc hImm n d e q g a).inner (baseCoset n)
    (baseI hDesc hImm n d e q g a hq
      (baseJ hDesc hImm n d e q g a hq v))
    (baseI hDesc hImm n d e q g a hq
      (baseJ hDesc hImm n d e q g a hq w)) = _
  rw [baseI_metric_compatible hDesc hImm n d e q g a hq,
    baseJ_metric_compatible hDesc hImm n d e q g a hq]

end
end QuaternionicSymmetry.CompactSymplecticProjectorBaseQuaternionicMetric
