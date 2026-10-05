import QuaternionicSymmetry.CompactSymplecticProjectorEuclideanModel
import QuaternionicSymmetry.CompactSymplecticProjectorSmoothAction

/-! The actual rank-two projector orbit immersion remains smooth in
the equivalent Euclidean/L² quotient model. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorEuclideanModelSmoothOrbit

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorSmoothAction
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ
private abbrev RModel (d : ℕ) := Fin d → ℝ

theorem smooth_quotientOrbitProjector_euclideanModel
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) :
    letI := a.quotientCharts
    ContMDiff (euclideanModel q) 𝓘(ℝ, Mat n) ∞
      (quotientOrbitProjector n) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  exact ((euclideanModelEquiv q).contMDiff_transContinuousLinearEquiv_left
    (I := 𝓘(ℝ, RModel q))).2
    (smooth_quotientOrbitProjector_actual hDesc n d e q g a)

end
end QuaternionicSymmetry.CompactSymplecticProjectorEuclideanModelSmoothOrbit
