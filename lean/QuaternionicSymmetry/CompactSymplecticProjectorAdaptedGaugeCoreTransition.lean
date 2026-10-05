import QuaternionicSymmetry.CompactSymplecticProjectorAdaptedAtlasChartBridge
import QuaternionicSymmetry.CompactSymplecticProjectorAdaptedAtlasGaugePlane

/-! The chart-change `C` appearing in the proved smooth local Q-frame
is precisely a transition of the actual refined Euclidean tangent core. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAdaptedGaugeCoreTransition

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorAdaptedNeighborhoodAtlas
open CompactSymplecticProjectorAdaptedAtlasChartBridge
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev EModel (d : ℕ) := EuclideanSpace ℝ (Fin d)
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

theorem localChartChange_eq_adaptedTangentCore
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (σ : ProjectiveCarrier n → G n)
    (x y : ProjectiveCarrier n) (C : RModel q ≃L[ℝ] RModel q)
    (hC : letI := g.charts
      letI := g.manifold
      letI := a.quotientCharts
      letI := a.quotientManifold
      (C : RModel q →L[ℝ] RModel q) =
        tangentCoordChange 𝓘(ℝ, RModel q)
          (leftCosetAction n (σ y) (baseCoset n))
          (leftCosetAction n (σ x) (baseCoset n))
          (leftCosetAction n (σ y) (baseCoset n))) :
    letI := adaptedEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI : IsManifold 𝓘(ℝ, EModel q) 1 (ProjectiveCarrier n) :=
      (adaptedEuclideanQuotientCharts_isManifold
        hLee hDesc hImm n d e q g a hq hn).of_le (by norm_cast)
    (euclideanModelEquiv q).toContinuousLinearMap.comp
      ((C : RModel q →L[ℝ] RModel q).comp
        (euclideanModelEquiv q).symm.toContinuousLinearMap) =
      (tangentBundleCore 𝓘(ℝ, EModel q) (ProjectiveCarrier n)).coordChange
        (achart (EModel q) (leftCosetAction n (σ y) (baseCoset n)))
        (achart (EModel q) (leftCosetAction n (σ x) (baseCoset n)))
        (leftCosetAction n (σ y) (baseCoset n)) := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  exact actualChartChange_eq_refined_tangentCore hLee hDesc hImm
    n d e q g a hq hn
    (leftCosetAction n (σ y) (baseCoset n))
    (leftCosetAction n (σ x) (baseCoset n))
    (leftCosetAction n (σ y) (baseCoset n)) C hC

end
end QuaternionicSymmetry.CompactSymplecticProjectorAdaptedGaugeCoreTransition
