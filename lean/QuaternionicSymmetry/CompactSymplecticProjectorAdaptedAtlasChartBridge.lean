import QuaternionicSymmetry.CompactSymplecticProjectorAdaptedAtlasTransition

/-! An explicitly checked original chart-change equivalence is exactly
the gauge-refined Euclidean tangent-bundle-core transition after conjugation. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAdaptedAtlasChartBridge

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorAdaptedNeighborhoodAtlas
open CompactSymplecticProjectorAdaptedAtlasTransition
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev EModel (d : ℕ) := EuclideanSpace ℝ (Fin d)

theorem actualChartChange_eq_refined_tangentCore
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x y z : ProjectiveCarrier n)
    (C : RModel q ≃L[ℝ] RModel q)
    (hC : letI := a.quotientCharts
      letI : IsManifold 𝓘(ℝ, RModel q) 1 (ProjectiveCarrier n) :=
        a.quotientManifold.of_le (by norm_cast)
      (C : RModel q →L[ℝ] RModel q) =
        tangentCoordChange 𝓘(ℝ, RModel q) x y z) :
    letI := adaptedEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI : IsManifold 𝓘(ℝ, EModel q) 1 (ProjectiveCarrier n) :=
      (adaptedEuclideanQuotientCharts_isManifold
        hLee hDesc hImm n d e q g a hq hn).of_le (by norm_cast)
    (euclideanModelEquiv q).toContinuousLinearMap.comp
      ((C : RModel q →L[ℝ] RModel q).comp
        (euclideanModelEquiv q).symm.toContinuousLinearMap) =
      (tangentBundleCore 𝓘(ℝ, EModel q) (ProjectiveCarrier n)).coordChange
        (achart (EModel q) x) (achart (EModel q) y) z := by
  letI := a.quotientCharts
  letI : IsManifold 𝓘(ℝ, RModel q) 1 (ProjectiveCarrier n) :=
    a.quotientManifold.of_le (by norm_cast)
  letI := adaptedEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI : IsManifold 𝓘(ℝ, EModel q) 1 (ProjectiveCarrier n) :=
    (adaptedEuclideanQuotientCharts_isManifold
      hLee hDesc hImm n d e q g a hq hn).of_le (by norm_cast)
  change (euclideanModelEquiv q).toContinuousLinearMap.comp
      ((C : RModel q →L[ℝ] RModel q).comp
        (euclideanModelEquiv q).symm.toContinuousLinearMap) =
      tangentCoordChange 𝓘(ℝ, EModel q) x y z
  rw [adapted_tangentCoordChange_eq_original_conj
    hLee hDesc hImm n d e q g a hq hn x y z, ← hC]

end
end QuaternionicSymmetry.CompactSymplecticProjectorAdaptedAtlasChartBridge
