import QuaternionicSymmetry.CompactSymplecticProjectorAdaptedAtlasMetric
import QuaternionicSymmetry.CompactSymplecticProjectorEuclideanChartBridgeTangent

/-! The actual descended rank-three imaginary plane, expressed on
the gauge-adapted Euclidean tangent model. Chart restriction has the
identity differential, so these are the same genuine tangent operators. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAdaptedAtlasPlane

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorEuclideanCharts
open CompactSymplecticProjectorEuclideanSelfModelPlane
open CompactSymplecticProjectorAdaptedNeighborhoodAtlas
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev EModel (d : ℕ) := EuclideanSpace ℝ (Fin d)

def adaptedImaginaryPlane
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) :
    letI := adaptedEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    Submodule ℝ (Module.End ℝ (TangentSpace 𝓘(ℝ, EModel q) x)) := by
  letI := euclideanQuotientCharts n d e q g a
  exact selfModelImaginaryPlane hDesc hImm n d e q g a hq hn x

theorem adaptedImaginaryPlane_finrank
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) :
    letI := adaptedEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    Module.finrank ℝ
      (adaptedImaginaryPlane hLee hDesc hImm n d e q g a hq hn x) = 3 := by
  letI := euclideanQuotientCharts n d e q g a
  exact selfModelImaginaryPlane_finrank hDesc hImm n d e q g a hq hn x

end
end QuaternionicSymmetry.CompactSymplecticProjectorAdaptedAtlasPlane
