import QuaternionicSymmetry.ManifoldChartRefinement
import QuaternionicSymmetry.CompactSymplecticProjectorEuclideanSelfModelQuaternionicMetric
import QuaternionicSymmetry.CompactSymplecticProjectorActualSmoothQuaternionicPlane

/-! Choose the checked local quaternionic-gauge neighborhoods at every
point and refine the genuine Euclidean quotient atlas to them. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAdaptedNeighborhoodAtlas

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorActualSmoothQuaternionicPlane
open CompactSymplecticProjectorEuclideanCharts
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldChartRefinement
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev EModel (d : ℕ) := EuclideanSpace ℝ (Fin d)

def actualGaugeNeighborhood
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) : Set (ProjectiveCarrier n) :=
  Classical.choose
    (actualQuotientPlane_has_local_smooth_frame hLee hDesc hImm
      n d e q g a hq hn x)

theorem actualGaugeNeighborhood_isOpen
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) :
    IsOpen (actualGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x) :=
  (Classical.choose_spec
    (actualQuotientPlane_has_local_smooth_frame hLee hDesc hImm
      n d e q g a hq hn x)).1

theorem mem_actualGaugeNeighborhood
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) :
    x ∈ actualGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x :=
  (Classical.choose_spec
    (actualQuotientPlane_has_local_smooth_frame hLee hDesc hImm
      n d e q g a hq hn x)).2.1

def adaptedEuclideanQuotientCharts
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) : ChartedSpace (EModel q) (ProjectiveCarrier n) := by
  letI := euclideanQuotientCharts n d e q g a
  exact restrictedCharts
    (actualGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn)
    (actualGaugeNeighborhood_isOpen hLee hDesc hImm n d e q g a hq hn)
    (mem_actualGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn)

theorem adaptedEuclideanQuotientCharts_isManifold
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) :
    letI := adaptedEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    IsManifold 𝓘(ℝ, EModel q) ∞ (ProjectiveCarrier n) := by
  letI := euclideanQuotientCharts n d e q g a
  letI := euclideanQuotientCharts_isManifold n d e q g a
  exact restrictedCharts_isManifold
    (I := 𝓘(ℝ, EModel q))
    (actualGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn)
    (actualGaugeNeighborhood_isOpen hLee hDesc hImm n d e q g a hq hn)
    (mem_actualGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn)

end
end QuaternionicSymmetry.CompactSymplecticProjectorAdaptedNeighborhoodAtlas
