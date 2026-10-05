import QuaternionicSymmetry.CompactSymplecticProjectorActualSmoothSectionFrame
import QuaternionicSymmetry.CompactSymplecticProjectorAdaptedNeighborhoodAtlas

/-! Refine the actual Euclidean quotient charts to neighborhoods where both
the quaternionic local frame and its representative section are smooth. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeAtlas

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorActualSmoothSectionFrame
open CompactSymplecticProjectorAdaptedNeighborhoodAtlas
open CompactSymplecticProjectorEuclideanCharts
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldChartRefinement
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev EModel (d : ℕ) := EuclideanSpace ℝ (Fin d)

def smoothSectionGaugeNeighborhood
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) : Set (ProjectiveCarrier n) :=
  Classical.choose
    (actualQuotientPlane_has_local_smooth_section_frame hLee hDesc hImm
      n d e q g a hq hn x)

theorem smoothSectionGaugeNeighborhood_isOpen
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) :
    IsOpen (smoothSectionGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x) :=
  (Classical.choose_spec
    (actualQuotientPlane_has_local_smooth_section_frame hLee hDesc hImm
      n d e q g a hq hn x)).1

theorem mem_smoothSectionGaugeNeighborhood
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) :
    x ∈ smoothSectionGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x :=
  (Classical.choose_spec
    (actualQuotientPlane_has_local_smooth_section_frame hLee hDesc hImm
      n d e q g a hq hn x)).2.1

def strongGaugeNeighborhood
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) : Set (ProjectiveCarrier n) :=
  actualGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x ∩
    smoothSectionGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x

theorem strongGaugeNeighborhood_isOpen
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) :
    IsOpen (strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x) :=
  (actualGaugeNeighborhood_isOpen hLee hDesc hImm n d e q g a hq hn x).inter
    (smoothSectionGaugeNeighborhood_isOpen hLee hDesc hImm n d e q g a hq hn x)

theorem mem_strongGaugeNeighborhood
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) :
    x ∈ strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x :=
  ⟨mem_actualGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x,
    mem_smoothSectionGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x⟩

def strongEuclideanQuotientCharts
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) : ChartedSpace (EModel q) (ProjectiveCarrier n) := by
  letI := euclideanQuotientCharts n d e q g a
  exact restrictedCharts
    (strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn)
    (strongGaugeNeighborhood_isOpen hLee hDesc hImm n d e q g a hq hn)
    (mem_strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn)

theorem strongEuclideanQuotientCharts_isManifold
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) :
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    IsManifold 𝓘(ℝ, EModel q) ∞ (ProjectiveCarrier n) := by
  letI := euclideanQuotientCharts n d e q g a
  letI := euclideanQuotientCharts_isManifold n d e q g a
  exact restrictedCharts_isManifold
    (I := 𝓘(ℝ, EModel q))
    (strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn)
    (strongGaugeNeighborhood_isOpen hLee hDesc hImm n d e q g a hq hn)
    (mem_strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn)

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeAtlas
