import QuaternionicSymmetry.CompactSymplecticProjectorStrongChartNoncommuting
import QuaternionicSymmetry.CompactSymplecticProjectorStrongScalarPosOfChartPair
import QuaternionicSymmetry.CompactSymplecticProjectorLeviCivita

/-! The genuine compact projector quotient has strictly positive scalar
curvature at every point for its actual quaternionic-compatible
Levi-Civita connection. The general Petersen source supplies only
ordinary Levi-Civita existence; positivity follows internally from
the proved model immersion and quaternionic tangent orbit geometry. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongScalarPositiveEverywhere

open Matrix Manifold Bundle GeneralLeviCivitaSource
open ManifoldQuaternionicConnection
open ManifoldQuaternionicScalarCurvature
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeMetric
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongCompatibleConnection
open CompactSymplecticProjectorStrongChartNoncommuting
open CompactSymplecticProjectorStrongScalarPosOfChartPair
open CompactSymplecticProjectorLeviCivita
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff Topology
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem actual_scalarCurvature_pos_on_chart
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    ∀ (D : CoordinateLeviCivitaConnection
        (smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn))
      (p : ProjectiveCarrier n) (y : EModel q)
      (hy : y ∈ (extChartAt 𝓘(ℝ,EModel q) p).target),
      0 < localScalarCurvature
        (strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn)
        (actualCompatibleTangentConnection hLee hDesc hImm n d e q g a hq hn D)
        p y hy := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  intro D p y hy
  apply actual_scalar_pos_of_chart_noncommuting_pair
    hLee hDesc hImm n d e q g a hq hn D p y hy
  exact actual_chartDerivative_noncommuting_everywhere
    hLee hDesc hImm n d e q g a hq hn p y hy

theorem actual_preferredScalarCurvature_pos
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    ∀ (D : CoordinateLeviCivitaConnection
        (smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn))
      (x : ProjectiveCarrier n),
      0 < preferredScalarCurvature
        (strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn)
        (actualCompatibleTangentConnection hLee hDesc hImm n d e q g a hq hn D)
        x := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  intro D x
  exact actual_scalarCurvature_pos_on_chart
    hLee hDesc hImm n d e q g a hq hn D x
      (extChartAt 𝓘(ℝ,EModel q) x x)
      ((extChartAt 𝓘(ℝ,EModel q) x).map_source (by simp))

theorem actual_positiveScalar_leviCivita_exists
    (hPetersen : PetersenLeviCivitaExistenceTheorem.{0, 0})
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    ∃ D : CoordinateLeviCivitaConnection
        (smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn),
      ∀ x : ProjectiveCarrier n,
        0 < preferredScalarCurvature
          (strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn)
          (actualCompatibleTangentConnection hLee hDesc hImm n d e q g a hq hn D)
          x := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  obtain ⟨D⟩ := actual_projector_leviCivita
    hPetersen hLee hDesc hImm n d e q g a hq hn
  exact ⟨D, actual_preferredScalarCurvature_pos
    hLee hDesc hImm n d e q g a hq hn D⟩

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongScalarPositiveEverywhere
