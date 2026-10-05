import QuaternionicSymmetry.CompactSymplecticProjectorCarrierConnected
import QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeMetric
import QuaternionicSymmetry.GeneralLeviCivitaSource

/-! The audited general Petersen Levi-Civita theorem applies to the actual
connected strong-atlas projector quotient and its constructed Frobenius
Riemannian metric. This supplies only ordinary torsion-free, metric-compatible
coordinate connection forms, not quaternionic parallelism or curvature. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorLeviCivita

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorCarrierConnected
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeMetric
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open GeneralLeviCivitaSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section


private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem actual_projector_leviCivita
    (hPetersen : PetersenLeviCivitaExistenceTheorem.{0, 0})
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) :
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold
      hLee hDesc hImm n d e q g a hq hn
    Nonempty (CoordinateLeviCivitaConnection
      (smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn)) := by
  letI : ConnectedSpace (ProjectiveCarrier n) := projectiveCarrier_connectedSpace n
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold
    hLee hDesc hImm n d e q g a hq hn
  exact hPetersen (EModel q) (ProjectiveCarrier n)
    (smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn)

end
end QuaternionicSymmetry.CompactSymplecticProjectorLeviCivita
