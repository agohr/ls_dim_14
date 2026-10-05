import QuaternionicSymmetry.CompactSymplecticProjectorStrongCompatibleConnection
import QuaternionicSymmetry.CompactSymplecticProjectorLeviCivita

/-! The actual compact projector quotient has a metric, torsion-free,
quaternionic-compatible tangent connection, derived from the general
ordinary Levi-Civita theorem and the internally proved Q-parallelism. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongCompatibleExistence

open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongCompatibleConnection
open CompactSymplecticProjectorLeviCivita
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open GeneralLeviCivitaSource
open ManifoldQuaternionicConnection
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff Topology
noncomputable section

theorem actual_compatible_tangent_connection_exists
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
    Nonempty (CompatibleTangentConnection
      (strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn)) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  obtain ⟨D⟩ := actual_projector_leviCivita
    hPetersen hLee hDesc hImm n d e q g a hq hn
  exact ⟨actualCompatibleTangentConnection hLee hDesc hImm n d e q g a hq hn D⟩

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongCompatibleExistence
