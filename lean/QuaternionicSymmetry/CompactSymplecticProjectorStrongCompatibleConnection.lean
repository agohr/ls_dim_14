import QuaternionicSymmetry.CompactSymplecticProjectorStrongAdaptedLCCommutator
import QuaternionicSymmetry.ManifoldQuaternionicAdaptedLeviCivitaMetric
import QuaternionicSymmetry.ManifoldQuaternionicAdaptedLeviCivitaTorsion
import QuaternionicSymmetry.CompactSymplecticProjectorStrongQuaternionicHermitianTangent

/-! The ordinary Levi-Civita connection of the actual projector metric,
expressed in the genuine strong-atlas orthonormal quaternionic frames,
is a compatible torsion-free quaternionic tangent connection. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongCompatibleConnection

open Manifold GeneralLeviCivitaSource
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeMetric
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongAdaptedLCCommutator
open CompactSymplecticProjectorCarrierConnected
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldQuaternionicConnection
open ManifoldQuaternionicAdaptedLeviCivitaForm
open ManifoldQuaternionicAdaptedLeviCivitaOverlap
open ManifoldQuaternionicAdaptedLeviCivitaMetric
open ManifoldQuaternionicAdaptedLeviCivitaTorsion
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff Topology
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

def actualCompatibleTangentConnection
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
    CoordinateLeviCivitaConnection
      (smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn) →
    CompatibleTangentConnection
      (strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  letI : ConnectedSpace (ProjectiveCarrier n) := projectiveCarrier_connectedSpace n
  have hqpos : 0 < q := by omega
  letI : Nonempty (Fin q) := ⟨⟨0, hqpos⟩⟩
  letI : Nontrivial (EModel q) := inferInstance
  intro D
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  let metric := smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn
  have hmetric : ∀ x (v w : TangentSpace 𝓘(ℝ,EModel q) x),
      metric.inner x v w = Q.tangentMetricForm x v w := by
    intro x v w
    exact (strongQuaternionicHermitianTangent_metric_eq_projector
      hLee hDesc hImm n d e q g a hq hn x v w).symm
  exact {
    form := adaptedLeviCivitaForm Q metric D
    smooth_form := adaptedLeviCivitaForm_smooth Q metric D
    overlap := adaptedLeviCivitaForm_overlap Q metric D
    metric := by
      intro p y u v w hy
      exact adaptedLeviCivitaForm_metric Q metric D hmetric p y hy u v w
    quaternionic := by
      intro p y u t hy
      have h := actual_adaptedLeviCivita_commutator
        hLee hDesc hImm n d e q g a hq hn D p y hy t u
      convert h using 1
    torsion := by
      intro p y u v hy
      exact adaptedLeviCivitaForm_torsion Q metric D p y hy u v
  }

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongCompatibleConnection
