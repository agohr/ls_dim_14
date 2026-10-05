import QuaternionicSymmetry.CompactSymplecticProjectorStrongQuaternionicReduction
import QuaternionicSymmetry.CompactSymplecticProjectorStrongFrameMetricTransition
import QuaternionicSymmetry.CompactSymplecticProjectorStrongFrameMetricIdentification
import QuaternionicSymmetry.ManifoldQuaternionicMetric

/-! The actual compact symplectic projector quotient carries a smooth
metric-adapted quaternionic tangent reduction. Its metric is exactly the
previously constructed Frobenius pullback metric. This does not yet prove
Levi-Civita parallelism or positive curvature. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongQuaternionicHermitianTangent

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongTangentFrameGauge
open CompactSymplecticProjectorStrongQuaternionicReduction
open CompactSymplecticProjectorStrongFrameMetricTransition
open CompactSymplecticProjectorStrongFrameMetricIdentification
open CompactSymplecticProjectorStrongGaugeMetric
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldQuaternionicMetric
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

def strongQuaternionicHermitianTangent
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) :
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ, EModel q)) (M := ProjectiveCarrier n) (n := ∞) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := CompactSymplecticProjectorEuclideanModel.euclideanModel_isManifold n d e q g a
  letI := CompactSymplecticProjectorEuclideanCharts.euclideanQuotientCharts n d e q g a
  letI := CompactSymplecticProjectorEuclideanCharts.euclideanQuotientCharts_isManifold n d e q g a
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  letI : IsManifold 𝓘(ℝ, EModel q) 1 (ProjectiveCarrier n) :=
    (strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn).of_le
      (by norm_cast)
  exact {
    frames := strongTangentFrameGauge hLee hDesc hImm n d e q g a hq hn
    reduction := strongQuaternionicReduction hLee hDesc hImm n d e q g a hq hn
    transition_inner := strongFrameTransition_inner hLee hDesc hImm n d e q g a hq hn }

theorem strongQuaternionicHermitianTangent_metric_eq_projector
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := CompactSymplecticProjectorEuclideanModel.euclideanModel_isManifold n d e q g a
    letI := CompactSymplecticProjectorEuclideanCharts.euclideanQuotientCharts n d e q g a
    letI := CompactSymplecticProjectorEuclideanCharts.euclideanQuotientCharts_isManifold n d e q g a
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    ∀ y (v w : EModel q),
      (strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn).tangentMetricForm
        y v w =
      (smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn).inner y v w := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := CompactSymplecticProjectorEuclideanModel.euclideanModel_isManifold n d e q g a
  letI := CompactSymplecticProjectorEuclideanCharts.euclideanQuotientCharts n d e q g a
  letI := CompactSymplecticProjectorEuclideanCharts.euclideanQuotientCharts_isManifold n d e q g a
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  letI : IsManifold 𝓘(ℝ, EModel q) 1 (ProjectiveCarrier n) :=
    (strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn).of_le
      (by norm_cast)
  intro y v w
  rw [SmoothQuaternionicHermitianTangent.tangentMetricForm_apply]
  exact (strongAdaptedMetric_eq_projectorMetric
    hLee hDesc hImm n d e q g a hq hn y v w).symm

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongQuaternionicHermitianTangent
