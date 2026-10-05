import QuaternionicSymmetry.CompactSymplecticProjectorStrongFrameMetricTransition
import QuaternionicSymmetry.ManifoldTangentFrameMetricIdentification

/-! The metric obtained by reading tangent vectors in the actual
metric-adapted strong quotient gauge is exactly the Frobenius pullback
metric of the projector immersion, pointwise on the genuine quotient. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongFrameMetricIdentification

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongTangentFrameGauge
open CompactSymplecticProjectorStrongIndexedFrameMetric
open CompactSymplecticProjectorStrongGaugeMetric
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldTangentFrameMetricIdentification
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem strongAdaptedMetric_eq_projectorMetric
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
    letI := strongEuclideanQuotientCharts_isManifold
      hLee hDesc hImm n d e q g a hq hn
    let F := strongTangentFrameGauge hLee hDesc hImm n d e q g a hq hn
    ∀ (y : ProjectiveCarrier n) (v w : EModel q),
      (smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn).inner y v w =
      inner ℝ
        (F.toFrame ((tangentBundleCore 𝓘(ℝ, EModel q)
          (ProjectiveCarrier n)).indexAt y) y v)
        (F.toFrame ((tangentBundleCore 𝓘(ℝ, EModel q)
          (ProjectiveCarrier n)).indexAt y) y w) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := CompactSymplecticProjectorEuclideanModel.euclideanModel_isManifold n d e q g a
  letI := CompactSymplecticProjectorEuclideanCharts.euclideanQuotientCharts n d e q g a
  letI := CompactSymplecticProjectorEuclideanCharts.euclideanQuotientCharts_isManifold n d e q g a
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold
    hLee hDesc hImm n d e q g a hq hn
  letI : IsManifold 𝓘(ℝ, EModel q) 1 (ProjectiveCarrier n) :=
    (strongEuclideanQuotientCharts_isManifold
      hLee hDesc hImm n d e q g a hq hn).of_le (by norm_cast)
  dsimp only
  intro y v w
  let F := strongTangentFrameGauge hLee hDesc hImm n d e q g a hq hn
  let m := smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn
  exact preferred_frame_metric_eq F (fun y v w => m.inner y v w)
    (fun i y hi v w => strongIndexedFrame_metric_orthonormal
      hLee hDesc hImm n d e q g a hq hn i y hi v w)
    y v w

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongFrameMetricIdentification
