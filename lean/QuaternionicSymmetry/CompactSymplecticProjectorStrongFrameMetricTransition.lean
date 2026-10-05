import QuaternionicSymmetry.CompactSymplecticProjectorStrongIndexedFrameMetric
import QuaternionicSymmetry.ManifoldTangentFrameMetricOverlap

/-! Every transition of the actual smooth adapted strong tangent frame is
orthogonal, derived from its checked pointwise Frobenius orthonormality
and the genuine tangent-core cocycle. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongFrameMetricTransition

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongTangentFrameGauge
open CompactSymplecticProjectorStrongIndexedFrameMetric
open CompactSymplecticProjectorStrongGaugeMetric
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldTangentFrameMetricOverlap
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem strongFrameTransition_inner
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
    ∀ (i j : atlas (EModel q) (ProjectiveCarrier n)) (y : ProjectiveCarrier n),
      y ∈ F.adaptedCore.baseSet i → y ∈ F.adaptedCore.baseSet j →
      ∀ v w : EModel q,
        inner ℝ (F.coordChange i j y v) (F.coordChange i j y w) = inner ℝ v w := by
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
  intro i j y hi hj v w
  let F := strongTangentFrameGauge hLee hDesc hImm n d e q g a hq hn
  let m := smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn
  exact transition_inner_of_preferred_orthonormal F
    (fun y v w => m.inner y v w)
    (fun i y hi v w => strongIndexedFrame_metric_orthonormal
      hLee hDesc hImm n d e q g a hq hn i y hi v w)
    i j y hi hj v w

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongFrameMetricTransition
