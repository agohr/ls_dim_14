import QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeChartIndex
import QuaternionicSymmetry.CompactSymplecticProjectorStrongTangentFrameGauge
import QuaternionicSymmetry.CompactSymplecticProjectorStrongFrameMetricCompatibility

/-! The concrete Frobenius metric makes every frame of the actual
arbitrary-index strong tangent gauge orthonormal after transport to the
point's preferred tangent chart. The atlas index is not replaced by an
unrelated chosen local section. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongIndexedFrameMetric

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeChartCenter
open CompactSymplecticProjectorStrongGaugeChartIndex
open CompactSymplecticProjectorStrongTangentFrameGauge
open CompactSymplecticProjectorStrongFrameMetricCompatibility
open CompactSymplecticProjectorStrongGaugeMetric
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem strongIndexedFrame_metric_orthonormal
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
    ∀ (i : atlas (EModel q) (ProjectiveCarrier n)) (y : ProjectiveCarrier n),
      y ∈ F.adaptedCore.baseSet i →
      ∀ v w : EModel q,
        (smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn).inner y
          ((tangentBundleCore 𝓘(ℝ, EModel q) (ProjectiveCarrier n)).coordChange
            i ((tangentBundleCore 𝓘(ℝ, EModel q) (ProjectiveCarrier n)).indexAt y) y
            (F.fromFrame i y v))
          ((tangentBundleCore 𝓘(ℝ, EModel q) (ProjectiveCarrier n)).coordChange
            i ((tangentBundleCore 𝓘(ℝ, EModel q) (ProjectiveCarrier n)).indexAt y) y
            (F.fromFrame i y w)) = inner ℝ v w := by
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
  intro i y hy v w
  let x := strongChartCenter hLee hDesc hImm n d e q g a hq hn i
  have hi : i = achart (EModel q) x := by
    apply Subtype.ext
    exact strongIndex_eq_preferredChart hLee hDesc hImm n d e q g a hq hn i
  have hW : y ∈ strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x := by
    apply mem_strongGaugeNeighborhood_of_chart_source
      hLee hDesc hImm n d e q g a hq hn i y
    exact hy
  have hMetric := localStrongFrame_metric_orthonormal
    hLee hDesc hImm n d e q g a hq hn x y hW v w
  change (smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn).inner y
      ((tangentBundleCore 𝓘(ℝ, EModel q) (ProjectiveCarrier n)).coordChange
        i (achart (EModel q) y) y
        (CompactSymplecticProjectorStrongOrthonormalCoordinateFrame.localOrthonormalFromFrame
          hLee hDesc hImm n d e q g a hq hn x y v))
      ((tangentBundleCore 𝓘(ℝ, EModel q) (ProjectiveCarrier n)).coordChange
        i (achart (EModel q) y) y
        (CompactSymplecticProjectorStrongOrthonormalCoordinateFrame.localOrthonormalFromFrame
          hLee hDesc hImm n d e q g a hq hn x y w)) = _
  rw [hi]
  exact hMetric

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongIndexedFrameMetric
