import QuaternionicSymmetry.GeneralImmersionChartPullbackMetric
import QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeMetric

/-! In every genuine strong quotient chart, the constructed Riemannian
metric is exactly the Frobenius pairing of first derivatives of the
actual projector immersion in that chart. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongChartMetricPullback

open Manifold Bundle GeneralLeviCivitaSource
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeMetric
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open CompactSymplecticProjectorAmbientMetric
open CompactSymplecticProjectorOrbitQuotient
open GeneralImmersionChartPullbackMetric
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff Topology
noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)
private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ

theorem actual_chartMetric_eq_frobenius_chart_derivatives
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
    ∀ (p : ProjectiveCarrier n) (y : EModel q)
      (hy : y ∈ (extChartAt 𝓘(ℝ,EModel q) p).target)
      (u v : EModel q),
      chartMetric
        (smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn)
        p y u v =
      frobeniusCLM n
        (fderiv ℝ (quotientOrbitProjector n ∘
          (extChartAt 𝓘(ℝ,EModel q) p).symm) y u)
        (fderiv ℝ (quotientOrbitProjector n ∘
          (extChartAt 𝓘(ℝ,EModel q) p).symm) y v) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  intro p y hy u v
  have hmetric : ∀ x (v w : TangentSpace 𝓘(ℝ,EModel q) x),
      (smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn).inner
        x v w = frobeniusCLM n
          (mfderiv 𝓘(ℝ,EModel q) 𝓘(ℝ,Mat n)
            (quotientOrbitProjector n) x v)
          (mfderiv 𝓘(ℝ,EModel q) 𝓘(ℝ,Mat n)
            (quotientOrbitProjector n) x w) := by
    intro x v w
    exact ManifoldImmersionPullbackMetricGeneral.metricCLM_apply
      (I := 𝓘(ℝ,EModel q)) (E := EModel q)
      (quotientOrbitProjector n) (frobeniusCLM n) x v w
  exact chartMetric_eq_ambient_chart_derivatives
    (quotientOrbitProjector n) (frobeniusCLM n)
    (smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn)
    (smooth_quotientOrbitProjector_strongGauge
      hLee hDesc hImm n d e q g a hq hn)
    hmetric p y hy u v

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongChartMetricPullback
