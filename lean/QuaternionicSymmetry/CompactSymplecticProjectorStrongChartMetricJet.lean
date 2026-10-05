import QuaternionicSymmetry.GeneralImmersionChartMetricDerivative
import QuaternionicSymmetry.CompactSymplecticProjectorStrongChartMetricPullback

/-! The genuine first jet of the actual Frobenius projector metric,
in every strong quotient chart, is its ambient projector Hessian pairing. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongChartMetricJet

open Manifold Bundle GeneralLeviCivitaSource
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeMetric
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open CompactSymplecticProjectorAmbientMetric
open CompactSymplecticProjectorOrbitQuotient
open GeneralImmersionChartMetricDerivative
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff Topology
noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)
private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ

theorem actual_chartMetric_first_jet_eq_projector_hessian
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
      (u v w : EModel q),
      let F := quotientOrbitProjector n ∘
        (extChartAt 𝓘(ℝ,EModel q) p).symm
      let dF := fderiv ℝ F
      let H := fderiv ℝ dF y
      fderiv ℝ
        (fun z => chartMetric
          (smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn)
          p z v w) y u =
        frobeniusCLM n (H u v) (dF y w) +
          frobeniusCLM n (dF y v) (H u w) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  intro p y hy u v w
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
  exact chartMetric_fderiv_eq_ambient_hessian
    (quotientOrbitProjector n) (frobeniusCLM n)
    (smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn)
    (smooth_quotientOrbitProjector_strongGauge
      hLee hDesc hImm n d e q g a hq hn)
    hmetric p y hy u v w

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongChartMetricJet
