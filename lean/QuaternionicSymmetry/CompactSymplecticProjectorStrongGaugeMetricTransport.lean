import QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeMetric
import QuaternionicSymmetry.CompactSymplecticProjectorEuclideanSelfModelMetricTransport
import QuaternionicSymmetry.CompactSymplecticProjectorEuclideanModelTangentFormula
import QuaternionicSymmetry.CompactSymplecticProjectorEuclideanChartBridgeTangent
import QuaternionicSymmetry.ManifoldChartRefinementDifferential

/-! The strong-chart Frobenius tensor is the same actual quotient metric
as the original one, under the proved canonical real→Euclidean tangent
coordinate equivalence. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeMetricTransport

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorAmbientMetric
open CompactSymplecticProjectorRiemannianMetric
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorEuclideanCharts
open CompactSymplecticProjectorEuclideanMetricTransport
open CompactSymplecticProjectorEuclideanQuaternionicPlane
open CompactSymplecticProjectorEuclideanChartBridgeTangent
open CompactSymplecticProjectorEuclideanSelfModelPlane
open CompactSymplecticProjectorEuclideanSelfModelOrbit
open CompactSymplecticProjectorEuclideanSelfModelMetric
open CompactSymplecticProjectorEuclideanSelfModelMetricTransport
open CompactSymplecticProjectorEuclideanModelTangentFormula
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeMetric
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldChartRefinementDifferential
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ
private abbrev RModel (q : ℕ) := Fin q → ℝ
private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem strongMetric_eq_selfMetric
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) :
    letI := euclideanQuotientCharts n d e q g a
    letI := euclideanQuotientCharts_isManifold n d e q g a
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold
      hLee hDesc hImm n d e q g a hq hn
    ∀ v w : EModel q,
      (smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn).inner x v w =
      (letI := euclideanQuotientCharts n d e q g a
       letI := euclideanQuotientCharts_isManifold n d e q g a
       (smoothProjectorMetric_selfModel hDesc hImm n d e q g a).inner x v w) := by
  letI := euclideanQuotientCharts n d e q g a
  letI := euclideanQuotientCharts_isManifold n d e q g a
  let W := strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn
  have hD := mfderiv_restrictedCharts_eq (I := 𝓘(ℝ, EModel q))
    (J := 𝓘(ℝ, Mat n)) W
    (strongGaugeNeighborhood_isOpen hLee hDesc hImm n d e q g a hq hn)
    (mem_strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn)
    (quotientOrbitProjector n) x
    ((smooth_quotientOrbitProjector_selfModel hDesc n d e q g a).mdifferentiableAt
      (by simp))
  intro v w
  change frobeniusCLM n
      ((@mfderiv ℝ _ (EModel q) _ _ (EModel q) _ 𝓘(ℝ, EModel q)
        (ProjectiveCarrier n) _
        (strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn)
        (Mat n) _ _ (Mat n) _ 𝓘(ℝ, Mat n) (Mat n) _
        (inferInstance : ChartedSpace (Mat n) (Mat n))
        (quotientOrbitProjector n) x) v)
      ((@mfderiv ℝ _ (EModel q) _ _ (EModel q) _ 𝓘(ℝ, EModel q)
        (ProjectiveCarrier n) _
        (strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn)
        (Mat n) _ _ (Mat n) _ 𝓘(ℝ, Mat n) (Mat n) _
        (inferInstance : ChartedSpace (Mat n) (Mat n))
        (quotientOrbitProjector n) x) w) = _
  rw [hD]
  rfl

theorem strongMetric_eq_originalMetric
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := euclideanModel_isManifold n d e q g a
    letI := euclideanQuotientCharts n d e q g a
    letI := euclideanQuotientCharts_isManifold n d e q g a
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold
      hLee hDesc hImm n d e q g a hq hn
    ∀ v w : RModel q,
      (smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn).inner x
        (euclideanModelEquiv q v) (euclideanModelEquiv q w) =
      (letI := a.quotientCharts
       letI := a.quotientManifold
       (smoothProjectorMetric hDesc hImm n d e q g a).inner x v w) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := euclideanModel_isManifold n d e q g a
  letI := euclideanQuotientCharts n d e q g a
  letI := euclideanQuotientCharts_isManifold n d e q g a
  intro v w
  rw [strongMetric_eq_selfMetric hLee hDesc hImm n d e q g a hq hn x]
  have hSelf := smoothProjectorMetric_selfModelChange hDesc hImm n d e q g a x
    (euclideanTangentEquiv n d e q g a x v)
    (euclideanTangentEquiv n d e q g a x w)
  have hOld := smoothProjectorMetric_modelChange hDesc hImm n d e q g a x v w
  simpa only [euclideanTangentEquiv_eq_coordinateEquiv,
    selfModelTangentEquiv_eq_refl, ContinuousLinearEquiv.refl_apply] using
    hSelf.trans hOld

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeMetricTransport
