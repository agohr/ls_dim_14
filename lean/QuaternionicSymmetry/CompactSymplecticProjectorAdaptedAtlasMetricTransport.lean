import QuaternionicSymmetry.CompactSymplecticProjectorAdaptedAtlasPlane
import QuaternionicSymmetry.ManifoldChartRefinementDifferential

/-! The concrete Frobenius metric is unchanged pointwise when the
Euclidean quotient charts are restricted to gauge neighborhoods. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAdaptedAtlasMetricTransport

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorAmbientMetric
open CompactSymplecticProjectorEuclideanCharts
open CompactSymplecticProjectorEuclideanSelfModelOrbit
open CompactSymplecticProjectorEuclideanSelfModelMetric
open CompactSymplecticProjectorAdaptedNeighborhoodAtlas
open CompactSymplecticProjectorAdaptedAtlasMetric
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldChartRefinementDifferential
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ
private abbrev EModel (d : ℕ) := EuclideanSpace ℝ (Fin d)

theorem smoothProjectorMetric_adapted_eq_self
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) :
    letI := euclideanQuotientCharts n d e q g a
    letI := euclideanQuotientCharts_isManifold n d e q g a
    letI := adaptedEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := adaptedEuclideanQuotientCharts_isManifold
      hLee hDesc hImm n d e q g a hq hn
    ∀ v w : EModel q,
      (smoothProjectorMetric_adaptedAtlas hLee hDesc hImm n d e q g a hq hn).inner
        x v w =
      (letI := euclideanQuotientCharts n d e q g a
       letI := euclideanQuotientCharts_isManifold n d e q g a
       (smoothProjectorMetric_selfModel hDesc hImm n d e q g a).inner x v w) := by
  letI := euclideanQuotientCharts n d e q g a
  letI := euclideanQuotientCharts_isManifold n d e q g a
  let W := actualGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn
  have hD := mfderiv_restrictedCharts_eq (I := 𝓘(ℝ, EModel q))
    (J := 𝓘(ℝ, Mat n)) W
    (actualGaugeNeighborhood_isOpen hLee hDesc hImm n d e q g a hq hn)
    (mem_actualGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn)
    (quotientOrbitProjector n) x
    ((smooth_quotientOrbitProjector_selfModel hDesc n d e q g a).mdifferentiableAt
      (by simp))
  intro v w
  change frobeniusCLM n
      ((@mfderiv ℝ _ (EModel q) _ _ (EModel q) _ 𝓘(ℝ, EModel q)
        (ProjectiveCarrier n) _
        (adaptedEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn)
        (Mat n) _ _ (Mat n) _ 𝓘(ℝ, Mat n) (Mat n) _
        (inferInstance : ChartedSpace (Mat n) (Mat n))
        (quotientOrbitProjector n) x) v)
      ((@mfderiv ℝ _ (EModel q) _ _ (EModel q) _ 𝓘(ℝ, EModel q)
        (ProjectiveCarrier n) _
        (adaptedEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn)
        (Mat n) _ _ (Mat n) _ 𝓘(ℝ, Mat n) (Mat n) _
        (inferInstance : ChartedSpace (Mat n) (Mat n))
        (quotientOrbitProjector n) x) w) = _
  rw [hD]
  rfl

end
end QuaternionicSymmetry.CompactSymplecticProjectorAdaptedAtlasMetricTransport
