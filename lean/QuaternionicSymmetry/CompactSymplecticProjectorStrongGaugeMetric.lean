import QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeAtlas
import QuaternionicSymmetry.CompactSymplecticProjectorEuclideanSelfModelOrbit
import QuaternionicSymmetry.ManifoldChartRefinementDifferential
import QuaternionicSymmetry.ManifoldImmersionPullbackMetricGeneral
import QuaternionicSymmetry.FinitePositiveBilinearBounded
import QuaternionicSymmetry.CompactSymplecticProjectorAmbientMetric

/-! The stronger smooth-section atlas carries the same actual smooth
projector immersion and its positive Frobenius-pullback Riemannian metric. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeMetric

open Manifold Bundle
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorAmbientMetric
open CompactSymplecticProjectorEuclideanCharts
open CompactSymplecticProjectorEuclideanSelfModelOrbit
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldChartRefinementDifferential
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ
private abbrev EModel (d : ℕ) := EuclideanSpace ℝ (Fin d)

theorem smooth_quotientOrbitProjector_strongGauge
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) :
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    ContMDiff 𝓘(ℝ, EModel q) 𝓘(ℝ, Mat n) ∞
      (quotientOrbitProjector n) := by
  letI := euclideanQuotientCharts n d e q g a
  letI := euclideanQuotientCharts_isManifold n d e q g a
  simpa [ContMDiff, contMDiffAt_iff, extChartAt,
    strongEuclideanQuotientCharts, ManifoldChartRefinement.restrictedCharts,
    mfld_simps] using
    (smooth_quotientOrbitProjector_selfModel hDesc n d e q g a)

theorem quotientOrbitProjector_mfderiv_injective_strongGauge
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) :
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    Function.Injective
      (mfderiv 𝓘(ℝ, EModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) x) := by
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
  simpa [W, strongEuclideanQuotientCharts] using
    (hD.symm ▸ quotientOrbitProjector_mfderiv_injective_selfModel
      hDesc hImm n d e q g a x)

def smoothProjectorMetric_strongGauge
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) :
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold
      hLee hDesc hImm n d e q g a hq hn
    ContMDiffRiemannianMetric 𝓘(ℝ, EModel q) ∞ (EModel q)
      (TangentSpace 𝓘(ℝ, EModel q) : ProjectiveCarrier n → Type _) := by
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold
    hLee hDesc hImm n d e q g a hq hn
  exact ManifoldImmersionPullbackMetricGeneral.smoothMetric
    (I := 𝓘(ℝ, EModel q)) (E := EModel q)
    (quotientOrbitProjector n) (frobeniusCLM n)
    (smooth_quotientOrbitProjector_strongGauge
      hLee hDesc hImm n d e q g a hq hn)
    (quotientOrbitProjector_mfderiv_injective_strongGauge
      hLee hDesc hImm n d e q g a hq hn)
    (frobeniusCLM_symm n) (frobeniusCLM_pos n)
    (FinitePositiveBilinearBounded.unitBall_isVonNBounded
      (frobeniusCLM n) (frobeniusCLM_pos n))

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeMetric
