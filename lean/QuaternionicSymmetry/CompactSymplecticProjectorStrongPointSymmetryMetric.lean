import QuaternionicSymmetry.CompactSymplecticProjectorStrongPointSymmetry
import QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeMetric
import QuaternionicSymmetry.CompactSymplecticProjectorSmoothAction

/-! The genuine point reflection preserves the Frobenius pullback metric
directly in the strong quotient atlas, by smooth projector equivariance. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongPointSymmetryMetric

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongPointSymmetry
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeMetric
open CompactSymplecticProjectorSmoothAction
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorAmbientMetric
open CompactSymplecticProjectorReflection
open CompactSymplecticProjectorPointSymmetry
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)
private abbrev Mat (n : ℕ) :=
  Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℂ

theorem pointSymmetry_metric_invariant_strong
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x y : ProjectiveCarrier n) :
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    ∀ v w : EModel q,
      (smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn).inner
        (pointSymmetry n x y)
        (mfderiv 𝓘(ℝ, EModel q) 𝓘(ℝ, EModel q) (pointSymmetry n x) y v)
        (mfderiv 𝓘(ℝ, EModel q) 𝓘(ℝ, EModel q) (pointSymmetry n x) y w) =
      (smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn).inner
        y v w := by
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  have hAct : ContMDiff 𝓘(ℝ, EModel q) 𝓘(ℝ, EModel q) ∞
      (pointSymmetry n x) := by
    have hf : (strongPointSymmetryDiffeomorph hLee hDesc hImm
        n d e q g a hq hn x : ProjectiveCarrier n → ProjectiveCarrier n) =
          pointSymmetry n x := by
      funext z
      exact strongPointSymmetry_apply hLee hDesc hImm n d e q g a hq hn x z
    rw [← hf]
    exact (strongPointSymmetryDiffeomorph hLee hDesc hImm
      n d e q g a hq hn x).contMDiff
  have hEq : ∀ z : ProjectiveCarrier n,
      quotientOrbitProjector n (pointSymmetry n x z) =
        conjugationCLM n (reflectionElement n x) (quotientOrbitProjector n z) := by
    intro z
    simpa only [pointSymmetry, conjugationCLM_apply] using
      quotient_projector_equivariant n (reflectionElement n x) z
  intro v w
  change frobeniusCLM n
      (mfderiv 𝓘(ℝ, EModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) (pointSymmetry n x y)
        (mfderiv 𝓘(ℝ, EModel q) 𝓘(ℝ, EModel q)
          (pointSymmetry n x) y v))
      (mfderiv 𝓘(ℝ, EModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) (pointSymmetry n x y)
        (mfderiv 𝓘(ℝ, EModel q) 𝓘(ℝ, EModel q)
          (pointSymmetry n x) y w)) =
    frobeniusCLM n
      (mfderiv 𝓘(ℝ, EModel q) 𝓘(ℝ, Mat n) (quotientOrbitProjector n) y v)
      (mfderiv 𝓘(ℝ, EModel q) 𝓘(ℝ, Mat n) (quotientOrbitProjector n) y w)
  exact ManifoldEquivariantPullbackPairing.pullback_pairing_invariant
    (quotientOrbitProjector n) (pointSymmetry n x)
    (conjugationCLM n (reflectionElement n x))
    (smooth_quotientOrbitProjector_strongGauge
      hLee hDesc hImm n d e q g a hq hn)
    hAct hEq (frobeniusCLM n)
    (frobeniusCLM_conjugationCLM n (reflectionElement n x)) y v w

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongPointSymmetryMetric
