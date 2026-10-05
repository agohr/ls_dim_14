import QuaternionicSymmetry.CompactSymplecticProjectorStrongTranslationDiffeomorph
import QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeMetric
import QuaternionicSymmetry.CompactSymplecticProjectorSmoothAction

/-! The actual Frobenius pullback metric is invariant under every compact
symplectic translation in the strong quotient atlas, not only reflections. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongTranslationMetric

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongTranslationDiffeomorph
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeMetric
open CompactSymplecticProjectorSmoothAction
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorAmbientMetric
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff

noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)
private abbrev Mat (n : ℕ) :=
  Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℂ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

theorem translation_metric_invariant_strong
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (u : G n) (y : ProjectiveCarrier n) :
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    ∀ v w : EModel q,
      (smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn).inner
        (leftCosetAction n u y)
        (mfderiv 𝓘(ℝ, EModel q) 𝓘(ℝ, EModel q) (leftCosetAction n u) y v)
        (mfderiv 𝓘(ℝ, EModel q) 𝓘(ℝ, EModel q) (leftCosetAction n u) y w) =
      (smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn).inner
        y v w := by
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  have hAct : ContMDiff 𝓘(ℝ, EModel q) 𝓘(ℝ, EModel q) ∞
      (leftCosetAction n u) := by
    have hf : (strongLeftCosetDiffeomorph hLee hDesc hImm
        n d e q g a hq hn u : ProjectiveCarrier n → ProjectiveCarrier n) =
          leftCosetAction n u := by
      funext z
      exact strongLeftCosetDiffeomorph_apply hLee hDesc hImm n d e q g a hq hn u z
    rw [← hf]
    exact (strongLeftCosetDiffeomorph hLee hDesc hImm
      n d e q g a hq hn u).contMDiff
  have hEq : ∀ z : ProjectiveCarrier n,
      quotientOrbitProjector n (leftCosetAction n u z) =
        conjugationCLM n u (quotientOrbitProjector n z) := by
    intro z
    simpa only [conjugationCLM_apply] using quotient_projector_equivariant n u z
  intro v w
  change frobeniusCLM n
      (mfderiv 𝓘(ℝ, EModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) (leftCosetAction n u y)
        (mfderiv 𝓘(ℝ, EModel q) 𝓘(ℝ, EModel q)
          (leftCosetAction n u) y v))
      (mfderiv 𝓘(ℝ, EModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) (leftCosetAction n u y)
        (mfderiv 𝓘(ℝ, EModel q) 𝓘(ℝ, EModel q)
          (leftCosetAction n u) y w)) =
    frobeniusCLM n
      (mfderiv 𝓘(ℝ, EModel q) 𝓘(ℝ, Mat n) (quotientOrbitProjector n) y v)
      (mfderiv 𝓘(ℝ, EModel q) 𝓘(ℝ, Mat n) (quotientOrbitProjector n) y w)
  exact ManifoldEquivariantPullbackPairing.pullback_pairing_invariant
    (quotientOrbitProjector n) (leftCosetAction n u)
    (conjugationCLM n u)
    (smooth_quotientOrbitProjector_strongGauge
      hLee hDesc hImm n d e q g a hq hn)
    hAct hEq (frobeniusCLM n)
    (frobeniusCLM_conjugationCLM n u) y v w

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongTranslationMetric
