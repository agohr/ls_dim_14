import QuaternionicSymmetry.CompactSymplecticProjectorEuclideanSelfModelPlane

/-! The self-model Frobenius metric agrees exactly with the prior
Euclidean tangent metric under the genuine atlas identity differential. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorEuclideanSelfModelMetricTransport

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorAmbientMetric
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorEuclideanCharts
open CompactSymplecticProjectorEuclideanChartBridge
open CompactSymplecticProjectorEuclideanSelfModelOrbit
open CompactSymplecticProjectorEuclideanSelfModelPlane
open CompactSymplecticProjectorEuclideanSelfModelMetric
open CompactSymplecticProjectorEuclideanModelSmoothOrbit
open CompactSymplecticProjectorEuclideanRiemannianMetric
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section
set_option maxHeartbeats 5000000

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ
private abbrev EModel (d : ℕ) := EuclideanSpace ℝ (Fin d)

theorem quotientOrbitProjector_mfderiv_selfModelChange
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (x : ProjectiveCarrier n) :
    letI := a.quotientCharts
    letI := euclideanQuotientCharts n d e q g a
    mfderiv (euclideanModel q) 𝓘(ℝ, Mat n)
      (quotientOrbitProjector n) x =
      (mfderiv 𝓘(ℝ, EModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) x).comp
        (selfModelTangentEquiv n d e q g a x : _ →L[ℝ] _) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := euclideanModel_isManifold n d e q g a
  letI := euclideanQuotientCharts n d e q g a
  letI := euclideanQuotientCharts_isManifold n d e q g a
  let Φ := euclideanChartDiffeomorph n d e q g a
  have hΦx : Φ x = x := rfl
  have h := mfderiv_comp x
    ((smooth_quotientOrbitProjector_selfModel hDesc n d e q g a).mdifferentiableAt
      (by simp))
    (Φ.contMDiff_toFun.mdifferentiableAt (by simp))
  simpa only [Function.comp_def, hΦx, selfModelTangentEquiv,
    Diffeomorph.mfderivToContinuousLinearEquiv_coe] using h

theorem smoothProjectorMetric_selfModelChange
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (x : ProjectiveCarrier n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := euclideanModel_isManifold n d e q g a
    letI := euclideanQuotientCharts n d e q g a
    letI := euclideanQuotientCharts_isManifold n d e q g a
    ∀ v w : TangentSpace (euclideanModel q) x,
      (smoothProjectorMetric_selfModel hDesc hImm n d e q g a).inner x
        (selfModelTangentEquiv n d e q g a x v)
        (selfModelTangentEquiv n d e q g a x w) =
      (smoothProjectorMetric_euclideanModel hDesc hImm n d e q g a).inner x v w := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := euclideanModel_isManifold n d e q g a
  letI := euclideanQuotientCharts n d e q g a
  letI := euclideanQuotientCharts_isManifold n d e q g a
  intro v w
  change frobeniusCLM n
      (mfderiv 𝓘(ℝ, EModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) x (selfModelTangentEquiv n d e q g a x v))
      (mfderiv 𝓘(ℝ, EModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) x (selfModelTangentEquiv n d e q g a x w)) =
    frobeniusCLM n
      (mfderiv (euclideanModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) x v)
      (mfderiv (euclideanModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) x w)
  have hD := quotientOrbitProjector_mfderiv_selfModelChange hDesc n d e q g a x
  rw [hD]
  rfl

end
end QuaternionicSymmetry.CompactSymplecticProjectorEuclideanSelfModelMetricTransport
