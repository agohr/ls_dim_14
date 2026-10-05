import QuaternionicSymmetry.CompactSymplecticProjectorEuclideanQuaternionicPlane
import QuaternionicSymmetry.CompactSymplecticProjectorRiemannianMetric

/-! The Euclidean-model Frobenius metric is exactly the original
projector metric transported by the genuine identity-diffeomorphism
differential, not an unrelated metric choice. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorEuclideanMetricTransport

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorEuclideanModelSmoothOrbit
open CompactSymplecticProjectorEuclideanQuaternionicPlane
open CompactSymplecticProjectorEuclideanRiemannianMetric
open CompactSymplecticProjectorRiemannianMetric
open CompactSymplecticProjectorAmbientMetric
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section
set_option maxHeartbeats 5000000

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ
private abbrev RModel (d : ℕ) := Fin d → ℝ

theorem quotientOrbitProjector_mfderiv_modelChange
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (x : ProjectiveCarrier n) :
    letI := a.quotientCharts
    mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, Mat n)
      (quotientOrbitProjector n) x =
      (mfderiv (euclideanModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) x).comp
        (euclideanTangentEquiv n d e q g a x : _ →L[ℝ] _) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  let Φ := euclideanModelDiffeomorph n d e q g a
  have hΦx : Φ x = x := rfl
  have h := mfderiv_comp x
    ((smooth_quotientOrbitProjector_euclideanModel hDesc n d e q g a).mdifferentiableAt
      (by simp))
    (Φ.contMDiff_toFun.mdifferentiableAt (by simp))
  simpa only [Function.comp_def, hΦx, euclideanTangentEquiv,
    Diffeomorph.mfderivToContinuousLinearEquiv_coe] using h

theorem smoothProjectorMetric_modelChange
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (x : ProjectiveCarrier n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := euclideanModel_isManifold n d e q g a
    ∀ v w : TangentSpace 𝓘(ℝ, RModel q) x,
      (smoothProjectorMetric_euclideanModel hDesc hImm n d e q g a).inner x
        (euclideanTangentEquiv n d e q g a x v)
        (euclideanTangentEquiv n d e q g a x w) =
      (smoothProjectorMetric hDesc hImm n d e q g a).inner x v w := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := euclideanModel_isManifold n d e q g a
  intro v w
  change frobeniusCLM n
      (mfderiv (euclideanModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) x (euclideanTangentEquiv n d e q g a x v))
      (mfderiv (euclideanModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) x (euclideanTangentEquiv n d e q g a x w)) =
    (smoothProjectorMetric hDesc hImm n d e q g a).inner x v w
  rw [smoothProjectorMetric_apply hDesc hImm n d e q g a x]
  have hD := quotientOrbitProjector_mfderiv_modelChange hDesc n d e q g a x
  rw [hD]
  rfl

end
end QuaternionicSymmetry.CompactSymplecticProjectorEuclideanMetricTransport
