import QuaternionicSymmetry.CompactSymplecticProjectorEuclideanSelfModelMetricTransport
import QuaternionicSymmetry.CompactSymplecticProjectorEuclideanQuaternionicMetric

/-! The actual translated quaternionic generators are orthogonal for
the genuine Euclidean self-model Frobenius metric. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorEuclideanSelfModelQuaternionicMetric

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseQuaternionic
open CompactSymplecticProjectorTranslationTangentEquiv
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorEuclideanCharts
open CompactSymplecticProjectorEuclideanSelfModelPlane
open CompactSymplecticProjectorEuclideanSelfModelMetric
open CompactSymplecticProjectorEuclideanSelfModelMetricTransport
open CompactSymplecticProjectorEuclideanQuaternionicMetric
open CompactSymplecticProjectorEuclideanRiemannianMetric
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section
set_option maxHeartbeats 5000000

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev EModel (d : ℕ) := EuclideanSpace ℝ (Fin d)
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

theorem selfModel_translated_generators_metric_compatible
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (u : G n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := euclideanModel_isManifold n d e q g a
    letI := euclideanQuotientCharts n d e q g a
    letI := euclideanQuotientCharts_isManifold n d e q g a
    ∀ S ∈ ({(baseI hDesc hImm n d e q g a hq).toLinearMap,
      (baseJ hDesc hImm n d e q g a hq).toLinearMap,
      (baseK hDesc hImm n d e q g a hq).toLinearMap} :
        Set (Module.End ℝ (TangentSpace 𝓘(ℝ, RModel q) (baseCoset n)))),
      ∀ v w : TangentSpace 𝓘(ℝ, EModel q)
          (leftCosetAction n u (baseCoset n)),
        (smoothProjectorMetric_selfModel hDesc hImm n d e q g a).inner
          (leftCosetAction n u (baseCoset n))
          (((selfModelTangentEquiv n d e q g a
            (leftCosetAction n u (baseCoset n))).toLinearEquiv.conjAlgEquiv ℝ)
            (((CompactSymplecticProjectorEuclideanQuaternionicPlane.euclideanTangentEquiv
              n d e q g a (leftCosetAction n u (baseCoset n))).toLinearEquiv.conjAlgEquiv ℝ)
              (((translationTangentEquiv n d e q g a u (baseCoset n)).toLinearEquiv.conjAlgEquiv ℝ) S)) v)
          (((selfModelTangentEquiv n d e q g a
            (leftCosetAction n u (baseCoset n))).toLinearEquiv.conjAlgEquiv ℝ)
            (((CompactSymplecticProjectorEuclideanQuaternionicPlane.euclideanTangentEquiv
              n d e q g a (leftCosetAction n u (baseCoset n))).toLinearEquiv.conjAlgEquiv ℝ)
              (((translationTangentEquiv n d e q g a u (baseCoset n)).toLinearEquiv.conjAlgEquiv ℝ) S)) w) =
        (smoothProjectorMetric_selfModel hDesc hImm n d e q g a).inner
          (leftCosetAction n u (baseCoset n)) v w := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := euclideanModel_isManifold n d e q g a
  letI := euclideanQuotientCharts n d e q g a
  letI := euclideanQuotientCharts_isManifold n d e q g a
  let x := leftCosetAction n u (baseCoset n)
  let D := selfModelTangentEquiv n d e q g a x
  let T := (CompactSymplecticProjectorEuclideanQuaternionicPlane.euclideanTangentEquiv
    n d e q g a x).toLinearEquiv
  let U := (translationTangentEquiv n d e q g a u (baseCoset n)).toLinearEquiv
  intro S hS v w
  have hOld := euclidean_translated_generators_metric_compatible
    hDesc hImm n d e q g a hq u S hS (D.symm v) (D.symm w)
  have hMetric := smoothProjectorMetric_selfModelChange hDesc hImm n d e q g a x
  have hLeft := hMetric ((T.conjAlgEquiv ℝ) ((U.conjAlgEquiv ℝ) S) (D.symm v))
    ((T.conjAlgEquiv ℝ) ((U.conjAlgEquiv ℝ) S) (D.symm w))
  have hRight := hMetric (D.symm v) (D.symm w)
  change (smoothProjectorMetric_selfModel hDesc hImm n d e q g a).inner x
      (D ((T.conjAlgEquiv ℝ) ((U.conjAlgEquiv ℝ) S) (D.symm v)))
      (D ((T.conjAlgEquiv ℝ) ((U.conjAlgEquiv ℝ) S) (D.symm w))) = _ at hLeft
  change (smoothProjectorMetric_selfModel hDesc hImm n d e q g a).inner x
      (D (D.symm v)) (D (D.symm w)) = _ at hRight
  rw [D.apply_symm_apply, D.apply_symm_apply] at hRight
  exact hLeft.trans (hOld.trans hRight.symm)

end
end QuaternionicSymmetry.CompactSymplecticProjectorEuclideanSelfModelQuaternionicMetric
