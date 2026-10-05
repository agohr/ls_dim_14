import QuaternionicSymmetry.CompactSymplecticProjectorAdaptedAtlasMetricTransport
import QuaternionicSymmetry.CompactSymplecticProjectorEuclideanSelfModelQuaternionicMetric

/-! The three genuinely transported quaternionic generators remain
orthogonal for the actual Frobenius metric on the gauge-refined quotient atlas. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAdaptedAtlasQuaternionicMetric

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseQuaternionic
open CompactSymplecticProjectorTranslationTangentEquiv
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorEuclideanCharts
open CompactSymplecticProjectorEuclideanSelfModelPlane
open CompactSymplecticProjectorEuclideanSelfModelQuaternionicMetric
open CompactSymplecticProjectorEuclideanQuaternionicPlane
open CompactSymplecticProjectorAdaptedNeighborhoodAtlas
open CompactSymplecticProjectorAdaptedAtlasMetric
open CompactSymplecticProjectorAdaptedAtlasMetricTransport
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev EModel (d : ℕ) := EuclideanSpace ℝ (Fin d)
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

theorem adapted_translated_generators_metric_compatible
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (u : G n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := euclideanModel_isManifold n d e q g a
    letI := euclideanQuotientCharts n d e q g a
    letI := euclideanQuotientCharts_isManifold n d e q g a
    letI := adaptedEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := adaptedEuclideanQuotientCharts_isManifold
      hLee hDesc hImm n d e q g a hq hn
    ∀ S ∈ ({(baseI hDesc hImm n d e q g a hq).toLinearMap,
      (baseJ hDesc hImm n d e q g a hq).toLinearMap,
      (baseK hDesc hImm n d e q g a hq).toLinearMap} :
        Set (Module.End ℝ (TangentSpace 𝓘(ℝ, RModel q) (baseCoset n)))),
      ∀ v w : EModel q,
        (smoothProjectorMetric_adaptedAtlas hLee hDesc hImm n d e q g a hq hn).inner
          (leftCosetAction n u (baseCoset n))
          (((selfModelTangentEquiv n d e q g a
            (leftCosetAction n u (baseCoset n))).toLinearEquiv.conjAlgEquiv ℝ)
            (((euclideanTangentEquiv n d e q g a
              (leftCosetAction n u (baseCoset n))).toLinearEquiv.conjAlgEquiv ℝ)
              (((translationTangentEquiv n d e q g a u (baseCoset n)).toLinearEquiv.conjAlgEquiv ℝ) S)) v)
          (((selfModelTangentEquiv n d e q g a
            (leftCosetAction n u (baseCoset n))).toLinearEquiv.conjAlgEquiv ℝ)
            (((euclideanTangentEquiv n d e q g a
              (leftCosetAction n u (baseCoset n))).toLinearEquiv.conjAlgEquiv ℝ)
              (((translationTangentEquiv n d e q g a u (baseCoset n)).toLinearEquiv.conjAlgEquiv ℝ) S)) w) =
        (smoothProjectorMetric_adaptedAtlas hLee hDesc hImm n d e q g a hq hn).inner
          (leftCosetAction n u (baseCoset n)) v w := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := euclideanModel_isManifold n d e q g a
  letI := euclideanQuotientCharts n d e q g a
  letI := euclideanQuotientCharts_isManifold n d e q g a
  let x := leftCosetAction n u (baseCoset n)
  intro S hS v w
  have hOld := selfModel_translated_generators_metric_compatible
    hDesc hImm n d e q g a hq u S hS v w
  let A : Module.End ℝ (EModel q) :=
    ((selfModelTangentEquiv n d e q g a x).toLinearEquiv.conjAlgEquiv ℝ)
      (((euclideanTangentEquiv n d e q g a x).toLinearEquiv.conjAlgEquiv ℝ)
        (((translationTangentEquiv n d e q g a u (baseCoset n)).toLinearEquiv.conjAlgEquiv ℝ) S))
  have hLeft := smoothProjectorMetric_adapted_eq_self
    hLee hDesc hImm n d e q g a hq hn x (A v) (A w)
  have hRight := smoothProjectorMetric_adapted_eq_self
    hLee hDesc hImm n d e q g a hq hn x v w
  exact hLeft.trans (hOld.trans hRight.symm)

end
end QuaternionicSymmetry.CompactSymplecticProjectorAdaptedAtlasQuaternionicMetric
