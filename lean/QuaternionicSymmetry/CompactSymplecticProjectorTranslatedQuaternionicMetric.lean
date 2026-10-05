import QuaternionicSymmetry.CompactSymplecticProjectorHomogeneousQuaternionicPlane
import QuaternionicSymmetry.CompactSymplecticProjectorBaseQuaternionicMetric

/-! Actual metric compatibility of representative-transported
quaternionic tangent operators at every quotient point. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorTranslatedQuaternionicMetric

open Manifold Bundle
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseQuaternionic
open CompactSymplecticProjectorBaseQuaternionicMetric
open CompactSymplecticProjectorRiemannianMetric
open CompactSymplecticProjectorTranslationTangentEquiv
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section
set_option maxHeartbeats 5000000

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

/-- Conjugating a base orthogonal tangent endomorphism by an actual
quotient translation differential preserves orthogonality for the
constructed smooth Riemannian metric. -/
theorem translation_conj_metric_compatible
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (u : G n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    ∀ (S : Module.End ℝ (TangentSpace 𝓘(ℝ, RModel q) (baseCoset n))),
    (∀ v w : TangentSpace 𝓘(ℝ, RModel q) (baseCoset n),
      (smoothProjectorMetric hDesc hImm n d e q g a).inner (baseCoset n)
        (S v) (S w) =
      (smoothProjectorMetric hDesc hImm n d e q g a).inner (baseCoset n) v w) →
    ∀ v w : TangentSpace 𝓘(ℝ, RModel q) (leftCosetAction n u (baseCoset n)),
      (smoothProjectorMetric hDesc hImm n d e q g a).inner
        (leftCosetAction n u (baseCoset n))
        (((translationTangentEquiv n d e q g a u (baseCoset n)).toLinearEquiv.conjAlgEquiv ℝ) S v)
        (((translationTangentEquiv n d e q g a u (baseCoset n)).toLinearEquiv.conjAlgEquiv ℝ) S w) =
      (smoothProjectorMetric hDesc hImm n d e q g a).inner
        (leftCosetAction n u (baseCoset n)) v w := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  let T := (translationTangentEquiv n d e q g a u (baseCoset n)).toLinearEquiv
  intro S hS v w
  have hA := smoothProjectorMetric_invariant hDesc hImm n d e q g a u (baseCoset n)
  have h1 := hA (S (T.symm v)) (S (T.symm w))
  have h2 := hA (T.symm v) (T.symm w)
  have h3 := hS (T.symm v) (T.symm w)
  change (smoothProjectorMetric hDesc hImm n d e q g a).inner
    (leftCosetAction n u (baseCoset n))
    (T (S (T.symm v))) (T (S (T.symm w))) = _ at h1
  change (smoothProjectorMetric hDesc hImm n d e q g a).inner
    (leftCosetAction n u (baseCoset n))
    (T (T.symm v)) (T (T.symm w)) = _ at h2
  rw [T.apply_symm_apply, T.apply_symm_apply] at h2
  change (smoothProjectorMetric hDesc hImm n d e q g a).inner
      (leftCosetAction n u (baseCoset n))
      (T (S (T.symm v))) (T (S (T.symm w))) =
    (smoothProjectorMetric hDesc hImm n d e q g a).inner
      (leftCosetAction n u (baseCoset n)) v w
  exact h1.trans (h3.trans h2.symm)

/-- Every representative transports the three checked quaternionic
generators to metric-compatible operators at its quotient point. -/
theorem translated_quaternionic_generators_metric_compatible
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n) (u : G n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    ∀ S ∈ ({(baseI hDesc hImm n d e q g a hq).toLinearMap,
      (baseJ hDesc hImm n d e q g a hq).toLinearMap,
      (baseK hDesc hImm n d e q g a hq).toLinearMap} :
        Set (Module.End ℝ (TangentSpace 𝓘(ℝ, RModel q) (baseCoset n)))),
      ∀ v w : TangentSpace 𝓘(ℝ, RModel q) (leftCosetAction n u (baseCoset n)),
        (smoothProjectorMetric hDesc hImm n d e q g a).inner
          (leftCosetAction n u (baseCoset n))
          (((translationTangentEquiv n d e q g a u (baseCoset n)).toLinearEquiv.conjAlgEquiv ℝ) S v)
          (((translationTangentEquiv n d e q g a u (baseCoset n)).toLinearEquiv.conjAlgEquiv ℝ) S w) =
        (smoothProjectorMetric hDesc hImm n d e q g a).inner
          (leftCosetAction n u (baseCoset n)) v w := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  intro S hS
  rcases hS with hS | hS | hS
  · subst S
    exact translation_conj_metric_compatible hDesc hImm n d e q g a u _
      (baseI_metric_compatible hDesc hImm n d e q g a hq)
  · subst S
    exact translation_conj_metric_compatible hDesc hImm n d e q g a u _
      (baseJ_metric_compatible hDesc hImm n d e q g a hq)
  · subst S
    exact translation_conj_metric_compatible hDesc hImm n d e q g a u _
      (baseK_metric_compatible hDesc hImm n d e q g a hq)

end
end QuaternionicSymmetry.CompactSymplecticProjectorTranslatedQuaternionicMetric
