import QuaternionicSymmetry.CompactSymplecticProjectorStrongTranslationPreferredPlane
import QuaternionicSymmetry.CompactSymplecticProjectorStrongTranslationMetric
import QuaternionicSymmetry.CompactSymplecticProjectorStrongTangentPlaneIdentification
import QuaternionicSymmetry.CompactSymplecticProjectorStrongQuaternionicHermitianTangent
import QuaternionicSymmetry.ManifoldQuaternionicSpanSymmetry

/-! Every genuine compact-symplectic left translation is an isometry of
the actual strong-atlas quaternionic-Hermitian tangent model. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongQuaternionicTranslation

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongTranslationDiffeomorph
open CompactSymplecticProjectorStrongTranslationPreferredPlane
open CompactSymplecticProjectorStrongTranslationMetric
open CompactSymplecticProjectorStrongTangentPlaneIdentification
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorTranslationDiffeomorph
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldQuaternionicSpanSymmetry
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

theorem strongTranslation_symm
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (u : G n) :
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    (strongLeftCosetDiffeomorph hLee hDesc hImm n d e q g a hq hn u).symm =
      strongLeftCosetDiffeomorph hLee hDesc hImm n d e q g a hq hn u⁻¹ := by
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  let T := strongLeftCosetDiffeomorph hLee hDesc hImm n d e q g a hq hn u
  let U := strongLeftCosetDiffeomorph hLee hDesc hImm n d e q g a hq hn u⁻¹
  apply Diffeomorph.ext
  intro y
  apply T.injective
  change T (T.symm y) = T (U y)
  rw [T.apply_symm_apply]
  change y = leftCosetAction n u (leftCosetAction n u⁻¹ y)
  rw [leftCosetAction_mul, mul_inv_cancel, leftCosetAction_one]

theorem translation_preserves_tangentSpan
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (u : G n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    PreservesSpan
      (strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn)
      (strongLeftCosetDiffeomorph hLee hDesc hImm n d e q g a hq hn u) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  let T := strongLeftCosetDiffeomorph hLee hDesc hImm n d e q g a hq hn u
  have hfwd (v : G n) : PreservesSpanForward Q
      (strongLeftCosetDiffeomorph hLee hDesc hImm n d e q g a hq hn v) := by
    intro y A hA
    let R := strongLeftCosetDiffeomorph hLee hDesc hImm n d e q g a hq hn v
    let D := R.mfderivToContinuousLinearEquiv (by simp) y
    refine ⟨D.conjContinuousAlgEquiv A, ?_, ?_⟩
    · rw [tangentSpan_eq_preferredPlane hLee hDesc hImm n d e q g a hq hn (R y)]
      have hP := translation_preferredPlane_invariant
        hLee hDesc hImm n d e q g a hq hn v y
      have hP' :
          CompactSymplecticProjectorPreferredContinuousPlane.preferredContinuousImaginaryPlane
            hDesc hImm n d e q g a hq hn (R y) =
          Submodule.map D.conjContinuousAlgEquiv.toLinearMap
            (CompactSymplecticProjectorPreferredContinuousPlane.preferredContinuousImaginaryPlane
              hDesc hImm n d e q g a hq hn y) := by
        simpa only [R, strongLeftCosetDiffeomorph_apply] using hP
      rw [hP']
      apply Submodule.mem_map_of_mem
      simpa only [Q, tangentSpan_eq_preferredPlane hLee hDesc hImm n d e q g a hq hn y]
        using hA
    · intro w
      change D (A w) = (D.conjContinuousAlgEquiv A) (D w)
      simp
  constructor
  · exact hfwd u
  · rw [strongTranslation_symm hLee hDesc hImm n d e q g a hq hn u]
    exact hfwd u⁻¹

theorem translation_is_quaternionic_isometry
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (u : G n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    IsQuaternionicIsometry
      (strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn)
      (strongLeftCosetDiffeomorph hLee hDesc hImm n d e q g a hq hn u) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  constructor
  · intro y v w
    rw [strongQuaternionicHermitianTangent_metric_eq_projector
      hLee hDesc hImm n d e q g a hq hn
      (strongLeftCosetDiffeomorph hLee hDesc hImm n d e q g a hq hn u y),
      strongQuaternionicHermitianTangent_metric_eq_projector
        hLee hDesc hImm n d e q g a hq hn y]
    simpa only [strongLeftCosetDiffeomorph_apply] using
      translation_metric_invariant_strong
        hLee hDesc hImm n d e q g a hq hn u y v w
  · exact translation_preserves_tangentSpan hLee hDesc hImm n d e q g a hq hn u

def translationQuaternionicIsometry
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (u : G n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    QuaternionicIsometries
      (strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  exact ⟨strongLeftCosetDiffeomorph hLee hDesc hImm n d e q g a hq hn u,
    translation_is_quaternionic_isometry hLee hDesc hImm n d e q g a hq hn u⟩

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongQuaternionicTranslation
