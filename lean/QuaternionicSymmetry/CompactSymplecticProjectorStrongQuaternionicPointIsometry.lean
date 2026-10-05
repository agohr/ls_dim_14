import QuaternionicSymmetry.CompactSymplecticProjectorStrongTangentPlaneIdentification
import QuaternionicSymmetry.CompactSymplecticProjectorStrongPointSymmetryPreferredPlane
import QuaternionicSymmetry.CompactSymplecticProjectorStrongPointSymmetryMetric
import QuaternionicSymmetry.ManifoldQuaternionicSpanSymmetry

/-! An actual projector point symmetry is an isometry of the constructed
smooth quaternionic-Hermitian tangent reduction. No connection or
quaternionic parallelism is assumed. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongQuaternionicPointIsometry

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongPointSymmetry
open CompactSymplecticProjectorStrongPointSymmetryPreferredPlane
open CompactSymplecticProjectorStrongPointSymmetryMetric
open CompactSymplecticProjectorStrongTangentPlaneIdentification
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorPointSymmetry
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldQuaternionicSpanSymmetry
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem pointSymmetry_preserves_tangentSpan
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    PreservesSpan
      (strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn)
      (strongPointSymmetryDiffeomorph hLee hDesc hImm n d e q g a hq hn x) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  let T := strongPointSymmetryDiffeomorph hLee hDesc hImm n d e q g a hq hn x
  have hT : T.symm = T := by
    apply Diffeomorph.ext
    intro y
    apply T.injective
    change T (T.symm y) = T (T y)
    rw [T.apply_symm_apply]
    simp only [T, strongPointSymmetry_apply]
    exact (pointSymmetry_involutive n x y).symm
  have hfwd : PreservesSpanForward Q T := by
    intro y A hA
    let D := T.mfderivToContinuousLinearEquiv (by simp) y
    refine ⟨D.conjContinuousAlgEquiv A, ?_, ?_⟩
    · rw [tangentSpan_eq_preferredPlane hLee hDesc hImm n d e q g a hq hn (T y)]
      have hP := pointSymmetry_preferredPlane_invariant
        hLee hDesc hImm n d e q g a hq hn x y
      have hP' :
          CompactSymplecticProjectorPreferredContinuousPlane.preferredContinuousImaginaryPlane
            hDesc hImm n d e q g a hq hn (T y) =
          Submodule.map D.conjContinuousAlgEquiv.toLinearMap
            (CompactSymplecticProjectorPreferredContinuousPlane.preferredContinuousImaginaryPlane
              hDesc hImm n d e q g a hq hn y) := by
        simpa only [T, strongPointSymmetry_apply] using hP
      rw [hP']
      apply Submodule.mem_map_of_mem
      simpa only [Q, tangentSpan_eq_preferredPlane hLee hDesc hImm n d e q g a hq hn y]
        using hA
    · intro v
      change D (A v) = (D.conjContinuousAlgEquiv A) (D v)
      simp
  constructor
  · exact hfwd
  · simpa only [hT] using hfwd

theorem pointSymmetry_is_quaternionic_isometry
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    IsQuaternionicIsometry
      (strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn)
      (strongPointSymmetryDiffeomorph hLee hDesc hImm n d e q g a hq hn x) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  constructor
  · intro y v w
    rw [strongQuaternionicHermitianTangent_metric_eq_projector
      hLee hDesc hImm n d e q g a hq hn
      (strongPointSymmetryDiffeomorph hLee hDesc hImm n d e q g a hq hn x y),
      strongQuaternionicHermitianTangent_metric_eq_projector
        hLee hDesc hImm n d e q g a hq hn y]
    simpa only [strongPointSymmetry_apply] using
      pointSymmetry_metric_invariant_strong
        hLee hDesc hImm n d e q g a hq hn x y v w
  · exact pointSymmetry_preserves_tangentSpan
      hLee hDesc hImm n d e q g a hq hn x

def pointSymmetryQuaternionicIsometry
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) :
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
  exact ⟨strongPointSymmetryDiffeomorph hLee hDesc hImm n d e q g a hq hn x,
    pointSymmetry_is_quaternionic_isometry hLee hDesc hImm n d e q g a hq hn x⟩

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongQuaternionicPointIsometry
