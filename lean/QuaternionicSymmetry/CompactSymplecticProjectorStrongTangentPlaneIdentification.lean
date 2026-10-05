import QuaternionicSymmetry.CompactSymplecticProjectorStrongQuaternionicPlaneIdentification
import QuaternionicSymmetry.ManifoldQuaternionicSpanSymmetry

/-! The actual tangent-fiber quaternionic span of the strong reduction is
the independently constructed preferred projector plane, pointwise. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongTangentPlaneIdentification

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongIndexedContinuousPlane
open CompactSymplecticProjectorStrongQuaternionicPlaneIdentification
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorPreferredContinuousPlane
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldQuaternionicSpanSymmetry
open VectorBundleFrameTransitions
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem tangentSpan_eq_preferredPlane
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (y : ProjectiveCarrier n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    tangentSpan (strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn) y =
      preferredContinuousImaginaryPlane hDesc hImm n d e q g a hq hn y := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  letI : IsManifold 𝓘(ℝ, EModel q) 1 (ProjectiveCarrier n) :=
    (strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn).of_le
      (by norm_cast)
  let Z := tangentBundleCore 𝓘(ℝ, EModel q) (ProjectiveCarrier n)
  let i := Z.indexAt y
  have hi : y ∈ Z.baseSet i := Z.mem_baseSet_at y
  have hchart := strongQuaternionicPlane_eq_projectorPlane
    hLee hDesc hImm n d e q g a hq hn i y hi
  have hpref := indexedLocalPlane_eq_core_transport
    hLee hDesc hImm n d e q g a hq hn i y hi
  have hId : (transitionAtlas Z).adjointCoordChange i i y =
      ContinuousLinearMap.id ℝ (EModel q →L[ℝ] EModel q) := by
    apply ContinuousLinearMap.ext
    intro A
    exact (transitionAtlas Z).adjointCoordChange_self i y hi A
  rw [hId] at hpref
  simp at hpref
  change (strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn).toSmoothAlmostQuaternionicTangent.chartSpan i y = _
  exact hchart.trans hpref

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongTangentPlaneIdentification
