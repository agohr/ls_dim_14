import QuaternionicSymmetry.CompactSymplecticProjectorStrongPreferredContinuousPlaneCoordinate
import QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeChartIndex
import QuaternionicSymmetry.CompactSymplecticProjectorStrongTangentFrameGauge

/-! The genuine projector Q-plane has the same preferred-fiber transport
formula at every index of the strong Euclidean quotient atlas. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongIndexedContinuousPlane

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeChartCenter
open CompactSymplecticProjectorStrongGaugeChartIndex
open CompactSymplecticProjectorStrongTangentFrameGauge
open CompactSymplecticProjectorStrongFrameQuaternionicSpan
open CompactSymplecticProjectorStrongPreferredContinuousPlaneCoordinate
open CompactSymplecticProjectorPreferredContinuousPlane
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open VectorBundleFrameTransitions
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

def indexedLocalPlane
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) :
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    atlas (EModel q) (ProjectiveCarrier n) → ProjectiveCarrier n →
      Submodule ℝ (EModel q →L[ℝ] EModel q) := by
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  exact fun i y => Submodule.span ℝ (Set.range
    (localQuaternionicGenerator hLee hDesc hImm n d e q g a hq hn
      (strongChartCenter hLee hDesc hImm n d e q g a hq hn i) y))

theorem indexedLocalPlane_eq_core_transport
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    ∀ i y, y ∈ (tangentBundleCore 𝓘(ℝ, EModel q) (ProjectiveCarrier n)).baseSet i →
      indexedLocalPlane hLee hDesc hImm n d e q g a hq hn i y =
        Submodule.map
          ((transitionAtlas (tangentBundleCore 𝓘(ℝ, EModel q)
            (ProjectiveCarrier n))).adjointCoordChange
              ((tangentBundleCore 𝓘(ℝ, EModel q) (ProjectiveCarrier n)).indexAt y) i y).toLinearMap
          (preferredContinuousImaginaryPlane hDesc hImm n d e q g a hq hn y) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  letI : IsManifold 𝓘(ℝ, EModel q) 1 (ProjectiveCarrier n) :=
    (strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn).of_le
      (by norm_cast)
  intro i y hy
  let x := strongChartCenter hLee hDesc hImm n d e q g a hq hn i
  have hi : i = achart (EModel q) x := by
    apply Subtype.ext
    exact strongIndex_eq_preferredChart hLee hDesc hImm n d e q g a hq hn i
  have hW : y ∈ strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x :=
    mem_strongGaugeNeighborhood_of_chart_source
      hLee hDesc hImm n d e q g a hq hn i y hy
  change Submodule.span ℝ (Set.range
      (localQuaternionicGenerator hLee hDesc hImm n d e q g a hq hn x y)) = _
  rw [hi]
  exact localContinuousPlane_eq_core_transport
    hLee hDesc hImm n d e q g a hq hn x y hW

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongIndexedContinuousPlane
