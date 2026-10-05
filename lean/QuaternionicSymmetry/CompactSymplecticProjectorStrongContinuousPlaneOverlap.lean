import QuaternionicSymmetry.CompactSymplecticProjectorStrongIndexedContinuousPlane
import QuaternionicSymmetry.ManifoldCorePlaneTransport

/-! The rank-three continuous endomorphism planes built from the actual
projector gauges obey the genuine strong tangent-core overlap cocycle. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongContinuousPlaneOverlap

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongIndexedContinuousPlane
open CompactSymplecticProjectorPreferredContinuousPlane
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open VectorBundleFrameTransitions
open ManifoldCorePlaneTransport
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem indexedLocalPlane_transport
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
    ∀ i j y, y ∈ (tangentBundleCore 𝓘(ℝ, EModel q) (ProjectiveCarrier n)).baseSet i →
      y ∈ (tangentBundleCore 𝓘(ℝ, EModel q) (ProjectiveCarrier n)).baseSet j →
      Submodule.map
        ((transitionAtlas (tangentBundleCore 𝓘(ℝ, EModel q)
          (ProjectiveCarrier n))).adjointCoordChange i j y).toLinearMap
        (indexedLocalPlane hLee hDesc hImm n d e q g a hq hn i y) =
      indexedLocalPlane hLee hDesc hImm n d e q g a hq hn j y := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  letI : IsManifold 𝓘(ℝ, EModel q) 1 (ProjectiveCarrier n) :=
    (strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn).of_le
      (by norm_cast)
  intro i j y hi hj
  exact localPlane_transport
    (tangentBundleCore 𝓘(ℝ, EModel q) (ProjectiveCarrier n))
    (preferredContinuousImaginaryPlane hDesc hImm n d e q g a hq hn)
    (indexedLocalPlane hLee hDesc hImm n d e q g a hq hn)
    (indexedLocalPlane_eq_core_transport hLee hDesc hImm n d e q g a hq hn)
    i j y hi hj

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongContinuousPlaneOverlap
