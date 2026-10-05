import QuaternionicSymmetry.CompactSymplecticProjectorStrongQuaternionicHermitianTangent
import QuaternionicSymmetry.CompactSymplecticProjectorStrongIndexedContinuousPlane
import QuaternionicSymmetry.CompactSymplecticProjectorStrongFrameQuaternionicSpan

/-! The chart-coordinate plane of the constructed smooth quaternionic
Hermitian tangent reduction is the independently defined projector Q-plane,
not merely an abstract isomorphic rank-three bundle. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongQuaternionicPlaneIdentification

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeChartCenter
open CompactSymplecticProjectorStrongFrameQuaternionicSpan
open CompactSymplecticProjectorStrongIndexedContinuousPlane
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorBaseStandardQuaternionicStructure
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldQuaternionicReduction
open VectorBundleFrameTransitions
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section
set_option maxRecDepth 4000

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem strongQuaternionicPlane_eq_projectorPlane
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
      (strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn).toSmoothAlmostQuaternionicTangent.chartSpan i y =
      indexedLocalPlane hLee hDesc hImm n d e q g a hq hn i y := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  letI : IsManifold 𝓘(ℝ, EModel q) 1 (ProjectiveCarrier n) :=
    (strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn).of_le
      (by norm_cast)
  intro i y hy
  let x := strongChartCenter hLee hDesc hImm n d e q g a hq hn i
  have hW : y ∈ strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x :=
    mem_strongGaugeNeighborhood_of_chart_source
      hLee hDesc hImm n d e q g a hq hn i y hy
  rw [SmoothAlmostQuaternionicTangent.chartSpan_eq_map]
  change Submodule.map
      (localFrameConjugation hLee hDesc hImm n d e q g a hq hn x y)
      (quaternionicSpan (standardRealQuaternionicStructure n q hq)) = _
  exact localFrameConjugation_quaternionicSpan
    hLee hDesc hImm n d e q g a hq hn x y hW

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongQuaternionicPlaneIdentification
