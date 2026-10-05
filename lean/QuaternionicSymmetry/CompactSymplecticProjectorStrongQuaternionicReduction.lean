import QuaternionicSymmetry.CompactSymplecticProjectorStrongContinuousPlaneOverlap
import QuaternionicSymmetry.CompactSymplecticProjectorStrongFrameQuaternionicSpan
import QuaternionicSymmetry.CompactSymplecticProjectorStrongTangentFrameGauge
import QuaternionicSymmetry.ManifoldTangentFramePlaneReduction

/-! The actual smooth action-derived tangent gauge gives an honest
quaternionic reduction of the strong quotient atlas. Its overlap law is
derived from the projector Q-plane, not imposed as model geometry. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongQuaternionicReduction

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeChartCenter
open CompactSymplecticProjectorStrongTangentFrameGauge
open CompactSymplecticProjectorStrongFrameQuaternionicSpan
open CompactSymplecticProjectorStrongIndexedContinuousPlane
open CompactSymplecticProjectorStrongContinuousPlaneOverlap
open CompactSymplecticProjectorBaseStandardQuaternionicStructure
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldQuaternionicReduction
open ManifoldTangentFramePlaneReduction
open VectorBundleFrameTransitions
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

def strongQuaternionicReduction
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) :
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    QuaternionicFrameReduction
      (strongTangentFrameGauge hLee hDesc hImm n d e q g a hq hn).adaptedCore := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  letI : IsManifold 𝓘(ℝ, EModel q) 1 (ProjectiveCarrier n) :=
    (strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn).of_le
      (by norm_cast)
  let F := strongTangentFrameGauge hLee hDesc hImm n d e q g a hq hn
  let Q := standardRealQuaternionicStructure n q hq
  apply reduction_of_chartPlane_overlap F Q
  intro i j y hi hj
  have hLocal (k : atlas (EModel q) (ProjectiveCarrier n))
      (hk : y ∈ F.adaptedCore.baseSet k) :
      localPlane F Q k y =
        indexedLocalPlane hLee hDesc hImm n d e q g a hq hn k y := by
    let x := strongChartCenter hLee hDesc hImm n d e q g a hq hn k
    have hW : y ∈ strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x :=
      mem_strongGaugeNeighborhood_of_chart_source
        hLee hDesc hImm n d e q g a hq hn k y hk
    change Submodule.map
      (localFrameConjugation hLee hDesc hImm n d e q g a hq hn x y)
      (quaternionicSpan (standardRealQuaternionicStructure n q hq)) = _
    exact localFrameConjugation_quaternionicSpan
      hLee hDesc hImm n d e q g a hq hn x y hW
  rw [hLocal i hi, hLocal j hj]
  exact indexedLocalPlane_transport hLee hDesc hImm n d e q g a hq hn i j y hi hj

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongQuaternionicReduction
