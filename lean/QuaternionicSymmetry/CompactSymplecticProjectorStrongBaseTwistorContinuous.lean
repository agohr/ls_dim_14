import QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseOperatorContinuous
import QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorPoint
import QuaternionicSymmetry.ManifoldQuaternionicIntrinsicFiberHomeomorph
import QuaternionicSymmetry.ManifoldTwistorFixedFiberPointContinuous

/-! The actual base-fiber map from imaginary quaternionic units into the
Levi-Civita twistor sphere is continuous in the genuine bundle topology. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorContinuous

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorStrongBaseOperatorContinuous
open CompactSymplecticProjectorStrongBaseTwistorFiber
open CompactSymplecticProjectorStrongBaseTwistorPoint
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldQuaternionicIntrinsicFiberHomeomorph
open ManifoldTwistorFixedFiberPointContinuous
open ManifoldQuaternionicIntrinsicTwistorComparison
open ManifoldTwistorSphereBundle
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff

noncomputable section

theorem continuous_strongBaseIntrinsicFiberPoint
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
    Continuous (strongBaseIntrinsicFiberPoint hLee hDesc hImm n d e q g a hq hn) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  have h := continuous_strongBaseUnitOperator hLee hDesc hImm n d e q g a hq hn
  have hplane : Continuous (fun z : coefficientSphere =>
      (⟨CompactSymplecticProjectorStrongBaseTwistorOperator.strongBaseUnitOperator
        hLee hDesc hImm n d e q g a hq hn z,
        CompactSymplecticProjectorStrongBaseTwistorOperator.strongBaseUnitOperator_mem_plane
          hLee hDesc hImm n d e q g a hq hn z⟩ :
        ManifoldQuaternionicSpanSymmetry.tangentSpan Q (baseCoset n))) :=
    h.subtype_mk _
  exact hplane.subtype_mk _

theorem continuous_strongBaseTwistorPoint
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) [NeZero q] :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    Continuous (strongBaseTwistorPoint hLee hDesc hImm n d e q g a hq hn) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  exact (continuous_preferredPoint_fixed Q (baseCoset n)).comp
    ((continuous_preferredFiberEquiv_symm Q (baseCoset n)).comp
      (continuous_strongBaseIntrinsicFiberPoint hLee hDesc hImm n d e q g a hq hn))

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorContinuous
