import QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorFiber
import QuaternionicSymmetry.ManifoldQuaternionicIntrinsicTwistorComparison

/-! The intrinsic base-fiber complex structure yields a point of the
existing smooth quaternionic twistor sphere, with the exact intrinsic
operator recovered under the proved fiber comparison. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorPoint

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorStrongBaseTwistorFiber
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldQuaternionicIntrinsicTwistorComparison
open ManifoldTwistorSphereBundle
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff

noncomputable section

def strongBaseTwistorPoint
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) [NeZero q] (z : coefficientSphere) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    TwistorSphere (strongQuaternionicHermitianTangent
      hLee hDesc hImm n d e q g a hq hn) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  exact preferredPoint Q (baseCoset n)
    ((preferredFiberEquiv Q (baseCoset n)).symm
      (strongBaseIntrinsicFiberPoint hLee hDesc hImm n d e q g a hq hn z))

theorem strongBaseTwistorPoint_base
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) [NeZero q] (z : coefficientSphere) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    projection (strongQuaternionicHermitianTangent
      hLee hDesc hImm n d e q g a hq hn)
      (strongBaseTwistorPoint hLee hDesc hImm n d e q g a hq hn z) =
      baseCoset n := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  change projection Q (preferredPoint Q (baseCoset n)
    ((preferredFiberEquiv Q (baseCoset n)).symm
      (strongBaseIntrinsicFiberPoint hLee hDesc hImm n d e q g a hq hn z))) = _
  exact projection_pointOfLocal Q (Q.frames.adaptedCore.indexAt (baseCoset n))
    (baseCoset n) (Q.frames.adaptedCore.mem_baseSet_at (baseCoset n)) _

theorem strongBaseTwistorPoint_intrinsic
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) [NeZero q] (z : coefficientSphere) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    toIntrinsicFiber (strongQuaternionicHermitianTangent
      hLee hDesc hImm n d e q g a hq hn)
      (strongBaseTwistorPoint hLee hDesc hImm n d e q g a hq hn z) =
      strongBaseIntrinsicFiberPoint hLee hDesc hImm n d e q g a hq hn z := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  change preferredToIntrinsic Q (baseCoset n)
    ((preferredFiberEquiv Q (baseCoset n)).symm
      (strongBaseIntrinsicFiberPoint hLee hDesc hImm n d e q g a hq hn z)) = _
  exact (preferredFiberEquiv Q (baseCoset n)).apply_symm_apply _

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorPoint
