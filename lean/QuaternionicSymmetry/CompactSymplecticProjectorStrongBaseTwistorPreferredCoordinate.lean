import QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorPoint

/-! The preferred adapted sphere coordinate of the *actual* base twistor
point is the coordinate of its concrete tangent operator. This identifies
the rotation that must be controlled in the smooth/complex fiber comparison;
it does not assert that the rotation is trivial. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorPreferredCoordinate

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorStrongBaseTwistorPoint
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

theorem strongBaseTwistorPoint_preferredCoordinate
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
    let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
    localCoordinate Q (Q.frames.adaptedCore.indexAt (baseCoset n))
      (strongBaseTwistorPoint hLee hDesc hImm n d e q g a hq hn z)
      (by rw [strongBaseTwistorPoint_base]; exact Q.frames.adaptedCore.mem_baseSet_at _) =
      (preferredFiberEquiv Q (baseCoset n)).symm
        (strongBaseIntrinsicFiberPoint hLee hDesc hImm n d e q g a hq hn z) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  change localCoordinate Q (Q.frames.adaptedCore.indexAt (baseCoset n))
      (preferredPoint Q (baseCoset n)
        ((preferredFiberEquiv Q (baseCoset n)).symm
          (strongBaseIntrinsicFiberPoint hLee hDesc hImm n d e q g a hq hn z)))
      _ = _
  exact localCoordinate_pointOfLocal Q (Q.frames.adaptedCore.indexAt (baseCoset n))
    (baseCoset n) (Q.frames.adaptedCore.mem_baseSet_at _) _

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorPreferredCoordinate
