import QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorPoint
import QuaternionicSymmetry.CompactSymplecticProjectorBaseImaginaryRank

/-! Distinct quaternionic imaginary unit directions give distinct actual
Levi-Civita twistor points over the base projector. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorInjective

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseQuaternionAction
open CompactSymplecticProjectorBaseImaginaryRank
open CompactSymplecticProjectorStrongBaseTwistorOperator
open CompactSymplecticProjectorStrongBaseTwistorFiber
open CompactSymplecticProjectorStrongBaseTwistorPoint
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldQuaternionicIntrinsicTwistorComparison
open ManifoldTwistorSphereBundle
open QuaternionicUnitScalarIsometries
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem strongBaseUnitOperator_injective
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) :
    letI := a.quotientCharts
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    Function.Injective (strongBaseUnitOperator hLee hDesc hImm n d e q g a hq hn) := by
  letI := a.quotientCharts
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  intro z w hzw
  let U := (euclideanModelEquiv q).toLinearEquiv
  have hOld : baseQuaternionAction hDesc hImm n d e q g a hq (pureScalar z.1) =
      baseQuaternionAction hDesc hImm n d e q g a hq (pureScalar w.1) := by
    ext v
    have hv := congrArg
      (fun T : EuclideanSpace ℝ (Fin q) →L[ℝ] EuclideanSpace ℝ (Fin q) => T (U v)) hzw
    change U ((baseQuaternionAction hDesc hImm n d e q g a hq (pureScalar z.1)) v) =
      U ((baseQuaternionAction hDesc hImm n d e q g a hq (pureScalar w.1)) v) at hv
    exact U.injective hv
  have hQuat := (baseQuaternionAction_injective hDesc hImm n d e q g a hq hn) hOld
  apply Subtype.ext
  funext t
  fin_cases t
  · exact congrArg (fun r : ℍ => r.imI) hQuat
  · exact congrArg (fun r : ℍ => r.imJ) hQuat
  · exact congrArg (fun r : ℍ => r.imK) hQuat

theorem strongBaseTwistorPoint_injective
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
    Function.Injective (strongBaseTwistorPoint hLee hDesc hImm n d e q g a hq hn) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  classical
  intro z w hzw
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  let F := preferredFiberEquiv Q (baseCoset n)
  let i := Q.frames.adaptedCore.indexAt (baseCoset n)
  have hi : baseCoset n ∈ Q.frames.adaptedCore.baseSet i :=
    Q.frames.adaptedCore.mem_baseSet_at (baseCoset n)
  let Z := F.symm (strongBaseIntrinsicFiberPoint hLee hDesc hImm n d e q g a hq hn z)
  let W := F.symm (strongBaseIntrinsicFiberPoint hLee hDesc hImm n d e q g a hq hn w)
  have hPoints : pointOfLocal Q i (baseCoset n) hi Z =
      pointOfLocal Q i (baseCoset n) hi W := hzw
  let coord (p : TwistorSphere Q) : coefficientSphere :=
    if hp : projection Q p ∈ Q.frames.adaptedCore.baseSet i then
      localCoordinate Q i p hp else Z
  have hCoord := congrArg coord hPoints
  have hcoeff : F.symm (strongBaseIntrinsicFiberPoint hLee hDesc hImm n d e q g a hq hn z) =
      F.symm (strongBaseIntrinsicFiberPoint hLee hDesc hImm n d e q g a hq hn w) := by
    change Z = W
    simpa only [coord, projection_pointOfLocal, dif_pos hi,
      localCoordinate_pointOfLocal] using hCoord
  have hIntrinsic := F.symm.injective hcoeff
  exact strongBaseUnitOperator_injective hLee hDesc hImm n d e q g a hq hn
    (congrArg (fun A => A.1.1) hIntrinsic)

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorInjective
