import QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorSurjective
import QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorPoint

/-! Set-level equivalence of the concrete imaginary-unit sphere with the
entire actual LC twistor fiber over the base projector, established from
the genuine rank-three plane and its square-minus-one equation. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorEquiv

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorStrongBaseTwistorPoint
open CompactSymplecticProjectorStrongBaseTwistorInjective
open CompactSymplecticProjectorStrongBaseTwistorSurjective
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
set_option maxHeartbeats 1000000

def strongBaseTwistorFiber
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
    Type := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  exact {p : TwistorSphere Q // projection Q p = baseCoset n}

def toStrongBaseTwistorFiber
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
    strongBaseTwistorFiber hLee hDesc hImm n d e q g a hq hn := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  exact ⟨strongBaseTwistorPoint hLee hDesc hImm n d e q g a hq hn z,
    strongBaseTwistorPoint_base hLee hDesc hImm n d e q g a hq hn z⟩

theorem toStrongBaseTwistorFiber_bijective
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
    Function.Bijective (toStrongBaseTwistorFiber hLee hDesc hImm n d e q g a hq hn) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  constructor
  · intro z w hzw
    exact strongBaseTwistorPoint_injective hLee hDesc hImm n d e q g a hq hn
      (congrArg Subtype.val hzw)
  · intro p
    let i := Q.frames.adaptedCore.indexAt (baseCoset n)
    have hi : baseCoset n ∈ Q.frames.adaptedCore.baseSet i :=
      Q.frames.adaptedCore.mem_baseSet_at (baseCoset n)
    have hp : projection Q p.1 = baseCoset n := p.2
    have hip : projection Q p.1 ∈ Q.frames.adaptedCore.baseSet i := by
      rw [hp]
      exact hi
    let b := localCoordinate Q i p.1 hip
    obtain ⟨z, hz⟩ := strongBaseIntrinsicFiberPoint_surjective
      hLee hDesc hImm n d e q g a hq hn (preferredToIntrinsic Q (baseCoset n) b)
    refine ⟨z, Subtype.ext ?_⟩
    have hcoef : (preferredFiberEquiv Q (baseCoset n)).symm
        (strongBaseIntrinsicFiberPoint hLee hDesc hImm n d e q g a hq hn z) = b := by
      rw [hz]
      exact (preferredFiberEquiv Q (baseCoset n)).symm_apply_apply b
    change preferredPoint Q (baseCoset n)
      ((preferredFiberEquiv Q (baseCoset n)).symm
        (strongBaseIntrinsicFiberPoint hLee hDesc hImm n d e q g a hq hn z)) = p.1
    rw [hcoef]
    simpa [preferredPoint, hp] using pointOfLocal_localCoordinate Q i p.1 hip

def strongBaseTwistorFiberEquiv
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
    coefficientSphere ≃ strongBaseTwistorFiber hLee hDesc hImm n d e q g a hq hn := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  exact Equiv.ofBijective
    (toStrongBaseTwistorFiber hLee hDesc hImm n d e q g a hq hn)
    (toStrongBaseTwistorFiber_bijective hLee hDesc hImm n d e q g a hq hn)

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorEquiv
