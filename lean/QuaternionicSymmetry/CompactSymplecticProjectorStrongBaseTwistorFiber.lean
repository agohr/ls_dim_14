import QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorOperator
import QuaternionicSymmetry.ManifoldQuaternionicIntrinsicTwistorComparison

/-! The checked quaternionic-line complex structures are actual points of
the strong quotient's intrinsic Levi-Civita twistor fiber at the base coset. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorFiber

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorStrongBaseTwistorOperator
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldQuaternionicDerivativeAction
open ManifoldQuaternionicIntrinsicTwistorComparison
open ManifoldTwistorSphereBundle
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff

noncomputable section
set_option maxHeartbeats 1000000

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

def strongBaseIntrinsicFiberPoint
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (z : coefficientSphere) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    IntrinsicTwistorFiber
      (strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn)
      (baseCoset n) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  exact ⟨⟨strongBaseUnitOperator hLee hDesc hImm n d e q g a hq hn z,
    strongBaseUnitOperator_mem_plane hLee hDesc hImm n d e q g a hq hn z⟩,
    strongBaseUnitOperator_square hLee hDesc hImm n d e q g a hq hn z⟩

theorem strongBaseIntrinsicFiberPoint_operator
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (z : coefficientSphere) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    (strongBaseIntrinsicFiberPoint hLee hDesc hImm n d e q g a hq hn z).1.1 =
      strongBaseUnitOperator hLee hDesc hImm n d e q g a hq hn z := rfl

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorFiber
