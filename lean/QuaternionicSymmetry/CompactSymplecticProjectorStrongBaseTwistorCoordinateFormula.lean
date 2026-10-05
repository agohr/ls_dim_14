import QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorCoordinateLinear

/-! The restriction of the actual linear tangent-operator coordinate map to
the coefficient sphere is exactly the preferred twistor-fiber coordinate. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorCoordinateFormula

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorStrongBaseTwistorOperator
open CompactSymplecticProjectorStrongBaseOperatorContinuous
open CompactSymplecticProjectorStrongBaseTwistorFiber
open CompactSymplecticProjectorStrongBaseTwistorPoint
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongBaseTwistorPreferredCoordinate
open CompactSymplecticProjectorStrongBaseTwistorCoordinateLinear
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldQuaternionicIntrinsicTwistorComparison
open ManifoldQuaternionicDerivativeAction
open ManifoldQuaternionicIntrinsicFiberHomeomorph
open ManifoldTwistorSphereBundle
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff

noncomputable section
set_option maxHeartbeats 1000000

theorem preferredBaseCoefficientLinear_apply
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
    preferredBaseCoefficientLinear hLee hDesc hImm n d e q g a hq hn z.1 =
      ((preferredFiberEquiv Q (baseCoset n)).symm
        (strongBaseIntrinsicFiberPoint hLee hDesc hImm n d e q g a hq hn z)).1 := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  let L := tangentSynthLinearEquiv Q (baseCoset n)
  let b := (preferredFiberEquiv Q (baseCoset n)).symm
    (strongBaseIntrinsicFiberPoint hLee hDesc hImm n d e q g a hq hn z)
  apply L.injective
  change L (L.symm ⟨strongBaseOperatorLinear hLee hDesc hImm
    n d e q g a hq hn z.1,
    strongBaseOperatorLinear_mem_plane hLee hDesc hImm
      n d e q g a hq hn z.1⟩) = L b.1
  rw [L.apply_symm_apply]
  apply Subtype.ext
  have h := congrArg (fun A : IntrinsicTwistorFiber Q (baseCoset n) => A.1.1)
    ((preferredFiberEquiv Q (baseCoset n)).apply_symm_apply
      (strongBaseIntrinsicFiberPoint hLee hDesc hImm n d e q g a hq hn z))
  have h' : tangentSynth Q (baseCoset n) b.1 =
      strongBaseUnitOperator hLee hDesc hImm n d e q g a hq hn z := by
    simpa only [preferredFiberEquiv, Equiv.ofBijective_apply,
      preferredToIntrinsic_operator, strongBaseIntrinsicFiberPoint_operator] using h
  change strongBaseOperatorLinear hLee hDesc hImm n d e q g a hq hn z.1 =
    tangentSynth Q (baseCoset n) b.1
  rw [strongBaseOperatorLinear_apply]
  exact h'.symm

theorem strongBaseTwistorPoint_preferredCoordinate_linear
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
    (localCoordinate Q (Q.frames.adaptedCore.indexAt (baseCoset n))
      (strongBaseTwistorPoint hLee hDesc hImm n d e q g a hq hn z)
      (by rw [CompactSymplecticProjectorStrongBaseTwistorPoint.strongBaseTwistorPoint_base];
          exact Q.frames.adaptedCore.mem_baseSet_at _)).1 =
      preferredBaseCoefficientLinear hLee hDesc hImm n d e q g a hq hn z.1 := by
  have hcoord := congrArg Subtype.val
    (strongBaseTwistorPoint_preferredCoordinate hLee hDesc hImm
      n d e q g a hq hn z)
  exact hcoord.trans
    (preferredBaseCoefficientLinear_apply hLee hDesc hImm
      n d e q g a hq hn z).symm

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorCoordinateFormula
