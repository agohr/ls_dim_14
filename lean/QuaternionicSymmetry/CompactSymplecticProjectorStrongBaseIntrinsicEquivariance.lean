import QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorEquiv
import QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorEquivariance
import QuaternionicSymmetry.CompactSymplecticProjectorStrongTranslationHom
import QuaternionicSymmetry.ManifoldQuaternionicDerivativeAction

/-! The actual isotropy differential rotates the intrinsic LC twistor
fiber by exactly the checked first-block quaternionic sphere action. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseIntrinsicEquivariance

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorIsotropyBlocks
open CompactSymplecticProjectorStabilizerHopfAction
open CompactSymplecticProjectorStrongBaseTwistorFiber
open CompactSymplecticProjectorStrongBaseTwistorEquivariance
open CompactSymplecticProjectorStrongTranslationHom
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorBaseStandardQuaternionicStructure
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldQuaternionicDerivativeAction
open ManifoldTwistorSphereBundle
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff

noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 4000

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem strongBaseIntrinsicFiberPoint_stabilizer
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) [NeZero q]
    (k : firstPairStabilizer n) (z : coefficientSphere) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    letI := sphereFiberAction n (standardRealQuaternionicStructure n q hq)
    let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
    let f := (translationQuaternionicIsometryHom hLee hDesc hImm n d e q g a hq hn) k.1
    let hfix : f • baseCoset n = baseCoset n :=
      stabilizer_fixes_baseCoset n k.1 k.2
    hfix ▸ intrinsicTwistorFiberAction Q f (baseCoset n)
      (strongBaseIntrinsicFiberPoint hLee hDesc hImm n d e q g a hq hn z) =
      strongBaseIntrinsicFiberPoint hLee hDesc hImm n d e q g a hq hn (k • z) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  letI := sphereFiberAction n (standardRealQuaternionicStructure n q hq)
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  let f := (translationQuaternionicIsometryHom hLee hDesc hImm n d e q g a hq hn) k.1
  have hfix : f • baseCoset n = baseCoset n :=
    stabilizer_fixes_baseCoset n k.1 k.2
  have hCast {x y : ProjectiveCarrier n} (h : x = y)
      (B : IntrinsicTwistorFiber Q x) : (h ▸ B).1.1 = B.1.1 := by
    cases h
    rfl
  apply Subtype.ext
  apply Subtype.ext
  ext v
  obtain ⟨w, rfl⟩ := (tangentEquiv Q f (baseCoset n)).surjective v
  rw [hCast hfix]
  change tangentConjugation Q f (baseCoset n)
      (strongBaseIntrinsicFiberPoint hLee hDesc hImm n d e q g a hq hn z).1.1
        (tangentEquiv Q f (baseCoset n) w) =
    (strongBaseIntrinsicFiberPoint hLee hDesc hImm n d e q g a hq hn (k • z)).1.1
      (tangentEquiv Q f (baseCoset n) w)
  rw [tangentConjugation_apply_tangentEquiv]
  exact strongBaseUnitOperator_stabilizer_intertwining
    hLee hDesc hImm n d e q g a hq hn k z w

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseIntrinsicEquivariance
