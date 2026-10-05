import QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorFiber
import QuaternionicSymmetry.CompactSymplecticProjectorStrongTranslationDerivativeSquare
import QuaternionicSymmetry.CompactSymplecticProjectorStabilizerExactSphereTangent

/-! Exact isotropy equivariance of the actual intrinsic base-twistor
operator, obtained by transporting the checked old-tangent quaternionic
matrix identity through the genuine old-to-strong derivative square. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorEquivariance

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseQuaternionAction
open CompactSymplecticProjectorStabilizerTangentFactor
open CompactSymplecticProjectorStabilizerExactSphereTangent
open CompactSymplecticProjectorStabilizerHopfAction
open CompactSymplecticProjectorStrongBaseTwistorOperator
open CompactSymplecticProjectorStrongTranslationDerivativeSquare
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorBaseStandardQuaternionicStructure
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open QuaternionicUnitScalarIsometries
open ManifoldTwistorSphereBundle
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem strongBaseUnitOperator_stabilizer_intertwining
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) [NeZero q]
    (k : firstPairStabilizer n) (z : coefficientSphere) :
    letI := a.quotientCharts
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := sphereFiberAction n (standardRealQuaternionicStructure n q hq)
    ∀ v : TangentSpace 𝓘(ℝ, EModel q) (baseCoset n),
      mfderiv 𝓘(ℝ, EModel q) 𝓘(ℝ, EModel q)
        (leftCosetAction n k.1) (baseCoset n)
        (strongBaseUnitOperator hLee hDesc hImm n d e q g a hq hn z v) =
      strongBaseUnitOperator hLee hDesc hImm n d e q g a hq hn (k • z)
        (mfderiv 𝓘(ℝ, EModel q) 𝓘(ℝ, EModel q)
          (leftCosetAction n k.1) (baseCoset n) v) := by
  letI := a.quotientCharts
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := sphereFiberAction n (standardRealQuaternionicStructure n q hq)
  intro v
  let U := (euclideanModelEquiv q).toLinearEquiv
  let A := baseQuaternionAction hDesc hImm n d e q g a hq (pureScalar z.1)
  let B := baseQuaternionAction hDesc hImm n d e q g a hq (pureScalar (k • z).1)
  let D := stabilizerTangentEnd n d e q g a k
  have hOld := stabilizerTangentEnd_sphere_intertwining
    hDesc hImm n d e q g a hq (standardRealQuaternionicStructure n q hq) k z
  have hOldv := congrArg (fun T : Module.End ℝ _ => T (U.symm v)) hOld
  change D (A (U.symm v)) = B (D (U.symm v)) at hOldv
  have hSq (w) :
      U (D w) = mfderiv 𝓘(ℝ, EModel q) 𝓘(ℝ, EModel q)
        (leftCosetAction n k.1) (baseCoset n) (U w) := by
    simpa only [stabilizerTangentEnd] using
      translation_derivative_coordinate_square hLee hDesc hImm
        n d e q g a hq hn k.1 (baseCoset n) w
  have hDv : U.symm (mfderiv 𝓘(ℝ, EModel q) 𝓘(ℝ, EModel q)
      (leftCosetAction n k.1) (baseCoset n) v) = D (U.symm v) := by
    apply U.injective
    rw [U.apply_symm_apply, hSq, U.apply_symm_apply]
  change mfderiv 𝓘(ℝ, EModel q) 𝓘(ℝ, EModel q)
      (leftCosetAction n k.1) (baseCoset n) (U (A (U.symm v))) =
    U (B (U.symm (mfderiv 𝓘(ℝ, EModel q) 𝓘(ℝ, EModel q)
      (leftCosetAction n k.1) (baseCoset n) v)))
  rw [← hSq, hDv, hOldv]

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorEquivariance
