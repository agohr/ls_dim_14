import QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorSphereSmooth
import QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorCoordinateFormula
import QuaternionicSymmetry.ManifoldTwistorSphereFiberInclusion
import QuaternionicSymmetry.ManifoldTwistorSphereHomeomorph

/-! On the actual base twistor fiber, the literal intrinsic-complex-structure
map into the smooth sphere-bundle total space is the checked smooth sphere
rotation followed by the genuine smooth fiber inclusion. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAmbientActualTwistorSmoothBaseFiber

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorStrongBaseTwistorPoint
open CompactSymplecticProjectorStrongBaseTwistorPreferredCoordinate
open CompactSymplecticProjectorStrongBaseTwistorCoordinateLinear
open CompactSymplecticProjectorStrongBaseTwistorCoordinateFormula
open CompactSymplecticProjectorStrongBaseTwistorSphereSmooth
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldTwistorSphereCore
open ManifoldTwistorSphereManifold
open ManifoldTwistorSphereFiberInclusion
open ManifoldTwistorCoefficientSphere
open ManifoldTwistorSphereBundle
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff

noncomputable section
set_option maxHeartbeats 1000000

theorem strongBaseTwistorPoint_smoothTotal_formula
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
    (sphereTotalHomeomorph Q).symm
      (strongBaseTwistorPoint hLee hDesc hImm n d e q g a hq hn z) =
      sphereFiberInclusion Q (baseCoset n)
        (preferredBaseGeometricSphereMap hLee hDesc hImm n d e q g a hq hn
          (coefficientSphereHomeomorph z)) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  apply Bundle.TotalSpace.ext
  · exact strongBaseTwistorPoint_base hLee hDesc hImm n d e q g a hq hn z
  · apply heq_of_eq
    apply Subtype.ext
    have hcoord := strongBaseTwistorPoint_preferredCoordinate_linear hLee hDesc hImm
      n d e q g a hq hn z
    simpa only [sphereTotalHomeomorph, sphereTotalEquiv, fromOriginalSphere,
      sphereFiberInclusion, preferredBaseGeometricSphereMap,
      preferredBaseGeometricLinear, coefficientSphereHomeomorph,
      toEuclidean] using congrArg toEuclidean hcoord

def strongBaseSmoothTotalFiber
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
    FourDimensionalHalfSpinProjective.ProjectiveSpinor →
      SphereBundleTotal
        (strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  exact sphereFiberInclusion Q (baseCoset n) ∘
    preferredBaseGeometricSphereMap hLee hDesc hImm n d e q g a hq hn ∘
      ManifoldTwistorCorrectedHopf.correctedHopf

theorem strongBaseSmoothTotalFiber_smooth
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
    ContMDiff 𝓘(ℝ, Fin 1 → ℂ) (𝓘(ℝ, EuclideanSpace ℝ (Fin q)).prod (𝓡 2)) ∞
      (strongBaseSmoothTotalFiber hLee hDesc hImm n d e q g a hq hn) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  exact (sphereFiberInclusion_smooth Q (baseCoset n)).comp
    ((preferredBaseGeometricSphereMap_smooth hLee hDesc hImm n d e q g a hq hn).comp
      ManifoldTwistorCorrectedHopf.correctedHopf_smooth)

end
end QuaternionicSymmetry.CompactSymplecticProjectorAmbientActualTwistorSmoothBaseFiber
