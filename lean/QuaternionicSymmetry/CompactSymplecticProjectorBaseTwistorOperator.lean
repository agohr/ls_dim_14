import QuaternionicSymmetry.CompactSymplecticProjectorStabilizerExactSphereTangent
import QuaternionicSymmetry.CompactSymplecticProjectorQuotientImaginaryPlane
import QuaternionicSymmetry.FourDimensionalHalfSpinHopfNorthSection

/-! The actual base-tangent quaternion algebra action sends each unit
imaginary quaternion to a complex structure in the descended projector
three-plane. This is the old-atlas operator used for the intrinsic twistor
fiber comparison; no preferred chart frame is identified with isotropy. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorBaseTwistorOperator

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseQuaternionAction
open CompactSymplecticProjectorBaseImaginaryPlane
open CompactSymplecticProjectorQuotientImaginaryPlane
open CompactSymplecticProjectorStabilizerTransport
open CompactSymplecticProjectorTranslatedImaginaryPlane
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open QuaternionicUnitScalarIsometries
open ManifoldTwistorSphereBundle
open FourDimensionalHalfSpinHopfNorthSection
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff

noncomputable section
set_option maxHeartbeats 1000000

private abbrev RModel (q : ℕ) := Fin q → ℝ

theorem base_unit_operator_mem_plane
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (z : coefficientSphere) :
    letI := a.quotientCharts
    baseQuaternionAction hDesc hImm n d e q g a hq (pureScalar z.1) ∈
      quotientImaginaryPlane hDesc hImm n d e q g a hq hn (baseCoset n) := by
  letI := a.quotientCharts
  have hplane : quotientImaginaryPlane hDesc hImm n d e q g a hq hn (baseCoset n) =
      baseImaginaryPlane hDesc hImm n d e q g a hq := by
    change translatedImaginaryPlane hDesc hImm n d e q g a hq
      (1 : firstPairStabilizer n).1 = _
    exact translatedImaginaryPlane_stabilizer hDesc hImm n d e q g a hq hn 1
  rw [hplane]
  exact action_imaginary_mem hDesc hImm n d e q g a hq _ (pureScalar_re _)

theorem base_unit_operator_square
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (z : coefficientSphere) :
    letI := a.quotientCharts
    ∀ v : TangentSpace 𝓘(ℝ, RModel q) (baseCoset n),
      baseQuaternionAction hDesc hImm n d e q g a hq (pureScalar z.1)
        (baseQuaternionAction hDesc hImm n d e q g a hq (pureScalar z.1) v) = -v := by
  letI := a.quotientCharts
  intro v
  have hz := pureScalar_sq z
  let F := baseQuaternionAction hDesc hImm n d e q g a hq
  have h : F (pureScalar z.1 * pureScalar z.1) = F (-1 : ℍ) := congrArg F hz
  rw [map_mul] at h
  have hv := congrArg (fun T : Module.End ℝ (TangentSpace 𝓘(ℝ, RModel q) (baseCoset n)) => T v) h
  simpa [F] using hv

end
end QuaternionicSymmetry.CompactSymplecticProjectorBaseTwistorOperator
