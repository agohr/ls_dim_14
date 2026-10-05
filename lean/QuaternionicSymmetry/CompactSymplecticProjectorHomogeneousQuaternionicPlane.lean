import QuaternionicSymmetry.CompactSymplecticProjectorQuotientImaginaryPlane

/-! The descended rank-three tangent plane is genuinely equivariant
under the smooth transitive action of the actual compact symplectic group. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorHomogeneousQuaternionicPlane

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorQuotientImaginaryPlane
open CompactSymplecticProjectorPlaneCocycle
open CompactSymplecticProjectorTranslationTangentEquiv
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section
set_option maxHeartbeats 5000000

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

/-- Every actual group translation carries the checked quotient
quaternionic plane at `x` exactly onto the plane at `u·x`. -/
theorem quotientImaginaryPlane_action
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (atlas : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (u : G n) (x : ProjectiveCarrier n) :
    letI := atlas.quotientCharts
    quotientImaginaryPlane hDesc hImm n d e q g atlas hq hn
      (leftCosetAction n u x) =
    (quotientImaginaryPlane hDesc hImm n d e q g atlas hq hn x).map
      (((translationTangentEquiv n d e q g atlas u x).toLinearEquiv.conjAlgEquiv ℝ).toLinearMap) := by
  letI := atlas.quotientCharts
  induction x using Quotient.inductionOn' with
  | _ v =>
      rw [show leftCosetAction n u (v : ProjectiveCarrier n) =
        ((u * v : G n) : ProjectiveCarrier n) from rfl]
      have hbase : leftCosetAction n v (baseCoset n) =
          (v : ProjectiveCarrier n) := by
        change ((v * 1 : G n) : ProjectiveCarrier n) = _
        simp
      have hc := translatedImaginaryPlane_mul hDesc hImm n d e q g atlas hq u v
      rw [hbase] at hc
      exact hc

end
end QuaternionicSymmetry.CompactSymplecticProjectorHomogeneousQuaternionicPlane
