import QuaternionicSymmetry.CompactSymplecticProjectorPlaneCocycle

/-! The actual quotient carries a canonically defined rank-three plane
of tangent endomorphisms at every point, constructed by descent of the
checked quaternionic base plane. Smoothness is a separate next step. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorQuotientImaginaryPlane

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorTranslatedImaginaryPlane
open CompactSymplecticProjectorPlaneCocycle
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

/-- An actual, representative-independent rank-three quaternionic
endomorphism plane in the true quotient tangent at `x`. -/
def quotientImaginaryPlane
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (atlas : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) :
    letI := atlas.quotientCharts
    Submodule ℝ (Module.End ℝ (TangentSpace 𝓘(ℝ, RModel q) x)) := by
  letI := atlas.quotientCharts
  exact Quotient.liftOn' x
    (fun u : G n => translatedImaginaryPlane hDesc hImm n d e q g atlas hq u)
    (by
      intro u v huv
      exact translatedImaginaryPlane_eq_of_coset_eq hDesc hImm n d e q g atlas
        hq hn u v (Quotient.sound' huv))

@[simp] theorem quotientImaginaryPlane_mk
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (atlas : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (u : G n) :
    letI := atlas.quotientCharts
    quotientImaginaryPlane hDesc hImm n d e q g atlas hq hn (u : ProjectiveCarrier n) =
      translatedImaginaryPlane hDesc hImm n d e q g atlas hq u := rfl

/-- The descended tangent endomorphism plane has real rank exactly three
at every actual quotient point. -/
theorem quotientImaginaryPlane_finrank
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (atlas : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) :
    letI := atlas.quotientCharts
    Module.finrank ℝ (quotientImaginaryPlane hDesc hImm n d e q g atlas hq hn x) = 3 := by
  letI := atlas.quotientCharts
  induction x using Quotient.inductionOn' with
  | _ u => exact translatedImaginaryPlane_finrank hDesc hImm n d e q g atlas hq hn u

end
end QuaternionicSymmetry.CompactSymplecticProjectorQuotientImaginaryPlane
