import QuaternionicSymmetry.CompactSymplecticProjectorPointSymmetry
import QuaternionicSymmetry.CompactSymplecticProjectorHomogeneousQuaternionicPlane

/-! Actual Riemannian point reflections preserve the constructed
smooth rank-three quotient quaternionic plane. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorPointSymmetryQuaternionicPlane

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorPointSymmetry
open CompactSymplecticProjectorReflection
open CompactSymplecticProjectorHomogeneousQuaternionicPlane
open CompactSymplecticProjectorQuotientImaginaryPlane
open CompactSymplecticProjectorTranslationTangentEquiv
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ

theorem pointSymmetry_preserves_quotientImaginaryPlane
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x y : ProjectiveCarrier n) :
    letI := a.quotientCharts
    quotientImaginaryPlane hDesc hImm n d e q g a hq hn (pointSymmetry n x y) =
      (quotientImaginaryPlane hDesc hImm n d e q g a hq hn y).map
        (((translationTangentEquiv n d e q g a
          (reflectionElement n x) y).toLinearEquiv.conjAlgEquiv ℝ).toLinearMap) := by
  letI := a.quotientCharts
  exact quotientImaginaryPlane_action hDesc hImm n d e q g a hq hn
    (reflectionElement n x) y

end
end QuaternionicSymmetry.CompactSymplecticProjectorPointSymmetryQuaternionicPlane
