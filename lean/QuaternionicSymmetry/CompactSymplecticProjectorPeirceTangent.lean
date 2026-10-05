import QuaternionicSymmetry.ProjectorPeirceTangentProjection
import QuaternionicSymmetry.CompactSymplecticProjectorTangentConstraints

/-! The Peirce projection associated to the actual orbit projector is
identity on the genuine immersed tangent image at every quotient point. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorPeirceTangent

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticClosedSubgroupSource
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticProjectorTangentConstraints
open CompactSymplecticProjectorOrbit
open CompactSymplecticProjectorOrbitQuotient
open ProjectorPeirceTangentProjection
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ
private abbrev RModel (d : ℕ) := Fin d → ℝ

theorem actual_tangentPart_eq_mfderiv
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (x : ProjectiveCarrier n) :
    letI := a.quotientCharts
    ∀ (v : TangentSpace 𝓘(ℝ,RModel q) x),
      let P : Mat n := quotientOrbitProjector n x
      let X : Mat n := mfderiv 𝓘(ℝ,RModel q) 𝓘(ℝ,Mat n)
        (quotientOrbitProjector n) x v
      tangentPart P X = X := by
  letI := a.quotientCharts
  intro v
  apply tangentPart_eq_self_of_tangent
  · induction x using Quotient.inductionOn' with
    | _ u => exact orbitProjector_idempotent n u
  · exact tangent_projector_offDiagonal hDesc n d e q g a x v

end
end QuaternionicSymmetry.CompactSymplecticProjectorPeirceTangent
