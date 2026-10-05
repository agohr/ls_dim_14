import QuaternionicSymmetry.ComplexProjectiveActualConeDirectClassicalAction
import QuaternionicSymmetry.ComplexProjectiveActualConeGlobalSchemeAction

/-! The glued regular action agrees with the diagonal analytic action on
classical projective points, using the literal product-cover inclusion. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeGlobalClassicalAction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction
open ComplexProjectiveConeQuotientHomogeneousPieces ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeClassicalPointInjective
open ComplexProjectiveActualConeProjProductCoordinateCover
open ComplexProjectiveActualConeProductCoverDirectAction
open ComplexProjectiveActualConeDirectLocalSchemeAction
open ComplexProjectiveActualConeDirectClassicalProductPoint
open ComplexProjectiveActualConeDirectClassicalAction
open ComplexProjectiveActualConeGlobalSchemeAction
open ComplexProjectiveTorusPreservation
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

theorem globalSchemeAction_classical_on_chart
    (μ : Fin (d + 1) → Fin r → ℤ)
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) (z : ComplexTorus r)
    (x : A) (hi : x.1.rep i ≠ 0) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
      awayComplexAlgebra A hA hNonempty (coordinateClass A i)
    (globalSchemeAction μ A hA hNonempty hCompact)
      ((actualConeTorusProductCoordinateCover (r := r) A hA hNonempty).f i
        (directClassicalProductPoint A hA hNonempty i z x hi)) =
      classicalPointToActualProjFixed A hA hNonempty
        ⟨projectiveAction μ z x.1,
          mapsTo_of_compact μ A hA hCompact z x.2⟩ := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
    awayComplexAlgebra A hA hNonempty (coordinateClass A i)
  have h := globalSchemeAction_restrict μ A hA hNonempty hCompact i
  have hx := congrArg (fun f => f
      (directClassicalProductPoint A hA hNonempty i z x hi)) h
  simpa [productCoverDirectLocalAction] using
    hx.trans (directBasicOpenProductAction_classical μ A hA hNonempty
      hCompact i z x hi)

end
end QuaternionicSymmetry.ComplexProjectiveActualConeGlobalClassicalAction
