import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleMultiplicationRestriction
import QuaternionicSymmetry.ComplexProjectiveActualConeGlobalSchemeAction

/-! The literal global multiplication-then-action composite restricts to
the checked two-parameter coaction on every actual standard-open chart.
The equality with the categorical iterated action is the next step. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeGlobalMultiplicationLocalFormula

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeProjProductCoordinateCover
open ComplexProjectiveActualConeDoubleProductCover
open ComplexProjectiveActualConeDoubleProductLocalAction
open ComplexProjectiveActualConeDoubleLocalMultiplication
open ComplexProjectiveActualConeDoubleMultiplicationRestriction
open ComplexProjectiveActualConeDoubleProductMultiplication
open ComplexProjectiveActualConeGlobalSchemeAction
open ComplexTorusLaurentComultiplication
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

theorem global_multiplication_action_restrict
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    let 𝒰₂ := actualConeDoubleTorusProductCoordinateCover (r := r) A hA hNonempty
    𝒰₂.f i ≫ actualConeDoubleProductMultiplication r A hA hNonempty ≫
      globalSchemeAction μ A hA hNonempty hCompact =
    directBasicOpenDoubleMultiplicationAction μ A hA hNonempty hCompact i := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  change ((actualConeDoubleTorusProductCoordinateCover (r := r) A hA hNonempty).f i ≫
      actualConeDoubleProductMultiplication r A hA hNonempty) ≫
      globalSchemeAction μ A hA hNonempty hCompact = _
  rw [actualConeDoubleProductMultiplication_restrict (r := r) A hA hNonempty i]
  rw [Category.assoc]
  rw [globalSchemeAction_restrict μ A hA hNonempty hCompact i]
  exact directBasicOpenDoubleMultiplication_action μ A hA hNonempty hCompact i

end
end QuaternionicSymmetry.ComplexProjectiveActualConeGlobalMultiplicationLocalFormula
