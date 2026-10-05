import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleIteratedRestriction
import QuaternionicSymmetry.ComplexProjectiveActualConeGlobalMultiplicationLocalFormula

/-! The actual glued regular torus-family morphism satisfies the genuine
Scheme-theoretic multiplication law on the literal two-torus product with
the actual cone Proj. The second torus parameter acts first and the first
acts on its result. This is equality of Scheme morphisms, not pointwise
agreement or a stipulated algebraic-action predicate. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeGlobalSchemeActionMultiplication

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeDoubleProductCover
open ComplexProjectiveActualConeDoubleProductLocalAction
open ComplexProjectiveActualConeDirectLocalSchemeAction
open ComplexProjectiveActualConeDoubleLocalIterated
open ComplexProjectiveActualConeDoubleIteratedRestriction
open ComplexProjectiveActualConeGlobalMultiplicationLocalFormula
open ComplexProjectiveActualConeDoubleProductMultiplication
open ComplexProjectiveActualConeDoubleProductIteratedAction
open ComplexProjectiveActualConeGlobalSchemeAction
open ComplexTorusLaurentComultiplication
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

theorem globalSchemeAction_multiplication
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    actualConeDoubleProductMultiplication r A hA hNonempty ≫
      globalSchemeAction μ A hA hNonempty hCompact =
    actualConeDoubleProductIterated r μ A hA hNonempty hCompact ≫
      globalSchemeAction μ A hA hNonempty hCompact := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  let 𝒰₂ := actualConeDoubleTorusProductCoordinateCover (r := r) A hA hNonempty
  apply 𝒰₂.hom_ext
  intro i
  calc
    𝒰₂.f i ≫ (actualConeDoubleProductMultiplication r A hA hNonempty ≫
        globalSchemeAction μ A hA hNonempty hCompact) =
      directBasicOpenDoubleMultiplicationAction μ A hA hNonempty hCompact i := by
        simpa only [Category.assoc] using
          global_multiplication_action_restrict μ A hA hNonempty hCompact i
    _ = directBasicOpenDoubleIterated μ A hA hNonempty hCompact i ≫
        directBasicOpenProductAction μ A hA hNonempty hCompact i :=
      (directBasicOpenDoubleIterated_action μ A hA hNonempty hCompact i).symm
    _ = 𝒰₂.f i ≫ (actualConeDoubleProductIterated r μ A hA hNonempty hCompact ≫
        globalSchemeAction μ A hA hNonempty hCompact) := by
      rw [← Category.assoc,
        actualConeDoubleProductIterated_restrict μ A hA hNonempty hCompact i]
      rw [Category.assoc,
        globalSchemeAction_restrict μ A hA hNonempty hCompact i]
      rfl

end
end QuaternionicSymmetry.ComplexProjectiveActualConeGlobalSchemeActionMultiplication
