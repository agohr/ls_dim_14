import QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedSchemeNaturality
import QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedCoactionOverlapAgreement

/-! The two localized regular torus-family actions are the same literal
affine scheme morphism on the actual homogeneous pairwise overlap. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedSchemeAgreement

open AlgebraicGeometry CategoryTheory
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeLocalizedCoactionLeft
open ComplexProjectiveActualConeLocalizedCoactionRight
open ComplexProjectiveActualConeLocalizedCoactionOverlapAgreement
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

theorem localized_scheme_actions_agree
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i j : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
    Spec.map (CommRingCat.ofHom
      (localizedCoactionLeft μ A hA hNonempty hCompact i j)) =
    Spec.map (CommRingCat.ofHom
      (localizedCoactionRight μ A hA hNonempty hCompact i j)) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
  rw [localizedCoactionRight_eq_left μ A hA hNonempty hCompact i j]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedSchemeAgreement
