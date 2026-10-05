import QuaternionicSymmetry.ComplexProjectiveActualConeDirectLocalSchemeAction
import QuaternionicSymmetry.ComplexProjectiveActualConeProjProductCoordinateCover

/-! The direct homogeneous-coaction scheme morphisms are indexed by the
actual finite open cover of the literal torus × cone-Proj product. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeProductCoverDirectAction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeProjProductCoordinateCover
open ComplexProjectiveActualConeDirectLocalSchemeAction
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

def productCoverDirectLocalAction
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    (actualConeTorusProductCoordinateCover (r := r) A hA hNonempty).X i ⟶
      Proj (quotientPiece A) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  exact directBasicOpenProductAction μ A hA hNonempty hCompact i

end
end QuaternionicSymmetry.ComplexProjectiveActualConeProductCoverDirectAction
