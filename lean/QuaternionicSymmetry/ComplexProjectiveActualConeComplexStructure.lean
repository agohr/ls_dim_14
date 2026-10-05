import QuaternionicSymmetry.ComplexProjectiveActualConeDegreeZeroScalars
import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenFractions

/-! One canonical complex structure map on the whole actual cone Proj,
factored through its genuine graded degree-zero coefficient ring. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeComplexStructure

open AlgebraicGeometry CategoryTheory
open ComplexProjectiveTopology
open ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeDegreeZeroScalars
noncomputable section

variable {d : ℕ}

def actualConeProjToSpecComplex (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    Proj (quotientPiece A) ⟶ Spec (CommRingCat.of ℂ) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  exact Proj.toSpecZero (quotientPiece A) ≫
    Spec.map (CommRingCat.ofHom (scalarToDegreeZero A hA hNonempty))

end
end QuaternionicSymmetry.ComplexProjectiveActualConeComplexStructure
