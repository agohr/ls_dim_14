import QuaternionicSymmetry.ComplexProjectiveDiagonalLaurentTransition
import QuaternionicSymmetry.ComplexProjectiveActualConeDegreeZeroScalars

/-! Explicit complex-algebra structures on the degree-zero ring and each
actual homogeneous localization, all induced from the same global scalar
map rather than chosen independently on projective charts. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeAwayComplexAlgebra

open ComplexProjectiveTopology
open ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeDegreeZeroScalars
noncomputable section

variable {d : ℕ}

def degreeZeroComplexAlgebra (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty) :
    Algebra ℂ (quotientPiece A 0) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  exact (scalarToDegreeZero A hA hNonempty).toAlgebra

def awayComplexAlgebra (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (f : MvPolynomial (Fin (d + 1)) ℂ ⧸ vanishingIdeal A) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A) f) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  exact ((HomogeneousLocalization.fromZeroRingHom (quotientPiece A)
    (Submonoid.powers f)).comp (scalarToDegreeZero A hA hNonempty)).toAlgebra

end
end QuaternionicSymmetry.ComplexProjectiveActualConeAwayComplexAlgebra
