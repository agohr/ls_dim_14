import QuaternionicSymmetry.ComplexProjectiveActualConeAwayComplexAlgebra
import QuaternionicSymmetry.ComplexProjectiveActualConeChartScalars

/-! The genuine actual standard-open ring comparison is an isomorphism
of complex algebras for the global degree-zero-induced scalar structure. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenAlgEquiv

open ComplexProjectiveTopology
open ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeStandardOpenEquiv
open ComplexProjectiveActualConeChartScalars
noncomputable section

variable {d : ℕ}

def standardOpenAlgEquiv (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
      awayComplexAlgebra A hA hNonempty (coordinateClass A i)
    HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i) ≃ₐ[ℂ]
      (MvPolynomial (Fin d) ℂ ⧸ chartVanishingIdeal A i) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
    awayComplexAlgebra A hA hNonempty (coordinateClass A i)
  exact { standardOpenEquiv A hA hNonempty i with
    commutes' := standardOpenToChart_scalar A hA hNonempty i }

end
end QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenAlgEquiv
