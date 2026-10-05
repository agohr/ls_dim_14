import QuaternionicSymmetry.ComplexProjectiveChartTensorBaseChangeGeneric
import QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleChartQuotientCoaction
import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenAlgEquiv

/-! The literal two-torus base change of an actual homogeneous standard-open
ring is the checked double-Laurent chart quotient. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeDoubleStandardOpenRing

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveDiagonalDoubleChartBaseChange
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeStandardOpenAlgEquiv
open ComplexProjectiveChartTensorBaseChangeGeneric
open ComplexTorusLaurentComultiplication
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

def doubleBaseChangedStandardOpenEquiv
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    DoubleTorusCoordinateRing r ⊗[ℂ]
      HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i) ≃ₐ[DoubleTorusCoordinateRing r]
    DoubleTorusCoordinateRing r ⊗[ℂ]
      (MvPolynomial (Fin d) ℂ ⧸ chartVanishingIdeal A i) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  exact Algebra.TensorProduct.congr
    (AlgEquiv.refl : DoubleTorusCoordinateRing r ≃ₐ[DoubleTorusCoordinateRing r]
      DoubleTorusCoordinateRing r)
    (standardOpenAlgEquiv A hA hNonempty i)

def doubleBaseChangedStandardOpenFamilyEquiv
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    DoubleTorusCoordinateRing r ⊗[ℂ]
      HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i) ≃+*
    (MvPolynomial (Fin d) (DoubleTorusCoordinateRing r) ⧸
      doubleExtendedChartIdeal (r := r) A i) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  exact (doubleBaseChangedStandardOpenEquiv (r := r) A hA hNonempty i).toRingEquiv.trans
    (chartFamilyProductRingEquiv (DoubleTorusCoordinateRing r)
      (chartVanishingIdeal A i)).symm

end
end QuaternionicSymmetry.ComplexProjectiveActualConeDoubleStandardOpenRing
