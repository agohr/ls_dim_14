import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenFractions

/-! Every affine-chart coordinate is represented by its genuine homogeneous
degree-zero fraction `X_j / X_i`. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenCoordinates

open ComplexProjectiveTopology
open ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeDehomogenization
open ComplexProjectiveActualConeStandardOpenMap
open ComplexProjectiveActualConeStandardOpenFractions
noncomputable section

variable {d : ℕ}

theorem standardOpenToChart_coordinate (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (i : Fin (d + 1)) (k : Fin d) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    standardOpenToChart A hA hNonempty i
      (HomogeneousLocalization.Away.mk (quotientPiece A)
        (coordinateClass_mem_degreeOne A i) 1
        (coordinateClass A (i.succAbove k))
        (coordinateClass_mem_degreeOne A (i.succAbove k))) =
      Ideal.Quotient.mk (chartVanishingIdeal A i) (MvPolynomial.X k) := by
  rw [standardOpenToChart_mk A hA hNonempty i 1
    (coordinateClass A (i.succAbove k))
    (coordinateClass_mem_degreeOne A (i.succAbove k))]
  simp [quotientDehomogenize, coordinateClass,
    dehomogenize_coordinate]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenCoordinates
