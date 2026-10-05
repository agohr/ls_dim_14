import QuaternionicSymmetry.ComplexProjectiveActualConeClassicalTranslatedCarrier
import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenAlgEquiv
import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenFractions
import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenCoordinates

/-! The homogeneous translated fraction `(X_j-cX_i)/X_i` becomes the affine
coordinate polynomial `X_k-c` in the actual chart quotient. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeTranslatedFractionChart

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeClassicalTranslatedCarrier
open ComplexProjectiveActualConeDehomogenization
open ComplexProjectiveActualConeStandardOpenAlgEquiv
open ComplexProjectiveActualConeStandardOpenFractions
noncomputable section

variable {d : ℕ}

theorem translatedFraction_chart
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1))
    (k : Fin d) (c : ℂ) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    standardOpenAlgEquiv A hA hNonempty i
      (coordinateDifferenceFraction A hA hNonempty i (i.succAbove k) c) =
      Ideal.Quotient.mk (chartVanishingIdeal A i)
        (MvPolynomial.X k - MvPolynomial.C c) := by
  letI : GradedAlgebra (quotientPiece A) :=
    quotientGradedAlgebra A hA hNonempty
  have hq : coordinateClass A (i.succAbove k) - c • coordinateClass A i ∈
      quotientPiece A 1 :=
    Submodule.sub_mem (quotientPiece A 1)
      (coordinateClass_mem_degreeOne A (i.succAbove k))
      (Submodule.smul_mem (quotientPiece A 1) c
        (coordinateClass_mem_degreeOne A i))
  change ComplexProjectiveActualConeStandardOpenEquiv.standardOpenEquiv A hA
    hNonempty i (HomogeneousLocalization.Away.mk (quotientPiece A)
      (coordinateClass_mem_degreeOne A i) 1
      (coordinateClass A (i.succAbove k) - c • coordinateClass A i) _) = _
  rw [ComplexProjectiveActualConeStandardOpenEquiv.standardOpenEquiv_apply,
    standardOpenToChart_mk A hA hNonempty i 1 _ hq]
  rw [map_sub]
  have hc : quotientDehomogenize A i (c • coordinateClass A i) =
      Ideal.Quotient.mk (chartVanishingIdeal A i) (MvPolynomial.C c) := by
    rw [Algebra.smul_def, map_mul, quotientDehomogenize_chosen_coordinate, mul_one]
    change quotientDehomogenize A i
      (Ideal.Quotient.mk (vanishingIdeal A) (MvPolynomial.C c)) = _
    simp [quotientDehomogenize]
  rw [hc]
  simp [quotientDehomogenize, coordinateClass, dehomogenize_coordinate]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeTranslatedFractionChart
