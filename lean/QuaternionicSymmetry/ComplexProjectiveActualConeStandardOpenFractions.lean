import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenMap

/-! Coordinate-fraction computation for the genuine standard-open map. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenFractions

open ComplexProjectiveTopology
open ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeDehomogenization
open ComplexProjectiveActualConeStandardOpenMap
noncomputable section

variable {d : ℕ}

theorem standardOpenToChart_mk (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (i : Fin (d + 1)) (n : ℕ)
    (q : MvPolynomial (Fin (d + 1)) ℂ ⧸ vanishingIdeal A)
    (hq : q ∈ quotientPiece A n) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    standardOpenToChart A hA hNonempty i
      (HomogeneousLocalization.Away.mk (quotientPiece A)
        (coordinateClass_mem_degreeOne A i) n q (by simpa using hq)) =
      quotientDehomogenize A i q := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  simp only [standardOpenToChart, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk]
  convert Localization.awayLift_mk (quotientDehomogenize A i)
    (coordinateClass A i) q 1 (by simp [quotientDehomogenize_chosen_coordinate]) n using 1
  simp

end
end QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenFractions
