import QuaternionicSymmetry.ComplexProjectiveActualConeDehomogenization

/-! The actual cone quotient dehomogenization extends from the chosen
coordinate to its genuine degree-zero homogeneous localization. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenMap

open ComplexProjectiveTopology
open ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeDehomogenization
noncomputable section

variable {d : ℕ}

def standardOpenToChart (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i) →+*
      (MvPolynomial (Fin d) ℂ ⧸ chartVanishingIdeal A i) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  let e := quotientDehomogenize A i
  have he : IsUnit (e (coordinateClass A i)) := by
    rw [quotientDehomogenize_chosen_coordinate]
    exact isUnit_one
  exact (Localization.awayLift e (coordinateClass A i) he).comp
    (algebraMap _ (Localization.Away (coordinateClass A i)))

end
end QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenMap
