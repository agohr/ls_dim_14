import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenTensorCoordinates
import QuaternionicSymmetry.ComplexProjectiveActualConeOverlapFractions

/-! Each actual pairwise projective overlap is the localization of either
standard-open coordinate ring at the other coordinate fraction. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeOverlapLocalization

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeOverlapFractions
noncomputable section

variable {d : ℕ}

theorem coordinateFraction_eq_isLocalizationElem
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i j : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    coordinateFraction A hA hNonempty i j =
      HomogeneousLocalization.Away.isLocalizationElem
        (coordinateClass_mem_degreeOne A i)
        (coordinateClass_mem_degreeOne A j) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  apply HomogeneousLocalization.val_injective
  simp [coordinateFraction, HomogeneousLocalization.Away.isLocalizationElem]

theorem actualOverlap_isLocalization
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i j : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    letI : Algebra
      (HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i))
      (HomogeneousLocalization.Away (quotientPiece A)
        (coordinateClass A i * coordinateClass A j)) :=
      (HomogeneousLocalization.awayMap (quotientPiece A)
        (coordinateClass_mem_degreeOne A j) rfl).toAlgebra
    IsLocalization.Away (coordinateFraction A hA hNonempty i j)
      (HomogeneousLocalization.Away (quotientPiece A)
        (coordinateClass A i * coordinateClass A j)) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra
      (HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i))
      (HomogeneousLocalization.Away (quotientPiece A)
        (coordinateClass A i * coordinateClass A j)) :=
    (HomogeneousLocalization.awayMap (quotientPiece A)
      (coordinateClass_mem_degreeOne A j) rfl).toAlgebra
  rw [coordinateFraction_eq_isLocalizationElem A hA hNonempty i j]
  exact HomogeneousLocalization.Away.isLocalization_mul
    (coordinateClass_mem_degreeOne A i)
    (coordinateClass_mem_degreeOne A j) rfl (by decide)

end
end QuaternionicSymmetry.ComplexProjectiveActualConeOverlapLocalization
