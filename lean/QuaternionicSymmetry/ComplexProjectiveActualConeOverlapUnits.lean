import QuaternionicSymmetry.ComplexProjectiveActualConeOverlapTensorMaps

/-! The coordinate inverted when passing from a standard open to a
pairwise overlap is an actual unit there. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeOverlapUnits

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeOverlapFractions
open ComplexProjectiveActualConeOverlapLocalization
open ComplexProjectiveActualConeOverlapComplexMaps
noncomputable section

variable {d : ℕ}

theorem left_overlap_coordinate_isUnit
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i j : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
      ComplexProjectiveActualConeAwayComplexAlgebra.awayComplexAlgebra
        A hA hNonempty (coordinateClass A i)
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i * coordinateClass A j)) :=
      ComplexProjectiveActualConeAwayComplexAlgebra.awayComplexAlgebra
        A hA hNonempty (coordinateClass A i * coordinateClass A j)
    IsUnit ((overlapRestrictionLeft A hA hNonempty i j)
      (coordinateFraction A hA hNonempty i j)) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra
      (HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i))
      (HomogeneousLocalization.Away (quotientPiece A)
        (coordinateClass A i * coordinateClass A j)) :=
    (HomogeneousLocalization.awayMap (quotientPiece A)
      (coordinateClass_mem_degreeOne A j) rfl).toAlgebra
  letI := actualOverlap_isLocalization A hA hNonempty i j
  change IsUnit ((algebraMap
    (HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i))
    (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)))
    (coordinateFraction A hA hNonempty i j))
  exact IsLocalization.Away.algebraMap_isUnit _

theorem right_overlap_coordinate_isUnit
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i j : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A j)) :=
      ComplexProjectiveActualConeAwayComplexAlgebra.awayComplexAlgebra
        A hA hNonempty (coordinateClass A j)
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i * coordinateClass A j)) :=
      ComplexProjectiveActualConeAwayComplexAlgebra.awayComplexAlgebra
        A hA hNonempty (coordinateClass A i * coordinateClass A j)
    IsUnit ((overlapRestrictionRight A hA hNonempty i j)
      (coordinateFraction A hA hNonempty j i)) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra
      (HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A j))
      (HomogeneousLocalization.Away (quotientPiece A)
        (coordinateClass A i * coordinateClass A j)) :=
    (HomogeneousLocalization.awayMap (quotientPiece A)
      (coordinateClass_mem_degreeOne A i) (by ring)).toAlgebra
  haveI : IsLocalization.Away (coordinateFraction A hA hNonempty j i)
      (HomogeneousLocalization.Away (quotientPiece A)
        (coordinateClass A i * coordinateClass A j)) := by
    rw [coordinateFraction_eq_isLocalizationElem A hA hNonempty j i]
    exact HomogeneousLocalization.Away.isLocalization_mul
      (coordinateClass_mem_degreeOne A j)
      (coordinateClass_mem_degreeOne A i) (by ring) (by decide)
  change IsUnit ((algebraMap
    (HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A j))
    (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)))
    (coordinateFraction A hA hNonempty j i))
  exact IsLocalization.Away.algebraMap_isUnit _

end
end QuaternionicSymmetry.ComplexProjectiveActualConeOverlapUnits
