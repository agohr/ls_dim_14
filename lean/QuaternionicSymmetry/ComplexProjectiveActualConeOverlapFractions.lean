import QuaternionicSymmetry.ComplexProjectiveActualConeOverlapScalars

/-! The two genuine homogeneous-localization presentations of a coordinate
on a pairwise standard-open overlap satisfy the rational transition law. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeOverlapFractions

open ComplexProjectiveTopology
open ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
noncomputable section

variable {d : ℕ}

def coordinateFraction (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (i k : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  exact HomogeneousLocalization.Away.mk (quotientPiece A)
    (coordinateClass_mem_degreeOne A i) 1 (coordinateClass A k)
    (coordinateClass_mem_degreeOne A k)

theorem overlap_coordinate_transition (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (i j k : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    HomogeneousLocalization.awayMap (quotientPiece A)
      (coordinateClass_mem_degreeOne A j) rfl
      (coordinateFraction A hA hNonempty i k) *
    HomogeneousLocalization.awayMap (quotientPiece A)
      (coordinateClass_mem_degreeOne A i) (by ring)
      (coordinateFraction A hA hNonempty j i) =
    HomogeneousLocalization.awayMap (quotientPiece A)
      (coordinateClass_mem_degreeOne A i) (by ring)
      (coordinateFraction A hA hNonempty j k) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  apply HomogeneousLocalization.val_injective
  simp [coordinateFraction, HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.val_mul, Localization.mk_mul,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, one_mem _, ?_⟩
  ring

end
end QuaternionicSymmetry.ComplexProjectiveActualConeOverlapFractions
