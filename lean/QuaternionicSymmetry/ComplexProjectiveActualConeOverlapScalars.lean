import QuaternionicSymmetry.ComplexProjectiveActualConeProjOverlap
import QuaternionicSymmetry.ComplexProjectiveActualConeDegreeZeroScalars

/-! Both restriction maps to an actual coordinate-pair overlap agree on
the canonical global complex scalars. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeOverlapScalars

open ComplexProjectiveTopology
open ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeDegreeZeroScalars
noncomputable section

variable {d : ℕ}

theorem overlap_scalar_from_left_eq_right (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (i j : Fin (d + 1)) (c : ℂ) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    HomogeneousLocalization.awayMap (quotientPiece A)
      (coordinateClass_mem_degreeOne A j) rfl
      (HomogeneousLocalization.fromZeroRingHom (quotientPiece A)
        (Submonoid.powers (coordinateClass A i))
        (scalarToDegreeZero A hA hNonempty c)) =
    HomogeneousLocalization.awayMap (quotientPiece A)
      (coordinateClass_mem_degreeOne A i) (by ring)
      (HomogeneousLocalization.fromZeroRingHom (quotientPiece A)
        (Submonoid.powers (coordinateClass A j))
        (scalarToDegreeZero A hA hNonempty c)) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  simp only [HomogeneousLocalization.awayMap_fromZeroRingHom]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeOverlapScalars
