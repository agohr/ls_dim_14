import QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedCoactionLeftNaturality
import QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedCoactionRight

/-! Exact restriction identity of the right localization extension. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedCoactionRightNaturality

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeOverlapComplexMaps
open ComplexProjectiveActualConeOverlapLocalization
open ComplexProjectiveActualConeOverlapFractions
open ComplexProjectiveActualConeOverlapTensorMaps
open ComplexProjectiveActualConeLocalizedCoactionRight
open ComplexProjectiveActualConeStandardOpenCoaction
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

set_option maxRecDepth 2048 in
theorem localizedCoactionRight_restrict
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i j : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A j)) := awayComplexAlgebra A hA hNonempty (coordinateClass A j)
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) := awayComplexAlgebra A hA hNonempty
        (coordinateClass A i * coordinateClass A j)
    ∀ a : HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A j),
      localizedCoactionRight μ A hA hNonempty hCompact i j
        ((overlapRestrictionRight A hA hNonempty i j) a) =
      overlapTensorRestrictionRight (r := r) A hA hNonempty i j
        (standardOpenCoaction μ A hA hNonempty hCompact j a) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A j)) := awayComplexAlgebra A hA hNonempty (coordinateClass A j)
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) := awayComplexAlgebra A hA hNonempty
        (coordinateClass A i * coordinateClass A j)
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
  intro a
  change localizedCoactionRight μ A hA hNonempty hCompact i j
    ((algebraMap _ _) a) = _
  dsimp only [localizedCoactionRight]
  exact IsLocalization.Away.lift_eq _ _ a

end
end QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedCoactionRightNaturality
