import QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedCoactionLeft

/-! Exact restriction identity of the left localization extension. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedCoactionLeftNaturality

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
open ComplexProjectiveActualConeLocalizedCoactionLeft
open ComplexProjectiveActualConeStandardOpenCoaction
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

set_option maxRecDepth 2048 in
theorem localizedCoactionLeft_restrict
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i j : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty (coordinateClass A i)
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) := awayComplexAlgebra A hA hNonempty
        (coordinateClass A i * coordinateClass A j)
    ∀ a : HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i),
      localizedCoactionLeft μ A hA hNonempty hCompact i j
        ((overlapRestrictionLeft A hA hNonempty i j) a) =
      overlapTensorRestrictionLeft (r := r) A hA hNonempty i j
        (standardOpenCoaction μ A hA hNonempty hCompact i a) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty (coordinateClass A i)
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) := awayComplexAlgebra A hA hNonempty
        (coordinateClass A i * coordinateClass A j)
  letI : Algebra
      (HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i))
      (HomogeneousLocalization.Away (quotientPiece A)
        (coordinateClass A i * coordinateClass A j)) :=
    (HomogeneousLocalization.awayMap (quotientPiece A)
      (coordinateClass_mem_degreeOne A j) rfl).toAlgebra
  letI := actualOverlap_isLocalization A hA hNonempty i j
  intro a
  change localizedCoactionLeft μ A hA hNonempty hCompact i j
    ((algebraMap _ _) a) = _
  dsimp only [localizedCoactionLeft]
  exact IsLocalization.Away.lift_eq _ _ a

end
end QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedCoactionLeftNaturality
