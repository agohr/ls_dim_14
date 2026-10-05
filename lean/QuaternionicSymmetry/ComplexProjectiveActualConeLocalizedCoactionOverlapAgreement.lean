import QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedCoactionChartAgreement

/-! The two actual regular torus-family coactions on a pairwise projective
overlap are equal as full ring homomorphisms, by localization extensionality. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedCoactionOverlapAgreement

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeOverlapFractions
open ComplexProjectiveActualConeOverlapLocalization
open ComplexProjectiveActualConeOverlapComplexMaps
open ComplexProjectiveActualConeLocalizedCoactionLeft
open ComplexProjectiveActualConeLocalizedCoactionRight
open ComplexProjectiveActualConeLocalizedCoactionChartAgreement
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

set_option maxRecDepth 2048 in
theorem localizedCoactionRight_eq_left
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i j : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty (coordinateClass A i)
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A j)) := awayComplexAlgebra A hA hNonempty (coordinateClass A j)
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) := awayComplexAlgebra A hA hNonempty
        (coordinateClass A i * coordinateClass A j)
    localizedCoactionRight μ A hA hNonempty hCompact i j =
      localizedCoactionLeft μ A hA hNonempty hCompact i j := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty (coordinateClass A i)
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A j)) := awayComplexAlgebra A hA hNonempty (coordinateClass A j)
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
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (coordinateFraction A hA hNonempty i j))
  apply RingHom.ext
  intro a
  change localizedCoactionRight μ A hA hNonempty hCompact i j
      ((overlapRestrictionLeft A hA hNonempty i j) a) =
    localizedCoactionLeft μ A hA hNonempty hCompact i j
      ((overlapRestrictionLeft A hA hNonempty i j) a)
  exact localizedCoactions_agree_on_left_chart
    μ A hA hNonempty hCompact i j a

end
end QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedCoactionOverlapAgreement
