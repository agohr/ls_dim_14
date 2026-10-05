import QuaternionicSymmetry.ComplexProjectiveActualConeRestrictedCoactionUnits

/-! The actual left standard-open coaction extends across the coordinate
inverted on the pairwise overlap, by the localization universal property. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedCoactionLeft

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeOverlapFractions
open ComplexProjectiveActualConeOverlapLocalization
open ComplexProjectiveActualConeOverlapTensorMaps
open ComplexProjectiveActualConeRestrictedCoactionUnits
open ComplexProjectiveActualConeStandardOpenCoaction
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

def localizedCoactionLeft
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i j : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
      awayComplexAlgebra A hA hNonempty (coordinateClass A i)
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i * coordinateClass A j)) :=
      awayComplexAlgebra A hA hNonempty
        (coordinateClass A i * coordinateClass A j)
    HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j) →+*
      TorusCoordinateRing r ⊗[ℂ]
        HomogeneousLocalization.Away (quotientPiece A)
          (coordinateClass A i * coordinateClass A j) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
    awayComplexAlgebra A hA hNonempty (coordinateClass A i)
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i * coordinateClass A j)) :=
    awayComplexAlgebra A hA hNonempty
      (coordinateClass A i * coordinateClass A j)
  letI : Algebra
      (HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i))
      (HomogeneousLocalization.Away (quotientPiece A)
        (coordinateClass A i * coordinateClass A j)) :=
    (HomogeneousLocalization.awayMap (quotientPiece A)
      (coordinateClass_mem_degreeOne A j) rfl).toAlgebra
  letI := actualOverlap_isLocalization A hA hNonempty i j
  let g : HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i) →+*
      TorusCoordinateRing r ⊗[ℂ]
        HomogeneousLocalization.Away (quotientPiece A)
          (coordinateClass A i * coordinateClass A j) :=
    (overlapTensorRestrictionLeft (r := r) A hA hNonempty i j).toRingHom.comp
      (standardOpenCoaction μ A hA hNonempty hCompact i)
  exact IsLocalization.Away.lift (g := g)
    (coordinateFraction A hA hNonempty i j)
    (left_restricted_coaction_fraction_isUnit μ A hA hNonempty hCompact i j)

end
end QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedCoactionLeft
