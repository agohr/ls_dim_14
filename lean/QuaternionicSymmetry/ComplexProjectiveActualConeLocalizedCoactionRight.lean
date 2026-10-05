import QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedCoactionLeft

/-! The right standard-open coaction also extends to the genuine pairwise
overlap localization, with the same literal target ring as the left lift. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedCoactionRight

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeOverlapFractions
open ComplexProjectiveActualConeOverlapLocalization
open ComplexProjectiveActualConeOverlapTensorMaps
open ComplexProjectiveActualConeOverlapUnits
open ComplexProjectiveActualConeRestrictedCoactionUnits
open ComplexProjectiveActualConeRestrictedCoactionCoordinates
open ComplexProjectiveActualConeStandardOpenCoaction
open ComplexProjectiveDiagonalLaurentUnits
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

theorem right_restricted_coaction_fraction_isUnit
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i j : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A j)) :=
      awayComplexAlgebra A hA hNonempty (coordinateClass A j)
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i * coordinateClass A j)) :=
      awayComplexAlgebra A hA hNonempty
        (coordinateClass A i * coordinateClass A j)
    IsUnit (overlapTensorRestrictionRight (r := r) A hA hNonempty i j
      (standardOpenCoaction μ A hA hNonempty hCompact j
        (coordinateFraction A hA hNonempty j i))) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A j)) :=
    awayComplexAlgebra A hA hNonempty (coordinateClass A j)
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i * coordinateClass A j)) :=
    awayComplexAlgebra A hA hNonempty
      (coordinateClass A i * coordinateClass A j)
  rw [right_restricted_coaction_fraction μ A hA hNonempty hCompact i j i]
  exact isUnit_tensor _ _
    (laurentMonomial_isUnit (μ i - μ j))
    (right_overlap_coordinate_isUnit A hA hNonempty i j)

def localizedCoactionRight
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i j : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A j)) :=
      awayComplexAlgebra A hA hNonempty (coordinateClass A j)
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
      (quotientPiece A) (coordinateClass A j)) :=
    awayComplexAlgebra A hA hNonempty (coordinateClass A j)
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i * coordinateClass A j)) :=
    awayComplexAlgebra A hA hNonempty
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
  let g : HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A j) →+*
      TorusCoordinateRing r ⊗[ℂ]
        HomogeneousLocalization.Away (quotientPiece A)
          (coordinateClass A i * coordinateClass A j) :=
    (overlapTensorRestrictionRight (r := r) A hA hNonempty i j).toRingHom.comp
      (standardOpenCoaction μ A hA hNonempty hCompact j)
  exact IsLocalization.Away.lift (g := g)
    (coordinateFraction A hA hNonempty j i)
    (right_restricted_coaction_fraction_isUnit μ A hA hNonempty hCompact i j)

end
end QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedCoactionRight
