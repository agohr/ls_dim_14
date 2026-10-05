import QuaternionicSymmetry.ComplexProjectiveActualConeAllFractionTensorCoordinates
import QuaternionicSymmetry.ComplexProjectiveActualConeOverlapTensorMaps
import QuaternionicSymmetry.ComplexProjectiveActualConeTensorOverlapCocycle

/-! Exact restriction of both actual standard-open coactions to the literal
torus × pairwise-overlap ring. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeRestrictedCoactionCoordinates

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeOverlapFractions
open ComplexProjectiveActualConeAllFractionTensorCoordinates
open ComplexProjectiveActualConeStandardOpenCoaction
open ComplexProjectiveActualConeOverlapTensorMaps
open ComplexProjectiveActualConeTensorOverlapCocycle
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

theorem left_restricted_coaction_fraction
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i j k : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
      awayComplexAlgebra A hA hNonempty (coordinateClass A i)
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i * coordinateClass A j)) :=
      awayComplexAlgebra A hA hNonempty
        (coordinateClass A i * coordinateClass A j)
    overlapTensorRestrictionLeft (r := r) A hA hNonempty i j
      (standardOpenCoaction μ A hA hNonempty hCompact i
        (coordinateFraction A hA hNonempty i k)) =
      laurentMonomial (μ k - μ i) ⊗ₜ[ℂ]
        (HomogeneousLocalization.awayMap (quotientPiece A)
          (coordinateClass_mem_degreeOne A j) rfl
          (coordinateFraction A hA hNonempty i k)) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
    awayComplexAlgebra A hA hNonempty (coordinateClass A i)
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i * coordinateClass A j)) :=
    awayComplexAlgebra A hA hNonempty
      (coordinateClass A i * coordinateClass A j)
  rw [standardOpenCoaction_fraction_tensor μ A hA hNonempty hCompact i k]
  simp [overlapTensorRestrictionLeft,
    ComplexProjectiveActualConeOverlapComplexMaps.overlapRestrictionLeft,
    Algebra.TensorProduct.map_tmul]

theorem right_restricted_coaction_fraction
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i j k : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A j)) :=
      awayComplexAlgebra A hA hNonempty (coordinateClass A j)
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i * coordinateClass A j)) :=
      awayComplexAlgebra A hA hNonempty
        (coordinateClass A i * coordinateClass A j)
    overlapTensorRestrictionRight (r := r) A hA hNonempty i j
      (standardOpenCoaction μ A hA hNonempty hCompact j
        (coordinateFraction A hA hNonempty j k)) =
      laurentMonomial (μ k - μ j) ⊗ₜ[ℂ]
        (HomogeneousLocalization.awayMap (quotientPiece A)
          (coordinateClass_mem_degreeOne A i) (by ring)
          (coordinateFraction A hA hNonempty j k)) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A j)) :=
    awayComplexAlgebra A hA hNonempty (coordinateClass A j)
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i * coordinateClass A j)) :=
    awayComplexAlgebra A hA hNonempty
      (coordinateClass A i * coordinateClass A j)
  rw [standardOpenCoaction_fraction_tensor μ A hA hNonempty hCompact j k]
  simp [overlapTensorRestrictionRight,
    ComplexProjectiveActualConeOverlapComplexMaps.overlapRestrictionRight,
    Algebra.TensorProduct.map_tmul]

theorem restricted_coaction_transition
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i j k : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
      awayComplexAlgebra A hA hNonempty (coordinateClass A i)
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A j)) :=
      awayComplexAlgebra A hA hNonempty (coordinateClass A j)
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i * coordinateClass A j)) :=
      awayComplexAlgebra A hA hNonempty
        (coordinateClass A i * coordinateClass A j)
    overlapTensorRestrictionLeft (r := r) A hA hNonempty i j
      (standardOpenCoaction μ A hA hNonempty hCompact i
        (coordinateFraction A hA hNonempty i k)) *
      overlapTensorRestrictionRight (r := r) A hA hNonempty i j
        (standardOpenCoaction μ A hA hNonempty hCompact j
          (coordinateFraction A hA hNonempty j i)) =
      overlapTensorRestrictionRight (r := r) A hA hNonempty i j
        (standardOpenCoaction μ A hA hNonempty hCompact j
          (coordinateFraction A hA hNonempty j k)) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
    awayComplexAlgebra A hA hNonempty (coordinateClass A i)
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A j)) :=
    awayComplexAlgebra A hA hNonempty (coordinateClass A j)
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i * coordinateClass A j)) :=
    awayComplexAlgebra A hA hNonempty
      (coordinateClass A i * coordinateClass A j)
  rw [left_restricted_coaction_fraction μ A hA hNonempty hCompact i j k,
    right_restricted_coaction_fraction μ A hA hNonempty hCompact i j i,
    right_restricted_coaction_fraction μ A hA hNonempty hCompact i j k]
  exact tensor_overlap_coordinate_cocycle μ A hA hNonempty i j k

end
end QuaternionicSymmetry.ComplexProjectiveActualConeRestrictedCoactionCoordinates
