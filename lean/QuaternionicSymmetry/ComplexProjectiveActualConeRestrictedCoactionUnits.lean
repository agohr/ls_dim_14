import QuaternionicSymmetry.ComplexProjectiveActualConeRestrictedCoactionCoordinates
import QuaternionicSymmetry.ComplexProjectiveActualConeOverlapUnits
import QuaternionicSymmetry.ComplexProjectiveDiagonalLaurentUnits

/-! The standard-open coaction sends the coordinate inverted on a pairwise
overlap to a unit of the literal torus × overlap coordinate ring. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeRestrictedCoactionUnits

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeOverlapFractions
open ComplexProjectiveActualConeOverlapTensorMaps
open ComplexProjectiveActualConeOverlapUnits
open ComplexProjectiveActualConeRestrictedCoactionCoordinates
open ComplexProjectiveActualConeStandardOpenCoaction
open ComplexProjectiveDiagonalLaurentUnits
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

theorem isUnit_tensor {B : Type*} [CommRing B] [Algebra ℂ B]
    (t : TorusCoordinateRing r) (b : B)
    (ht : IsUnit t) (hb : IsUnit b) :
    IsUnit (t ⊗ₜ[ℂ] b) := by
  obtain ⟨t', ht'⟩ := isUnit_iff_exists_inv.mp ht
  obtain ⟨b', hb'⟩ := isUnit_iff_exists_inv.mp hb
  apply isUnit_iff_exists_inv.mpr
  refine ⟨t' ⊗ₜ[ℂ] b', ?_⟩
  simp [Algebra.TensorProduct.tmul_mul_tmul,
    ht', hb', Algebra.TensorProduct.one_def]

theorem left_restricted_coaction_fraction_isUnit
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
    IsUnit (overlapTensorRestrictionLeft (r := r) A hA hNonempty i j
      (standardOpenCoaction μ A hA hNonempty hCompact i
        (coordinateFraction A hA hNonempty i j))) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
    awayComplexAlgebra A hA hNonempty (coordinateClass A i)
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i * coordinateClass A j)) :=
    awayComplexAlgebra A hA hNonempty
      (coordinateClass A i * coordinateClass A j)
  rw [left_restricted_coaction_fraction μ A hA hNonempty hCompact i j j]
  exact isUnit_tensor _ _
    (laurentMonomial_isUnit (μ j - μ i))
    (left_overlap_coordinate_isUnit A hA hNonempty i j)

end
end QuaternionicSymmetry.ComplexProjectiveActualConeRestrictedCoactionUnits
