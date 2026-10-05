import QuaternionicSymmetry.ComplexProjectiveActualConeOverlapLocalization
import QuaternionicSymmetry.ComplexProjectiveDiagonalLaurentTransition

/-! On the literal torus × pairwise-Proj-overlap ring, the regular
coordinate/character expressions obey the projective transition cocycle. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeTensorOverlapCocycle

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeOverlapFractions
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalLaurentTransition
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

theorem tensor_overlap_coordinate_cocycle
    (μ : Fin (d + 1) → Fin r → ℤ)
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i j k : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) :=
      awayComplexAlgebra A hA hNonempty
        (coordinateClass A i * coordinateClass A j)
    (laurentMonomial (μ k - μ i) ⊗ₜ[ℂ]
        HomogeneousLocalization.awayMap (quotientPiece A)
          (coordinateClass_mem_degreeOne A j) rfl
          (coordinateFraction A hA hNonempty i k)) *
      (laurentMonomial (μ i - μ j) ⊗ₜ[ℂ]
        HomogeneousLocalization.awayMap (quotientPiece A)
          (coordinateClass_mem_degreeOne A i) (by ring)
          (coordinateFraction A hA hNonempty j i)) =
      (laurentMonomial (μ k - μ j) ⊗ₜ[ℂ]
        HomogeneousLocalization.awayMap (quotientPiece A)
          (coordinateClass_mem_degreeOne A i) (by ring)
          (coordinateFraction A hA hNonempty j k)) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) :=
    awayComplexAlgebra A hA hNonempty
      (coordinateClass A i * coordinateClass A j)
  rw [Algebra.TensorProduct.tmul_mul_tmul,
    laurentRatio_cocycle μ i j k,
    overlap_coordinate_transition A hA hNonempty i j k]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeTensorOverlapCocycle
