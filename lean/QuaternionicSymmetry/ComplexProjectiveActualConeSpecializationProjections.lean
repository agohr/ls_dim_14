import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenSpecializationTensor

/-! The actual standard-open torus specialization has the expected exact
formulas on both tensor-product projection homomorphisms. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeSpecializationProjections

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeStandardOpenCounit
open ComplexProjectiveActualConeStandardOpenSpecializationTensor
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

theorem specializeStandardOpen_left
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1))
    (z : ComplexTorus r) (t : TorusCoordinateRing r) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    specializeStandardOpen (r := r) A hA hNonempty i z
      (t ⊗ₜ[ℂ] (1 : HomogeneousLocalization.Away
        (quotientPiece A) (coordinateClass A i))) =
    algebraMap ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) (evalTorus z t) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  rw [specializeStandardOpen_tmul]
  exact mul_one _

theorem specializeStandardOpen_right
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1))
    (z : ComplexTorus r)
    (x : HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    specializeStandardOpen (r := r) A hA hNonempty i z
      ((1 : TorusCoordinateRing r) ⊗ₜ[ℂ] x) = x := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  rw [specializeStandardOpen_tmul]
  simp

end
end QuaternionicSymmetry.ComplexProjectiveActualConeSpecializationProjections
