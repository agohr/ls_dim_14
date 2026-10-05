import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleStandardOpenFactorization
import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenIteratedCoaction

/-! Exact two-parameter formulas for the actual standard-open ring: an
incoming Laurent coefficient occupies the untouched torus factor, while the
geometric coordinate is transformed by the genuine single coaction on the
other factor. No pointwise or surrogate algebraic-action predicate occurs. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenIteratedFormula

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalDoubleBaseChange
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeStandardOpenCoaction
open ComplexProjectiveActualConeDoubleStandardOpenCoaction
open ComplexProjectiveActualConeDoubleStandardOpenFactorization
open ComplexProjectiveActualConeStandardOpenParameterTensor
open ComplexProjectiveActualConeStandardOpenIteratedCoaction
open ComplexTorusLaurentComultiplication
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

theorem firstStandardOpenTwist_tmul_coaction
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) (t : TorusCoordinateRing r)
    (x : HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    firstStandardOpenTwist μ A hA hNonempty hCompact i (t ⊗ₜ[ℂ] x) =
      ((secondParameter t) ⊗ₜ[ℂ] 1) *
        firstParameterStandardOpen (r := r) A hA hNonempty i
          (standardOpenCoaction μ A hA hNonempty hCompact i x) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  rw [firstStandardOpenTwist_tmul,
    firstStandardOpenTwist_coaction_coordinate]

theorem secondStandardOpenTwist_tmul_coaction
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) (t : TorusCoordinateRing r)
    (x : HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    secondStandardOpenTwist μ A hA hNonempty hCompact i (t ⊗ₜ[ℂ] x) =
      ((firstParameter t) ⊗ₜ[ℂ] 1) *
        secondParameterStandardOpen (r := r) A hA hNonempty i
          (standardOpenCoaction μ A hA hNonempty hCompact i x) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  rw [secondStandardOpenTwist_tmul,
    secondStandardOpenTwist_coaction_coordinate]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenIteratedFormula
