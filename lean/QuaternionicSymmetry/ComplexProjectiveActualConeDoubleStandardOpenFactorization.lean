import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleStandardOpenCoefficient

/-! Both literal two-parameter chart maps separate the incoming Laurent
coefficient from the geometric standard-open coordinate. This records the
ordered factors needed for the scheme product-action diagrams. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeDoubleStandardOpenFactorization

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalDoubleBaseChange
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeDoubleStandardOpenCoaction
open ComplexProjectiveActualConeDoubleStandardOpenCoefficient
open ComplexTorusLaurentComultiplication
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

theorem firstStandardOpenTwist_tmul
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
        firstStandardOpenTwist μ A hA hNonempty hCompact i (1 ⊗ₜ[ℂ] x) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  rw [← firstStandardOpenTwist_tmul_one μ A hA hNonempty hCompact i t,
    ← map_mul]
  simp

theorem secondStandardOpenTwist_tmul
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
        secondStandardOpenTwist μ A hA hNonempty hCompact i (1 ⊗ₜ[ℂ] x) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  rw [← secondStandardOpenTwist_tmul_one μ A hA hNonempty hCompact i t,
    ← map_mul]
  simp

end
end QuaternionicSymmetry.ComplexProjectiveActualConeDoubleStandardOpenFactorization
