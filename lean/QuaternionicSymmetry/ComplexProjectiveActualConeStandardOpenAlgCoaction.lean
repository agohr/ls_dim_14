import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenCoactionScalars

/-! The checked actual homogeneous standard-open coaction is a morphism of
the canonical complex algebras, not only of abstract rings. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenAlgCoaction

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeStandardOpenCoaction
open ComplexProjectiveActualConeStandardOpenCoactionScalars
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

def standardOpenAlgCoaction
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i) →ₐ[ℂ]
      TorusCoordinateRing r ⊗[ℂ]
        HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  exact AlgHom.mk' (standardOpenCoaction μ A hA hNonempty hCompact i) (by
    intro c x
    simp only [Algebra.smul_def, map_mul]
    rw [standardOpenCoaction_scalar μ A hA hNonempty hCompact i c]
    rw [Algebra.TensorProduct.algebraMap_apply'])

@[simp] theorem standardOpenAlgCoaction_apply
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1))
    (x : HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    standardOpenAlgCoaction μ A hA hNonempty hCompact i x =
      standardOpenCoaction μ A hA hNonempty hCompact i x := rfl

end
end QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenAlgCoaction
