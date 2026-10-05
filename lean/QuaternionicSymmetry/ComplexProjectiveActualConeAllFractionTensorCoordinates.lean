import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenTensorCoordinates
import QuaternionicSymmetry.ComplexProjectiveActualConeOverlapFractions

/-! The literal tensor-coordinate formula for every projective coordinate
fraction, including the denominator coordinate itself. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeAllFractionTensorCoordinates

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeOverlapFractions
open ComplexProjectiveActualConeStandardOpenCoaction
open ComplexProjectiveActualConeStandardOpenTensorCoordinates
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

theorem coordinateFraction_self
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    coordinateFraction A hA hNonempty i i = 1 := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  apply HomogeneousLocalization.val_injective
  simp [coordinateFraction, HomogeneousLocalization.Away.val_mk]

theorem standardOpenCoaction_fraction_tensor
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i k : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
      awayComplexAlgebra A hA hNonempty (coordinateClass A i)
    standardOpenCoaction μ A hA hNonempty hCompact i
      (coordinateFraction A hA hNonempty i k) =
      laurentMonomial (μ k - μ i) ⊗ₜ[ℂ]
        coordinateFraction A hA hNonempty i k := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
    awayComplexAlgebra A hA hNonempty (coordinateClass A i)
  by_cases h : k = i
  · subst k
    rw [coordinateFraction_self A hA hNonempty i]
    simp [laurentMonomial, Algebra.TensorProduct.one_def,
      AddMonoidAlgebra.one_def]
  · obtain ⟨n, hn⟩ := Fin.exists_succAbove_eq_iff.mpr h
    subst k
    exact standardOpenCoaction_coordinate_tensor μ A hA hNonempty hCompact i n

end
end QuaternionicSymmetry.ComplexProjectiveActualConeAllFractionTensorCoordinates
