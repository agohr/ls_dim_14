import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenCoactionCoordinates
import QuaternionicSymmetry.ComplexProjectiveDiagonalChartFamilyTensorFormula

/-! Literal tensor-coordinate formula for the standard-open torus coaction. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenTensorCoordinates

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveDiagonalChartIdealDescent
open ComplexProjectiveDiagonalChartProductScheme
open ComplexProjectiveDiagonalChartFamilyTensorFormula
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeStandardOpenCoordinates
open ComplexProjectiveActualConeStandardOpenAlgEquiv
open ComplexProjectiveActualConeBaseChangedChartRing
open ComplexProjectiveActualConeStandardOpenCoaction
open ComplexProjectiveActualConeStandardOpenCoactionCoordinates
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

theorem standardOpenCoaction_coordinate_tensor
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) (k : Fin d) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
      awayComplexAlgebra A hA hNonempty (coordinateClass A i)
    standardOpenCoaction μ A hA hNonempty hCompact i
      (HomogeneousLocalization.Away.mk (quotientPiece A)
        (coordinateClass_mem_degreeOne A i) 1
        (coordinateClass A (i.succAbove k))
        (coordinateClass_mem_degreeOne A (i.succAbove k))) =
      laurentMonomial (μ (i.succAbove k) - μ i) ⊗ₜ[ℂ]
        (HomogeneousLocalization.Away.mk (quotientPiece A)
          (coordinateClass_mem_degreeOne A i) 1
          (coordinateClass A (i.succAbove k))
          (coordinateClass_mem_degreeOne A (i.succAbove k))) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
    awayComplexAlgebra A hA hNonempty (coordinateClass A i)
  apply (baseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i).injective
  rw [standardOpenCoaction_coordinate]
  change (Ideal.Quotient.mk (extendedChartIdeal (r := r) A i)
      (regularChartCoordinate μ i k)) =
    (chartFamilyProductRingEquiv (r := r) A i).symm
      ((baseChangedStandardOpenEquiv (r := r) A hA hNonempty i)
        (laurentMonomial (μ (i.succAbove k) - μ i) ⊗ₜ[ℂ]
          HomogeneousLocalization.Away.mk (quotientPiece A)
            (coordinateClass_mem_degreeOne A i) 1
            (coordinateClass A (i.succAbove k))
            (coordinateClass_mem_degreeOne A (i.succAbove k))))
  simp only [baseChangedStandardOpenEquiv,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  simp [standardOpenAlgEquiv,
    ComplexProjectiveActualConeStandardOpenEquiv.standardOpenEquiv_apply,
    standardOpenToChart_coordinate]
  apply (chartFamilyProductRingEquiv (r := r) A i).injective
  simp only [RingEquiv.apply_symm_apply]
  simpa [regularChartCoordinate, Algebra.smul_def] using
    (chartFamilyProductRingEquiv_baseChanged (r := r) A i
      (laurentMonomial (μ (i.succAbove k) - μ i)) (MvPolynomial.X k))

end
end QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenTensorCoordinates
