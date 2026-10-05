import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleStandardOpenRing
import QuaternionicSymmetry.ComplexProjectiveChartTensorGenericFormula

/-! Exact pure-tensor value of the double-torus quotient comparison on
representatives of the actual homogeneous standard-open chart ring. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeDoubleStandardOpenTensorFormula

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveDiagonalDoubleChartBaseChange
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeStandardOpenEquiv
open ComplexProjectiveActualConeStandardOpenAlgEquiv
open ComplexProjectiveActualConeDoubleStandardOpenRing
open ComplexProjectiveChartTensorBaseChangeGeneric
open ComplexProjectiveChartTensorGenericFormula
open ComplexTorusLaurentComultiplication
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

set_option maxRecDepth 2048 in
theorem doubleBaseChangedStandardOpenFamilyEquiv_tmul_rep
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1))
    (s : DoubleTorusCoordinateRing r) (p : MvPolynomial (Fin d) ℂ) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    doubleBaseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i
      (s ⊗ₜ[ℂ] (standardOpenEquiv A hA hNonempty i).symm
        (Ideal.Quotient.mk (chartVanishingIdeal A i) p)) =
    Ideal.Quotient.mk (doubleExtendedChartIdeal (r := r) A i)
      (s • MvPolynomial.map (algebraMap ℂ (DoubleTorusCoordinateRing r)) p) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  apply (chartFamilyProductRingEquiv (DoubleTorusCoordinateRing r)
    (chartVanishingIdeal A i)).injective
  change _ = chartFamilyProductRingEquiv (DoubleTorusCoordinateRing r)
    (chartVanishingIdeal A i)
      (Ideal.Quotient.mk
        (polynomialExtendedIdeal (DoubleTorusCoordinateRing r)
          (chartVanishingIdeal A i))
        (s • MvPolynomial.map (algebraMap ℂ (DoubleTorusCoordinateRing r)) p))
  rw [chartFamilyProductRingEquiv_baseChanged]
  simp only [doubleBaseChangedStandardOpenFamilyEquiv, RingEquiv.trans_apply]
  have hcancel := (chartFamilyProductRingEquiv (DoubleTorusCoordinateRing r)
    (chartVanishingIdeal A i)).apply_symm_apply
      ((doubleBaseChangedStandardOpenEquiv (r := r) A hA hNonempty i).toRingEquiv
        (s ⊗ₜ[ℂ] (standardOpenEquiv A hA hNonempty i).symm
          (Ideal.Quotient.mk (chartVanishingIdeal A i) p)))
  refine hcancel.trans ?_
  change doubleBaseChangedStandardOpenEquiv (r := r) A hA hNonempty i
      (s ⊗ₜ[ℂ] (standardOpenEquiv A hA hNonempty i).symm
        (Ideal.Quotient.mk (chartVanishingIdeal A i) p)) =
      s ⊗ₜ[ℂ] Ideal.Quotient.mk (chartVanishingIdeal A i) p
  simp [doubleBaseChangedStandardOpenEquiv, standardOpenAlgEquiv,
    Algebra.TensorProduct.congr_apply]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeDoubleStandardOpenTensorFormula
