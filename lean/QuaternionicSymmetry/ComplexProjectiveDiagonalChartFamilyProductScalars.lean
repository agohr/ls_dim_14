import QuaternionicSymmetry.ComplexProjectiveDiagonalChartFamilyTensorFormula

/-! Scalar values under the literal chart-family/product tensor equivalence. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalChartFamilyProductScalars

open ComplexProjectiveTopology
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveDiagonalChartIdealDescent
open ComplexProjectiveDiagonalChartProductScheme
open ComplexProjectiveDiagonalChartFamilyTensorFormula
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

theorem chartFamilyProductRingEquiv_C
    (A : Set (Space d)) (i : Fin (d + 1)) (c : ℂ) :
    chartFamilyProductRingEquiv (r := r) A i
      (Ideal.Quotient.mk (extendedChartIdeal (r := r) A i)
        (MvPolynomial.C (algebraMap ℂ (TorusCoordinateRing r) c))) =
      (1 : TorusCoordinateRing r) ⊗ₜ[ℂ]
        Ideal.Quotient.mk (chartVanishingIdeal A i) (MvPolynomial.C c) := by
  simpa using chartFamilyProductRingEquiv_baseChanged (r := r) A i 1 (MvPolynomial.C c)

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalChartFamilyProductScalars
