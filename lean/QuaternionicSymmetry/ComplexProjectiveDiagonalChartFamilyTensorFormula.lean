import QuaternionicSymmetry.ComplexProjectiveDiagonalChartProductTensorFormula
import QuaternionicSymmetry.ComplexProjectiveDiagonalChartProductScheme

/-! The product comparison evaluated on a base-changed chart polynomial. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalChartFamilyTensorFormula

open ComplexProjectiveTopology
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveDiagonalChartIdealDescent
open ComplexProjectiveDiagonalChartTensorBaseChange
open ComplexProjectiveDiagonalChartTensorQuotient
open ComplexProjectiveDiagonalChartProductRing
open ComplexProjectiveDiagonalChartProductScheme
open ComplexProjectiveDiagonalChartProductTensorFormula
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

theorem chartFamilyProductRingEquiv_baseChanged
    (A : Set (Space d)) (i : Fin (d + 1))
    (t : TorusCoordinateRing r) (p : MvPolynomial (Fin d) ℂ) :
    chartFamilyProductRingEquiv (r := r) A i
      (Ideal.Quotient.mk (extendedChartIdeal (r := r) A i)
        (t • MvPolynomial.map (algebraMap ℂ (TorusCoordinateRing r)) p)) =
      t ⊗ₜ[ℂ] Ideal.Quotient.mk (chartVanishingIdeal A i) p := by
  let q := Ideal.Quotient.mk (tensorExtendedChartIdeal (r := r) A i)
    (t ⊗ₜ[ℂ] p)
  have hq : chartTensorQuotientEquiv (r := r) A i q =
      Ideal.Quotient.mk (extendedChartIdeal (r := r) A i)
        (t • MvPolynomial.map (algebraMap ℂ (TorusCoordinateRing r)) p) := by
    simp [q, chartTensorQuotientEquiv, chartTensorEquiv]
  rw [← hq]
  have hs : (chartTensorQuotientEquiv (r := r) A i).symm.toRingEquiv
      ((chartTensorQuotientEquiv (r := r) A i) q) = q := by
    exact (chartTensorQuotientEquiv (r := r) A i).symm_apply_apply q
  simp only [chartFamilyProductRingEquiv, RingEquiv.trans_apply, hs]
  exact chartTensorQuotientProductEquiv_mk_tmul A i t p

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalChartFamilyTensorFormula
