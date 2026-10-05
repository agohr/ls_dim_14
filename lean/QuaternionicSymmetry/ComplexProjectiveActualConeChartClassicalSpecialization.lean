import QuaternionicSymmetry.ComplexProjectiveDiagonalChartFamilySpecialization
import QuaternionicSymmetry.ComplexProjectiveDiagonalChartQuotientFamily

/-! Evaluation of the actual regular affine-chart family at classical torus
and chart points agrees with the diagonal projective action in that chart. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeChartClassicalSpecialization

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction
open ComplexProjectiveDiagonalHolomorphic
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalChartLocus
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveDiagonalChartQuotientFamily
open ComplexProjectiveDiagonalChartFamilySpecialization
open ComplexProjectiveDiagonalAffineChartComorphism
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

def chartPointEval (A : Set (Space d)) (i : Fin (d + 1))
    (w : Fin d → ℂ) (hw : w ∈ chartLocus A i) :
    (MvPolynomial (Fin d) ℂ ⧸ chartVanishingIdeal A i) →+* ℂ :=
  Ideal.Quotient.lift (chartVanishingIdeal A i)
    (MvPolynomial.eval₂Hom (RingHom.id ℂ) w)
    (by
      intro p hp
      exact (mem_chartVanishingIdeal_iff A i p).mp hp w hw)

@[simp] theorem chartPointEval_mk (A : Set (Space d))
    (i : Fin (d + 1)) (w : Fin d → ℂ)
    (hw : w ∈ chartLocus A i) (p : MvPolynomial (Fin d) ℂ) :
    chartPointEval A i w hw
      (Ideal.Quotient.mk (chartVanishingIdeal A i) p) =
      MvPolynomial.eval w p := by
  simp [chartPointEval, MvPolynomial.eval_eq]

theorem chart_family_classical_specialization
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) (z : ComplexTorus r)
    (w : Fin d → ℂ) (hw : w ∈ chartLocus A i)
    (p : MvPolynomial (Fin d) ℂ) :
    chartPointEval A i w hw
      (specializeChartQuotient A i z
        (chartQuotientFamilyHom μ A hA hCompact i
          (Ideal.Quotient.mk (chartVanishingIdeal A i) p))) =
      MvPolynomial.eval (chartDiagonal μ z i w) p := by
  rw [chartQuotientFamilyHom, Ideal.Quotient.lift_mk]
  change chartPointEval A i w hw
    (specializeChartQuotient A i z
      (Ideal.Quotient.mk _ (chartActionComorphism μ i p))) = _
  rw [specializeChartQuotient_mk, chartPointEval_mk]
  rw [← MvPolynomial.eval₂_eq_eval_map]
  exact eval_chartActionComorphism μ i z w p

end
end QuaternionicSymmetry.ComplexProjectiveActualConeChartClassicalSpecialization
