import QuaternionicSymmetry.ComplexProjectiveDiagonalChartQuotientFamily

/-! The actual quotient Laurent family preserves the canonical complex
scalars of the chart coordinate algebra. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalChartQuotientFamilyScalars

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveDiagonalChartIdealDescent
open ComplexProjectiveDiagonalChartQuotientFamily
open ComplexProjectiveDiagonalAffineChartComorphism
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

theorem chartQuotientFamilyHom_C
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) (c : ℂ) :
    chartQuotientFamilyHom μ A hA hCompact i
      (Ideal.Quotient.mk (chartVanishingIdeal A i) (MvPolynomial.C c)) =
    Ideal.Quotient.mk (extendedChartIdeal (r := r) A i)
      (MvPolynomial.C (algebraMap ℂ (TorusCoordinateRing r) c)) := by
  simp [chartQuotientFamilyHom, chartActionComorphism]

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalChartQuotientFamilyScalars
