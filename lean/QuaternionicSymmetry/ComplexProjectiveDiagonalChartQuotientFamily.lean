import QuaternionicSymmetry.ComplexProjectiveDiagonalChartIdealDescent
import QuaternionicSymmetry.ComplexProjectiveDiagonalAffineChartComorphism
import QuaternionicSymmetry.ComplexProjectiveTorusPreservation

/-! A single regular Laurent-parameter family descends to the actual
standard affine-chart coordinate quotient. This is a genuine ring map of
chart coordinate algebras, not a list of pointwise automorphisms. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalChartQuotientFamily

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalAffineChartComorphism
open ComplexProjectiveDiagonalChartLocus
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveDiagonalChartIdealDescent
open ComplexProjectiveTorusPreservation
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

theorem chartActionComorphism_mem_extendedChartIdeal
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1))
    {p : MvPolynomial (Fin d) ℂ}
    (hp : p ∈ chartVanishingIdeal A i) :
    chartActionComorphism μ i p ∈ extendedChartIdeal (r := r) A i := by
  rw [← chartFamilyZeroIdeal_eq_extendedChartIdeal]
  rw [mem_chartFamilyZeroIdeal_iff]
  intro z w hw
  rw [eval_chartActionComorphism]
  exact (mem_chartVanishingIdeal_iff A i p).mp hp _
    (chartDiagonal_maps_chartLocus μ z A
      (mapsTo_of_compact μ A hA hCompact z) i hw)

def chartQuotientFamilyHom
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) :
    (MvPolynomial (Fin d) ℂ ⧸ chartVanishingIdeal A i) →+*
      (MvPolynomial (Fin d) (TorusCoordinateRing r) ⧸
        extendedChartIdeal (r := r) A i) :=
  Ideal.Quotient.lift (chartVanishingIdeal A i)
    ((Ideal.Quotient.mk (extendedChartIdeal (r := r) A i)).comp
      (chartActionComorphism μ i).toRingHom)
    (by
      intro p hp
      change (Ideal.Quotient.mk (extendedChartIdeal (r := r) A i))
        (chartActionComorphism μ i p) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (chartActionComorphism_mem_extendedChartIdeal μ A hA hCompact i hp))

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalChartQuotientFamily
