import QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleChartTwistPolynomial

/-! Both successive torus substitutions preserve the actual projective
chart ideal after literal two-parameter base change. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleChartTwistIdeal

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveDiagonalChartIdealDescent
open ComplexProjectiveDiagonalChartQuotientFamily
open ComplexProjectiveDiagonalAffineChartComorphism
open ComplexProjectiveDiagonalDoubleChartBaseChange
open ComplexProjectiveDiagonalDoubleChartQuotientMaps
open ComplexProjectiveDiagonalDoubleChartTwistPolynomial
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

theorem firstChartTwist_map_extendedChartIdeal_le
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) :
    (extendedChartIdeal (r := r) A i).map (firstChartTwist μ i) ≤
      doubleExtendedChartIdeal (r := r) A i := by
  have hpres : (chartVanishingIdeal A i).map (chartActionComorphism μ i).toRingHom ≤
      extendedChartIdeal (r := r) A i :=
    Ideal.map_le_iff_le_comap.mpr (by
      intro p hp
      exact chartActionComorphism_mem_extendedChartIdeal μ A hA hCompact i hp)
  calc
    (extendedChartIdeal (r := r) A i).map (firstChartTwist μ i) =
        ((chartVanishingIdeal A i).map (chartActionComorphism μ i).toRingHom).map
          (firstChartPolynomial (r := r)) := by
      rw [extendedChartIdeal, Ideal.map_map,
        firstChartTwist_comp_baseChange, ← Ideal.map_map]
    _ ≤ (extendedChartIdeal (r := r) A i).map (firstChartPolynomial (r := r)) :=
      Ideal.map_mono hpres
    _ = doubleExtendedChartIdeal (r := r) A i :=
      firstChartPolynomial_map_extendedChartIdeal A i

theorem secondChartTwist_map_extendedChartIdeal_le
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) :
    (extendedChartIdeal (r := r) A i).map (secondChartTwist μ i) ≤
      doubleExtendedChartIdeal (r := r) A i := by
  have hpres : (chartVanishingIdeal A i).map (chartActionComorphism μ i).toRingHom ≤
      extendedChartIdeal (r := r) A i :=
    Ideal.map_le_iff_le_comap.mpr (by
      intro p hp
      exact chartActionComorphism_mem_extendedChartIdeal μ A hA hCompact i hp)
  calc
    (extendedChartIdeal (r := r) A i).map (secondChartTwist μ i) =
        ((chartVanishingIdeal A i).map (chartActionComorphism μ i).toRingHom).map
          (secondChartPolynomial (r := r)) := by
      rw [extendedChartIdeal, Ideal.map_map,
        secondChartTwist_comp_baseChange, ← Ideal.map_map]
    _ ≤ (extendedChartIdeal (r := r) A i).map (secondChartPolynomial (r := r)) :=
      Ideal.map_mono hpres
    _ = doubleExtendedChartIdeal (r := r) A i :=
      secondChartPolynomial_map_extendedChartIdeal A i

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleChartTwistIdeal
