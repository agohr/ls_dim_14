import QuaternionicSymmetry.ComplexProjectiveActualConeChartNormalization

/-! A homogeneous cone polynomial vanishing after dehomogenization on the
actual affine chart becomes a cone equation after multiplying by the chosen
homogeneous coordinate. This is the exact saturation step for injectivity. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeChartSaturation

open ComplexProjectiveTopology
open ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveActualConeDehomogenization
open ComplexProjectiveActualConeChartNormalization
noncomputable section

variable {d : ℕ}

theorem chosen_times_mem_vanishingIdeal (A : Set (Space d))
    (i : Fin (d + 1)) (n : ℕ)
    (p : MvPolynomial (Fin (d + 1)) ℂ)
    (hp : p.IsHomogeneous n)
    (hchart : dehomogenize i p ∈ chartVanishingIdeal A i) :
    MvPolynomial.X i * p ∈ vanishingIdeal A := by
  rw [mem_vanishingIdeal_iff]
  intro v hv
  by_cases hvi : v i = 0
  · simp [hvi]
  have hv0 : v ≠ 0 := by
    intro hz
    simp [hz] at hvi
  have hpoint : Projectivization.mk ℂ v hv0 ∈ A := by
    rcases hv with hzero | ⟨hne, hmem⟩
    · exact (hv0 hzero).elim
    · exact hmem
  have hw : normalizedCoordinates i v ∈
      ComplexProjectiveDiagonalChartLocus.chartLocus A i :=
    normalizedCoordinates_mem_chartLocus A i v hv0 hvi hpoint
  have hz := (mem_chartVanishingIdeal_iff A i (dehomogenize i p)).mp
    hchart (normalizedCoordinates i v) hw
  rw [eval_dehomogenize,
    homogeneousVector_normalizedCoordinates i v hvi,
    homogeneous_eval_smul p n hp] at hz
  have hpv : MvPolynomial.eval v p = 0 := by
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ (inv_ne_zero hvi))
  simp [hpv]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeChartSaturation
