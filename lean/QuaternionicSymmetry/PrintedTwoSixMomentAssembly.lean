import QuaternionicSymmetry.QuaternionicFiveSixPointwise

/-! Full-u linear moment decompositions in quaternionic dimensions five
and six, with exact printed rational coefficients. -/
namespace QuaternionicSymmetry.PrintedTwoSixMomentAssembly
open MvPolynomial DimensionElevenTwelveDensity
  ElevenTwelveProjectionCertificates ReconstructionExamples
  QuaternionicFiveSixPointwise
open scoped BigOperators
noncomputable section

abbrev P := DimensionElevenTwelveDensity.P

def coefficients5 : Fin 3 → ℚ := ![268/45, 1/15, 104/15]
def coefficients6 : Fin 3 → ℚ := ![416/45, 2/15, 56/3]

theorem coefficients5_nonneg (i : Fin 3) : 0 ≤ coefficients5 i := by
  fin_cases i <;> norm_num [coefficients5]
theorem coefficients6_nonneg (i : Fin 3) : 0 ≤ coefficients6 i := by
  fin_cases i <;> norm_num [coefficients6]

theorem density5_generators : k5 = C 72 * u ^ 5 +
    ∑ i, C (coefficients5 i) * generators5 i := by
  rw [dimension_five_projection]
  simp [Fin.sum_univ_succ, coefficients5, generators5]
  ring

theorem density6_generators : k6 = C 96 * u ^ 6 +
    ∑ i, C (coefficients6 i) * generators6 i := by
  rw [dimension_six_projection]
  simp [Fin.sum_univ_succ, coefficients6, generators6]
  ring

theorem linear_density5 (L : P →ₗ[ℚ] ℝ) :
    L k5 = (72:ℝ) * L (u^5) +
      ∑ i, (coefficients5 i : ℝ) * L (generators5 i) := by
  rw [density5_generators]
  simp only [map_add, map_sum, ← smul_eq_C_mul, map_smul, Rat.smul_def]
  norm_num

theorem linear_density6 (L : P →ₗ[ℚ] ℝ) :
    L k6 = (96:ℝ) * L (u^6) +
      ∑ i, (coefficients6 i : ℝ) * L (generators6 i) := by
  rw [density6_generators]
  simp only [map_add, map_sum, ← smul_eq_C_mul, map_smul, Rat.smul_def]
  norm_num

end
end QuaternionicSymmetry.PrintedTwoSixMomentAssembly
