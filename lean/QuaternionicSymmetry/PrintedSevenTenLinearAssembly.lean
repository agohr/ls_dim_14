import QuaternionicSymmetry.QuaternionicSevenPointwise
import QuaternionicSymmetry.QuaternionicEightPointwise
import QuaternionicSymmetry.QuaternionicNinePointwise
import QuaternionicSymmetry.QuaternionicTenPointwise

/-! Exact finite generator decompositions of the printed dimension 7–10
certificates. Every nonscalar generator has an actual pointwise sign theorem. -/
namespace QuaternionicSymmetry.PrintedSevenTenLinearAssembly
open MvPolynomial DimensionElevenTwelveDensity PrintedCertificatesSevenTen
open QuaternionicSevenPointwise QuaternionicEightPointwise
  QuaternionicNinePointwise QuaternionicTenPointwise
open scoped BigOperators
noncomputable section

abbrev P := DimensionElevenTwelveDensity.P

def coefficients7 : Fin 6 → ℚ :=
  ![28080/1890, 668/1890, 100096/1890, 3/1890, 6528/1890, 4080/1890]
def coefficients8 : Fin 6 → ℚ :=
  ![96720/4725, 2710/4725, 485640/4725, 15/4725, 43320/4725, 29070/4725]
def coefficients9 : Fin 7 → ℚ :=
  ![180512/315, 14704/14175, 8752/45, 239/28350, 2992/405, 2090/81, 2048]
def coefficients10 : Fin 7 → ℚ :=
  ![182336/225, 21278/14175, 1495736/4725, 194/14175, 4048/4725, 23276/405, 4096]

theorem coefficients7_nonneg (i : Fin 6) : 0 ≤ coefficients7 i := by
  fin_cases i <;> norm_num [coefficients7]
theorem coefficients8_nonneg (i : Fin 6) : 0 ≤ coefficients8 i := by
  fin_cases i <;> norm_num [coefficients8]
theorem coefficients9_nonneg (i : Fin 7) : 0 ≤ coefficients9 i := by
  fin_cases i <;> norm_num [coefficients9]
theorem coefficients10_nonneg (i : Fin 7) : 0 ≤ coefficients10 i := by
  fin_cases i <;> norm_num [coefficients10]

theorem rhs7_generators : rhs7 = C 128 * u ^ 7 +
    ∑ i, C (coefficients7 i) * generators7 i := by
  simp [rhs7, Fin.sum_univ_succ, coefficients7, generators7]
  ring

theorem rhs8_generators : rhs8 = C 160 * u ^ 8 +
    ∑ i, C (coefficients8 i) * generators8 i := by
  simp [rhs8, Fin.sum_univ_succ, coefficients8, generators8]
  ring

theorem rhs9_generators : rhs9 = C 200 * u ^ 9 +
    ∑ i, C (coefficients9 i) * generators9 i := by
  simp [rhs9, Fin.sum_univ_succ, coefficients9, generators9]
  ring

theorem rhs10_generators : rhs10 = C 240 * u ^ 10 +
    ∑ i, C (coefficients10 i) * generators10 i := by
  simp [rhs10, Fin.sum_univ_succ, coefficients10, generators10]
  ring


theorem linear_rhs7 (L : P →ₗ[ℚ] ℝ) :
    L rhs7 = (128:ℝ) * L (u^7) +
      ∑ i, (coefficients7 i : ℝ) * L (generators7 i) := by
  rw [rhs7_generators]
  simp only [map_add, map_sum, ← smul_eq_C_mul, map_smul, Rat.smul_def]
  norm_num

theorem linear_rhs8 (L : P →ₗ[ℚ] ℝ) :
    L rhs8 = (160:ℝ) * L (u^8) +
      ∑ i, (coefficients8 i : ℝ) * L (generators8 i) := by
  rw [rhs8_generators]
  simp only [map_add, map_sum, ← smul_eq_C_mul, map_smul, Rat.smul_def]
  norm_num

theorem linear_rhs9 (L : P →ₗ[ℚ] ℝ) :
    L rhs9 = (200:ℝ) * L (u^9) +
      ∑ i, (coefficients9 i : ℝ) * L (generators9 i) := by
  rw [rhs9_generators]
  simp only [map_add, map_sum, ← smul_eq_C_mul, map_smul, Rat.smul_def]
  norm_num

theorem linear_rhs10 (L : P →ₗ[ℚ] ℝ) :
    L rhs10 = (240:ℝ) * L (u^10) +
      ∑ i, (coefficients10 i : ℝ) * L (generators10 i) := by
  rw [rhs10_generators]
  simp only [map_add, map_sum, ← smul_eq_C_mul, map_smul, Rat.smul_def]
  norm_num

end
end QuaternionicSymmetry.PrintedSevenTenLinearAssembly
