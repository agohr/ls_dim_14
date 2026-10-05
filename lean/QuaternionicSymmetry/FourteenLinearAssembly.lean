import QuaternionicSymmetry.H2WitnessFourteen
import QuaternionicSymmetry.ConditionalH2Bounds

/-! Conditional numerical assembly of the complete dimension-fourteen
finite H2 certificate. The linear functional is abstract: the index identity,
positive volume, six orbital signs, and one restricted-square sign remain
explicit premises. -/

namespace QuaternionicSymmetry.FourteenLinearAssembly

open MvPolynomial
open scoped BigOperators
open DimensionThirteenFourteenDensity H2WitnessFourteen

noncomputable section

abbrev P := DimensionThirteenFourteenDensity.P

/-- Six positive-coefficient orbital groups and the one Hodge square,
each with its full `u` power. -/
def generators14 : Fin 7 → P := ![
  u ^ 13 * embed w1,
  u ^ 12 * embed w2,
  u ^ 11 * embed w3,
  u ^ 10 * embed w4,
  u ^ 9 * embed w5,
  u ^ 8 * embed w6,
  factor ^ 2 * u ^ 8]

def coefficients14 : Fin 7 → ℚ := ![1, 1, 1, 1, 1, 1, 20]

theorem coefficients14_pos (i : Fin 7) : 0 < coefficients14 i := by
  fin_cases i <;> norm_num [coefficients14]

theorem density14_generators :
    density14 = C 448 * u ^ 14 +
      ∑ i, C (coefficients14 i) * generators14 i := by
  rw [density14_witness]
  simp [H2WitnessFourteen.witness, H2WitnessFourteen.orbitalSum,
    generators14, coefficients14, Fin.sum_univ_succ]
  ring

theorem linear_density14 (L : P →ₗ[ℚ] ℝ) :
    L density14 = (448 : ℝ) * L (u ^ 14) +
      ∑ i, (coefficients14 i : ℝ) * L (generators14 i) := by
  rw [density14_generators]
  simp only [map_add, map_sum, ← smul_eq_C_mul, map_smul, Rat.smul_def]
  norm_num

theorem bound14 {d : ℕ} (L : P →ₗ[ℚ] ℝ)
    (hindex : (d : ℝ) = (QuaternionicSymmetry.delta 14 : ℝ) + L density14)
    (hU : 0 < L (u ^ 14))
    (hgenerators : ∀ i, 0 ≤ L (generators14 i)) : 18 ≤ d := by
  rw [linear_density14] at hindex
  apply ConditionalH2Bounds.bound14 (R :=
    ∑ i, (coefficients14 i : ℝ) * L (generators14 i))
    (by simpa only [add_assoc] using hindex) hU
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (by exact_mod_cast coefficients14_pos i |>.le)
    (hgenerators i)

theorem no_small_symmetry14 {d : ℕ} (L : P →ₗ[ℚ] ℝ)
    (hindex : (d : ℝ) = (QuaternionicSymmetry.delta 14 : ℝ) + L density14)
    (hU : 0 < L (u ^ 14))
    (hgenerators : ∀ i, 0 ≤ L (generators14 i))
    (hsmall : d ≤ 3) : False := by
  have h := bound14 L hindex hU hgenerators
  omega

end
end QuaternionicSymmetry.FourteenLinearAssembly
