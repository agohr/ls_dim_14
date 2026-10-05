import QuaternionicSymmetry.H2WitnessThirteen
import QuaternionicSymmetry.ConditionalH2Bounds

/-! Conditional numerical assembly of the complete dimension-thirteen
finite H2 certificate. The linear functional is abstract: the index identity,
positive volume, six orbital signs, and one restricted-square sign remain
explicit premises. -/

namespace QuaternionicSymmetry.ThirteenLinearAssembly

open MvPolynomial
open scoped BigOperators
open DimensionThirteenFourteenDensity H2WitnessThirteen

noncomputable section

abbrev P := DimensionThirteenFourteenDensity.P

/-- Six positive-coefficient orbital groups and the one Hodge square,
each with its full `u` power. -/
def generators13 : Fin 7 → P := ![
  u ^ 12 * embed w1,
  u ^ 11 * embed w2,
  u ^ 10 * embed w3,
  u ^ 9 * embed w4,
  u ^ 8 * embed w5,
  u ^ 7 * embed w6,
  factor ^ 2 * u ^ 7]

def coefficients13 : Fin 7 → ℚ := ![1, 1, 1, 1, 1, 1, 18]

theorem coefficients13_pos (i : Fin 7) : 0 < coefficients13 i := by
  fin_cases i <;> norm_num [coefficients13]

/-- The generators are the exact, independently reconstructed polynomial
terms, rather than an abstract nonnegative remainder. -/
theorem density13_generators :
    density13 = C 392 * u ^ 13 +
      ∑ i, C (coefficients13 i) * generators13 i := by
  rw [density13_witness]
  simp [H2WitnessThirteen.witness, H2WitnessThirteen.orbitalSum,
    generators13, coefficients13, Fin.sum_univ_succ]
  ring

theorem linear_density13 (L : P →ₗ[ℚ] ℝ) :
    L density13 = (392 : ℝ) * L (u ^ 13) +
      ∑ i, (coefficients13 i : ℝ) * L (generators13 i) := by
  rw [density13_generators]
  simp only [map_add, map_sum, ← smul_eq_C_mul, map_smul, Rat.smul_def]
  norm_num

theorem bound13 {d : ℕ} (L : P →ₗ[ℚ] ℝ)
    (hindex : (d : ℝ) = (QuaternionicSymmetry.delta 13 : ℝ) + L density13)
    (hU : 0 < L (u ^ 13))
    (hgenerators : ∀ i, 0 ≤ L (generators13 i)) : 15 ≤ d := by
  rw [linear_density13] at hindex
  apply ConditionalH2Bounds.bound13 (R :=
    ∑ i, (coefficients13 i : ℝ) * L (generators13 i))
    (by simpa only [add_assoc] using hindex) hU
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (by exact_mod_cast coefficients13_pos i |>.le)
    (hgenerators i)

theorem no_small_symmetry13 {d : ℕ} (L : P →ₗ[ℚ] ℝ)
    (hindex : (d : ℝ) = (QuaternionicSymmetry.delta 13 : ℝ) + L density13)
    (hU : 0 < L (u ^ 13))
    (hgenerators : ∀ i, 0 ≤ L (generators13 i))
    (hsmall : d ≤ 3) : False := by
  have h := bound13 L hindex hU hgenerators
  omega

end
end QuaternionicSymmetry.ThirteenLinearAssembly
