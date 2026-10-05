import QuaternionicSymmetry.Arithmetic

/-! Conditional numerical assembly for the printed n=11,12 certificates.

The twelve inputs are, in order, the six projection moments, five scalar
orbital moments, and the fifth Gaussian coefficient integral in Chapter 7.
Their signs and the index equality are explicit arguments. This file proves
only the finite sign arithmetic, not the geometric interpretations.
-/

namespace QuaternionicSymmetry.ConditionalC12Bounds

open scoped BigOperators

def coefficients11 : Fin 12 → ℚ := ![
  2482652/51975, 3094720/6237, 214814/93555,
  164360/2673, 10048/891, 922051/93555,
  1008851484437/2142693, 151204920425/714231,
  10770035384/714231, 51654964/6428079,
  252882056/1530495, 8192]

def coefficients12 : Fin 12 → ℚ := ![
  3050776/51975, 12506936/17325, 1445966/467775,
  472784/155925, 152711/18711, 1771432/18711,
  2298362246/9933, 194400388184/148995,
  7327263802/9933, 178334456/148995,
  4485216/3311, 16384]

theorem coefficients11_nonneg (i : Fin 12) : 0 ≤ coefficients11 i := by
  fin_cases i <;> norm_num [coefficients11]

theorem coefficients12_nonneg (i : Fin 12) : 0 ≤ coefficients12 i := by
  fin_cases i <;> norm_num [coefficients12]

def remainder11 (v : Fin 12 → ℝ) : ℝ :=
  ∑ i, (coefficients11 i : ℝ) * v i

def remainder12 (v : Fin 12 → ℝ) : ℝ :=
  ∑ i, (coefficients12 i : ℝ) * v i

theorem remainder11_nonneg (v : Fin 12 → ℝ) (hv : ∀ i, 0 ≤ v i) :
    0 ≤ remainder11 v := by
  unfold remainder11
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (by exact_mod_cast coefficients11_nonneg i) (hv i)

theorem remainder12_nonneg (v : Fin 12 → ℝ) (hv : ∀ i, 0 ≤ v i) :
    0 ≤ remainder12 v := by
  unfold remainder12
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (by exact_mod_cast coefficients12_nonneg i) (hv i)

/-- The n=11 printed identity, if interpreted as a numerical index equality
with all twelve named generator integrals nonnegative, forces `d ≥ 13`. -/
theorem bound11 {d : ℕ} {U : ℝ} (v : Fin 12 → ℝ)
    (hindex : (d : ℝ) = (delta 11 : ℝ) +
      (scalarCoefficient 11 : ℝ) * U + remainder11 v)
    (hU : 0 < U) (hv : ∀ i, 0 ≤ v i) : 13 ≤ d := by
  have h := lower_bound_of_printed_certificate hindex (by norm_num) hU
    (remainder11_nonneg v hv)
  norm_num [delta] at h ⊢
  exact h

/-- The analogous n=12 consequence is `d ≥ 16`. -/
theorem bound12 {d : ℕ} {U : ℝ} (v : Fin 12 → ℝ)
    (hindex : (d : ℝ) = (delta 12 : ℝ) +
      (scalarCoefficient 12 : ℝ) * U + remainder12 v)
    (hU : 0 < U) (hv : ∀ i, 0 ≤ v i) : 16 ≤ d := by
  have h := lower_bound_of_printed_certificate hindex (by norm_num) hU
    (remainder12_nonneg v hv)
  norm_num [delta] at h ⊢
  exact h

theorem no_small_symmetry11 {d : ℕ} {U : ℝ} (v : Fin 12 → ℝ)
    (hindex : (d : ℝ) = (delta 11 : ℝ) +
      (scalarCoefficient 11 : ℝ) * U + remainder11 v)
    (hU : 0 < U) (hv : ∀ i, 0 ≤ v i) (hsmall : d ≤ 3) : False := by
  have h := bound11 v hindex hU hv
  omega

theorem no_small_symmetry12 {d : ℕ} {U : ℝ} (v : Fin 12 → ℝ)
    (hindex : (d : ℝ) = (delta 12 : ℝ) +
      (scalarCoefficient 12 : ℝ) * U + remainder12 v)
    (hU : 0 < U) (hv : ∀ i, 0 ≤ v i) (hsmall : d ≤ 3) : False := by
  have h := bound12 v hindex hU hv
  omega

end QuaternionicSymmetry.ConditionalC12Bounds
