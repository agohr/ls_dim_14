import Mathlib.NumberTheory.Bernoulli
import Mathlib.Tactic

/-!
# The finite logarithmic `A-hat` calculation

This is the algebraic bridge between the root formula in Chapter 9 and the
coefficients used by the rational certificates.  It deliberately stops before
any curvature, index, or positivity assertion.

For a sequence `z`, `splitPower n u z b` is the substituted power sum
`s_b`: it is `n` in degree zero and
`(-1)^b z_b / 2 - u^b` otherwise.  `rawB` is the homogeneous weight-`j`
term of the textbook's finite root formula.
-/

namespace QuaternionicSymmetry.LogAhat

open scoped BigOperators

/-- The coefficient of `x^(2j)` in `log ((x/2) / sinh (x/2))`. -/
def ell (j : ℕ) : ℚ :=
  -bernoulli (2 * j) / ((2 * j : ℚ) * ((2 * j).factorial : ℚ))

theorem ell_one : ell 1 = -1 / 24 := by
  norm_num [ell]

theorem ell_two : ell 2 = 1 / 2880 := by
  rw [ell, bernoulli_eq_bernoulli'_of_ne_one (by omega)]
  norm_num

theorem ell_three : ell 3 = -1 / 181440 := by
  have hfive : bernoulli' 5 = 0 :=
    bernoulli'_eq_zero_of_odd (by decide) (by omega)
  rw [ell, bernoulli_eq_bernoulli'_of_ne_one (by omega), bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose, hfive]

theorem ell_four : ell 4 = 1 / 9676800 := by
  have hfive : bernoulli' 5 = 0 :=
    bernoulli'_eq_zero_of_odd (by decide) (by omega)
  have hsix : bernoulli' 6 = 1 / 42 := by
    rw [bernoulli'_def]
    norm_num [Finset.sum_range_succ, Nat.choose, hfive]
  have hseven : bernoulli' 7 = 0 :=
    bernoulli'_eq_zero_of_odd (by decide) (by omega)
  rw [ell, bernoulli_eq_bernoulli'_of_ne_one (by omega), bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose, hfive, hsix, hseven]

variable {R : Type*} [Field R] [CharZero R]

/-- The power-sum substitution `s_0 = n` and
`s_b = (-1)^b z_b / 2 - u^b` for `b > 0`. -/
def splitPower (n : ℕ) (u : R) (z : ℕ → R) (b : ℕ) : R :=
  if b = 0 then n else (-1 : R) ^ b * z b / 2 - u ^ b

/-- The weight-`j` term of the logarithmic root formula after substituting
the corrected Weyl power sums. -/
def rawB (n : ℕ) (u : R) (z : ℕ → R) (j : ℕ) : R :=
  2 * ∑ b ∈ Finset.range (j + 1),
    (ell j : R) * (Nat.choose (2 * j) (2 * b) : R) * u ^ (j - b)
      * splitPower n u z b

/-- The first four displayed certificate coefficients, obtained from `rawB`. -/
def B1 (n : ℕ) (u z1 : R) : R := -((n : R) - 1) / 12 * u + z1 / 24
def B2 (n : ℕ) (u z1 z2 : R) : R :=
  ((n : R) - 7) / 1440 * u ^ 2 - u * z1 / 480 + z2 / 2880
def B3 (n : ℕ) (u z1 z2 z3 : R) : R :=
  -((n : R) - 31) / 90720 * u ^ 3 + u ^ 2 * z1 / 12096 - u * z2 / 12096 + z3 / 181440
def B4 (n : ℕ) (u z1 z2 z3 z4 : R) : R :=
  ((n : R) - 127) / 4838400 * u ^ 4 - u ^ 3 * z1 / 345600 + u ^ 2 * z2 / 138240
    - u * z3 / 345600 + z4 / 9676800
theorem rawB_one (n : ℕ) (u : R) (z : ℕ → R) :
    rawB n u z 1 = B1 n u (z 1) := by
  simp only [rawB]
  rw [ell_one]
  norm_num [Finset.sum_range_succ, Nat.choose, splitPower, B1]
  ring

theorem rawB_two (n : ℕ) (u : R) (z : ℕ → R) :
    rawB n u z 2 = B2 n u (z 1) (z 2) := by
  simp only [rawB]
  rw [ell_two]
  norm_num [Finset.sum_range_succ, Nat.choose, splitPower, B2]
  ring

theorem rawB_three (n : ℕ) (u : R) (z : ℕ → R) :
    rawB n u z 3 = B3 n u (z 1) (z 2) (z 3) := by
  simp only [rawB]
  rw [ell_three]
  norm_num [Finset.sum_range_succ, Nat.choose, splitPower, B3]
  ring

theorem rawB_four (n : ℕ) (u : R) (z : ℕ → R) :
    rawB n u z 4 = B4 n u (z 1) (z 2) (z 3) (z 4) := by
  simp only [rawB]
  rw [ell_four]
  norm_num [Finset.sum_range_succ, Nat.choose, splitPower, B4]
  ring

/-- Coefficients through weight four of `exp (B1*t + B2*t^2 + ...)`. -/
def A0 : R := 1
def A1 (b1 : R) : R := b1
def A2 (b1 b2 : R) : R := b2 + b1 ^ 2 / 2
def A3 (b1 b2 b3 : R) : R := b3 + b1 * b2 + b1 ^ 3 / 6
def A4 (b1 b2 b3 b4 : R) : R :=
  b4 + b1 * b3 + b2 ^ 2 / 2 + b1 ^ 2 * b2 / 2 + b1 ^ 4 / 24

omit [CharZero R] in
theorem A1_recurrence (b1 : R) : A1 b1 = b1 * A0 := by
  simp [A1, A0]

theorem A2_recurrence (b1 b2 : R) :
    2 * A2 b1 b2 = b1 * A1 b1 + 2 * b2 * A0 := by
  simp only [A2, A1, A0]
  ring

theorem A3_recurrence (b1 b2 b3 : R) :
    3 * A3 b1 b2 b3 = b1 * A2 b1 b2 + 2 * b2 * A1 b1 + 3 * b3 * A0 := by
  simp only [A3, A2, A1, A0]
  ring

theorem A4_recurrence (b1 b2 b3 b4 : R) :
    4 * A4 b1 b2 b3 b4 = b1 * A3 b1 b2 b3 + 2 * b2 * A2 b1 b2
      + 3 * b3 * A1 b1 + 4 * b4 * A0 := by
  simp only [A4, A3, A2, A1, A0]
  ring

end QuaternionicSymmetry.LogAhat
