import QuaternionicSymmetry.LogAhat

/-! The weight-five term of the universal A-hat root calculation in
Chapter 6. These are identities over fields of characteristic zero; they do
not identify a curvature form with a de Rham class or an index number. -/

namespace QuaternionicSymmetry.LogAhat

open scoped BigOperators

theorem ell_five : ell 5 = -1 / 479001600 := by
  have h5 : bernoulli' 5 = 0 :=
    bernoulli'_eq_zero_of_odd (by decide) (by omega)
  have h6 : bernoulli' 6 = 1 / 42 := by
    rw [bernoulli'_def]
    norm_num [Finset.sum_range_succ, Nat.choose, h5]
  have h7 : bernoulli' 7 = 0 :=
    bernoulli'_eq_zero_of_odd (by decide) (by omega)
  have h8 : bernoulli' 8 = -1 / 30 := by
    rw [bernoulli'_def]
    norm_num [Finset.sum_range_succ, Nat.choose, h5, h6, h7]
  have h9 : bernoulli' 9 = 0 :=
    bernoulli'_eq_zero_of_odd (by decide) (by omega)
  rw [ell, bernoulli_eq_bernoulli'_of_ne_one (by omega)]
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose, h5, h6, h7, h8, h9]

variable {R : Type*} [Field R] [CharZero R]

/-- The degree-five logarithmic root polynomial, retaining the powers of `u`
and using `z_j = 2 p_j`. -/
def B5 (n : ℕ) (u z1 z2 z3 z4 z5 : R) : R :=
  -((n : R) - 511) / 239500800 * u ^ 5 +
    u ^ 4 * z1 / 10644480 - u ^ 3 * z2 / 2280960 +
    u ^ 2 * z3 / 2280960 - u * z4 / 10644480 + z5 / 479001600

theorem rawB_five (n : ℕ) (u : R) (z : ℕ → R) :
    rawB n u z 5 = B5 n u (z 1) (z 2) (z 3) (z 4) (z 5) := by
  simp only [rawB]
  rw [ell_five]
  norm_num [Finset.sum_range_succ, Nat.choose, splitPower, B5]
  ring

/-- At `u = 1` and `z_j = 2 p_j`, the root sum is exactly Chapter 6's
reduced logarithmic coefficient `L₅`. -/
theorem B5_reduced (n : ℕ) (p1 p2 p3 p4 p5 : R) :
    B5 n 1 (2 * p1) (2 * p2) (2 * p3) (2 * p4) (2 * p5) =
      (2 * (ell 5 : R)) *
        ((n : R) + 1 - 512 - 45 * p1 + 210 * p2 - 210 * p3 + 45 * p4 - p5) := by
  rw [ell_five]
  norm_num [B5]
  ring

/-- The fifth exponential coefficient in terms of logarithmic coefficients. -/
def A5 (b1 b2 b3 b4 b5 : R) : R :=
  b5 + b1 * b4 + b2 * b3 + b1 ^ 2 * b3 / 2 +
    b1 * b2 ^ 2 / 2 + b1 ^ 3 * b2 / 6 + b1 ^ 5 / 120

theorem A5_recurrence (b1 b2 b3 b4 b5 : R) :
    5 * A5 b1 b2 b3 b4 b5 =
      b1 * A4 b1 b2 b3 b4 + 2 * b2 * A3 b1 b2 b3 +
      3 * b3 * A2 b1 b2 + 4 * b4 * A1 b1 + 5 * b5 * A0 := by
  simp only [A5, A4, A3, A2, A1, A0]
  ring

end QuaternionicSymmetry.LogAhat
