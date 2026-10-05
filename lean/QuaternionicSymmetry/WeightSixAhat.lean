import QuaternionicSymmetry.WeightFiveAhat

/-! The weight-six term of the universal A-hat root calculation in Chapter 6.
The variable `u` and the independent power sums `z₁,…,z₆` are retained;
this asserts an algebraic identity, not an equality of forms or numbers. -/

namespace QuaternionicSymmetry.LogAhat

open scoped BigOperators

theorem ell_six : ell 6 = 691 / 15692092416000 := by
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
  have h10 : bernoulli' 10 = 5 / 66 := by
    rw [bernoulli'_def]
    norm_num [Finset.sum_range_succ, Nat.choose, h5, h6, h7, h8, h9]
  have h11 : bernoulli' 11 = 0 :=
    bernoulli'_eq_zero_of_odd (by decide) (by omega)
  rw [ell, bernoulli_eq_bernoulli'_of_ne_one (by omega), bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose, h5, h6, h7, h8, h9, h10, h11]

variable {R : Type*} [Field R] [CharZero R]

/-- Weight six before reducing `u` to one and with `z_j=2p_j` left explicit. -/
def B6 (n : ℕ) (u z1 z2 z3 z4 z5 z6 : R) : R :=
  (691 / 7846046208000 : R) * ((n : R) - 2047) * u ^ 6
    - (691 / 237758976000 : R) * u ^ 5 * z1
    + (691 / 31701196800 : R) * u ^ 4 * z2
    - (691 / 16982784000 : R) * u ^ 3 * z3
    + (691 / 31701196800 : R) * u ^ 2 * z4
    - (691 / 237758976000 : R) * u * z5
    + (691 / 15692092416000 : R) * z6

theorem rawB_six (n : ℕ) (u : R) (z : ℕ → R) :
    rawB n u z 6 = B6 n u (z 1) (z 2) (z 3) (z 4) (z 5) (z 6) := by
  simp only [rawB]
  rw [ell_six]
  norm_num [Finset.sum_range_succ, Nat.choose, splitPower, B6]
  ring

/-- The reduced Chapter 6 coefficient, at `u=1` and `z_j=2p_j`. -/
theorem B6_reduced (n : ℕ) (p1 p2 p3 p4 p5 p6 : R) :
    B6 n 1 (2 * p1) (2 * p2) (2 * p3) (2 * p4) (2 * p5) (2 * p6) =
      (2 * (ell 6 : R)) *
        ((n : R) + 1 - 2048 - 66 * p1 + 495 * p2 - 924 * p3
          + 495 * p4 - 66 * p5 + p6) := by
  rw [ell_six]
  norm_num [B6]
  ring

/-- The weight-six exponential coefficient in the logarithmic coefficients. -/
def A6 (b1 b2 b3 b4 b5 b6 : R) : R :=
  b6 + b1 * b5 + b2 * b4 + b3 ^ 2 / 2 + b1 ^ 2 * b4 / 2
    + b1 * b2 * b3 + b2 ^ 3 / 6 + b1 ^ 3 * b3 / 6
    + b1 ^ 2 * b2 ^ 2 / 4 + b1 ^ 4 * b2 / 24 + b1 ^ 6 / 720

theorem A6_recurrence (b1 b2 b3 b4 b5 b6 : R) :
    6 * A6 b1 b2 b3 b4 b5 b6 =
      b1 * A5 b1 b2 b3 b4 b5 + 2 * b2 * A4 b1 b2 b3 b4
        + 3 * b3 * A3 b1 b2 b3 + 4 * b4 * A2 b1 b2
        + 5 * b5 * A1 b1 + 6 * b6 * A0 := by
  simp only [A6, A5, A4, A3, A2, A1, A0]
  ring

end QuaternionicSymmetry.LogAhat
