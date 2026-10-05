import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Tactic

/-!
Finite Gaussian moment polynomials.  These are identities in an arbitrary
commutative semiring and are not statements about expectations or measures.
-/

namespace QuaternionicSymmetry.GaussianMomentPolynomials

variable {R : Type*} [CommSemiring R]

/-- The formal even Gaussian moment polynomial, with `0‼ = 1`. -/
def moment (n : ℕ) (v : R) : R :=
  if n % 2 = 0 then (Nat.doubleFactorial (n - 1) : R) * v ^ (n / 2) else 0

@[simp] theorem moment_zero (v : R) : moment 0 v = 1 := by
  norm_num [moment]

@[simp] theorem moment_one (v : R) : moment 1 v = 0 := by
  norm_num [moment]

@[simp] theorem moment_two (v : R) : moment 2 v = v := by
  norm_num [moment]

@[simp] theorem moment_three (v : R) : moment 3 v = 0 := by
  norm_num [moment]

@[simp] theorem moment_four (v : R) : moment 4 v = 3 * v ^ 2 := by
  norm_num [moment]

@[simp] theorem moment_five (v : R) : moment 5 v = 0 := by
  norm_num [moment]

@[simp] theorem moment_six (v : R) : moment 6 v = 15 * v ^ 3 := by
  norm_num [moment]

@[simp] theorem moment_seven (v : R) : moment 7 v = 0 := by
  norm_num [moment]

@[simp] theorem moment_eight (v : R) : moment 8 v = 105 * v ^ 4 := by
  norm_num [moment]

/-- Binomial convolution of formal moments through order eight. -/
theorem moment_convolution_le_eight (m : ℕ) (hm : m ≤ 8) (u v : R) :
    ∑ j ∈ Finset.range (m + 1),
      (Nat.choose m j : R) * moment (m - j) u * moment j v = moment m (u + v) := by
  interval_cases m <;>
    norm_num [Finset.sum_range_succ, moment, Nat.choose] <;>
    ring

end QuaternionicSymmetry.GaussianMomentPolynomials
