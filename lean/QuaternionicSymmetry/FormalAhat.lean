import QuaternionicSymmetry.CharacterSeries
import QuaternionicSymmetry.LogAhat
import Mathlib.RingTheory.PowerSeries.Inverse

/-! The first coefficients of the actual formal A-hat series.

The denominator is characterized by `X * denominator = exp(X/2) - exp(-X/2)`.
Its inverse is therefore the formal series `(X/2)/sinh(X/2)`. No analytic
convergence or geometric interpretation is assumed here.
-/

namespace QuaternionicSymmetry.FormalAhat

open scoped BigOperators

noncomputable section

def denominator : PowerSeries ℚ :=
  PowerSeries.mk fun n =>
    ((1 / 2 : ℚ) ^ (n + 1) - (-1 / 2 : ℚ) ^ (n + 1)) / (n + 1).factorial

@[simp] theorem denominator_coeff (n : ℕ) :
    PowerSeries.coeff n denominator =
      ((1 / 2 : ℚ) ^ (n + 1) - (-1 / 2 : ℚ) ^ (n + 1)) / (n + 1).factorial :=
  PowerSeries.coeff_mk _ _

theorem denominator_characterization :
    PowerSeries.X * denominator =
      PowerSeries.rescale (1 / 2) (PowerSeries.exp ℚ) -
        PowerSeries.rescale (-1 / 2) (PowerSeries.exp ℚ) := by
  ext n
  cases n with
  | zero =>
      rw [map_sub, PowerSeries.coeff_rescale, PowerSeries.coeff_rescale]
      simp
  | succ n =>
      simp [PowerSeries.coeff_rescale, denominator_coeff, div_eq_mul_inv, sub_mul]

@[simp] theorem denominator_constant : PowerSeries.constantCoeff denominator = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, denominator_coeff]
  norm_num

def ahatSeries : PowerSeries ℚ := denominator⁻¹

theorem ahat_mul_denominator : ahatSeries * denominator = 1 :=
  PowerSeries.inv_mul_cancel denominator (by simp)

private theorem coefficient_equation (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1),
      PowerSeries.coeff i ahatSeries * PowerSeries.coeff (n - i) denominator =
      PowerSeries.coeff n (1 : PowerSeries ℚ) := by
  have h := congrArg (PowerSeries.coeff n) ahat_mul_denominator
  simpa only [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] using h

theorem coefficients :
    (List.range 9).map (fun n => PowerSeries.coeff n ahatSeries) =
      [1, 0, -1/24, 0, 7/5760, 0, -31/967680, 0, 127/154828800] := by
  have h0 := coefficient_equation 0
  have h1 := coefficient_equation 1
  have h2 := coefficient_equation 2
  have h3 := coefficient_equation 3
  have h4 := coefficient_equation 4
  have h5 := coefficient_equation 5
  have h6 := coefficient_equation 6
  have h7 := coefficient_equation 7
  have h8 := coefficient_equation 8
  norm_num [Finset.sum_range_succ, denominator_coeff] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  norm_num [List.range_succ]
  constructor
  · exact h0
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- The first four even coefficients are the exponential coefficients of the
Bernoulli logarithmic coefficients used in the root calculation. -/
theorem coefficients_from_log :
    PowerSeries.coeff 2 ahatSeries = LogAhat.A1 (LogAhat.ell 1) ∧
    PowerSeries.coeff 4 ahatSeries = LogAhat.A2 (LogAhat.ell 1) (LogAhat.ell 2) ∧
    PowerSeries.coeff 6 ahatSeries =
      LogAhat.A3 (LogAhat.ell 1) (LogAhat.ell 2) (LogAhat.ell 3) ∧
    PowerSeries.coeff 8 ahatSeries =
      LogAhat.A4 (LogAhat.ell 1) (LogAhat.ell 2) (LogAhat.ell 3) (LogAhat.ell 4) := by
  have h := coefficients
  norm_num [List.range_succ] at h
  rcases h with ⟨_, _, h2, _, h4, _, h6, _, h8⟩
  rw [h2, h4, h6, h8, LogAhat.ell_one, LogAhat.ell_two, LogAhat.ell_three,
    LogAhat.ell_four]
  norm_num [LogAhat.A1, LogAhat.A2, LogAhat.A3, LogAhat.A4]

end
end QuaternionicSymmetry.FormalAhat
