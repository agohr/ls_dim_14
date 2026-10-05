import QuaternionicSymmetry.FormalExponentialCoefficients
import Mathlib.RingTheory.PowerSeries.Exp

/-! The finite recurrence computes the coefficients of the genuine formal
power-series exponential substituted into a series with zero constant term. -/
namespace QuaternionicSymmetry.FormalExponentialSeries
open FormalExponentialCoefficients
noncomputable section
variable {R : Type} [CommRing R] [Algebra ℚ R]

def logarithm (b : ℕ → R) : PowerSeries R :=
  PowerSeries.mk (fun n => if n = 0 then 0 else b n)

omit [Algebra ℚ R] in
@[simp] theorem logarithm_constant (b : ℕ → R) :
    PowerSeries.constantCoeff (logarithm b) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [logarithm]

def exponential (b : ℕ → R) : PowerSeries R :=
  (PowerSeries.exp R).subst (logarithm b)

theorem exponential_constant (b : ℕ → R) :
    PowerSeries.constantCoeff (exponential b) = 1 := by
  change MvPowerSeries.constantCoeff ((PowerSeries.exp R).subst (logarithm b)) = 1
  rw [PowerSeries.constantCoeff_subst
    (PowerSeries.HasSubst.of_constantCoeff_zero (logarithm_constant b))]
  rw [finsum_eq_single _ 0]
  · simp
  · intro d hd
    have hzero : MvPowerSeries.constantCoeff (logarithm b) = 0 := logarithm_constant b
    simp [map_pow, hzero, zero_pow hd]

theorem derivative_exponential (b : ℕ → R) :
    PowerSeries.derivative R (exponential b) =
      PowerSeries.derivative R (logarithm b) * exponential b := by
  rw [exponential, PowerSeries.derivative_subst R
    (PowerSeries.HasSubst.of_constantCoeff_zero (logarithm_constant b)),
    PowerSeries.derivative_exp, mul_comm]

theorem exponential_coefficient (b : ℕ → R) (n : ℕ) :
    PowerSeries.coeff n (exponential b) = coefficient b n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      rw [coefficient_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply,
        exponential_constant]
    | succ n =>
      have heq := congrArg (PowerSeries.coeff n) (derivative_exponential b)
      rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at heq
      simp only [PowerSeries.coeff_derivative, logarithm, PowerSeries.coeff_mk,
        Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false] at heq
      rw [coefficient_succ, Fin.sum_univ_eq_sum_range
        (fun j => (j+1 : R) * b (j+1) * coefficient b (n-j)) (n+1)]
      have heq' : PowerSeries.coeff (n+1) (exponential b) * (n+1 : R) =
          ∑ j ∈ Finset.range (n+1),
            (j+1 : R) * b (j+1) * coefficient b (n-j) := by
        rw [heq]
        apply Finset.sum_congr rfl
        intro j hj
        rw [ih (n-j) (by omega)]
        ring
      have hi : (n+1 : R) * algebraMap ℚ R (1/(n+1 : ℚ)) = 1 := by
        have hq : (n+1 : ℚ) * (1/(n+1 : ℚ)) = 1 := by field_simp
        simpa only [map_mul, map_add, map_natCast, map_one] using
          congrArg (algebraMap ℚ R) hq
      rw [← heq']
      calc
        _ = PowerSeries.coeff (n+1) (exponential b) *
            ((n+1 : R) * algebraMap ℚ R (1/(n+1 : ℚ))) := by rw [hi, mul_one]
        _ = _ := by ring

end
end QuaternionicSymmetry.FormalExponentialSeries
