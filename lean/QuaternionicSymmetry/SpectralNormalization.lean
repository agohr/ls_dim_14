import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Tactic

/-! The scalar normalization in the quaternionic spectral coefficient formula. -/

namespace QuaternionicSymmetry.QuaternionicSpectralCoefficients

def momentScalar (n k : ℕ) : ℝ :=
  ((2 * n).choose (2 * k) : ℝ) * (Nat.doubleFactorial (2 * (n - k) - 1) : ℝ)

def radialScalar (n k : ℕ) : ℝ :=
  ((2 * n).factorial : ℝ) * (Nat.doubleFactorial (2 * (n - k) + 1) : ℝ)

theorem momentScalar_pos (n k : ℕ) (hk : k ≤ n) : 0 < momentScalar n k := by
  unfold momentScalar
  exact mul_pos (Nat.cast_pos.mpr (Nat.choose_pos (by omega)))
    (Nat.cast_pos.mpr (Nat.doubleFactorial_pos _))

theorem radialScalar_pos (n k : ℕ) : 0 < radialScalar n k := by
  unfold radialScalar
  positivity

theorem scalar_normalization (n k : ℕ) (hk : k ≤ n) :
    momentScalar n k * ((2 * k).factorial : ℝ) * ((2 * (n - k) + 1).factorial : ℝ) =
      radialScalar n k := by
  have hc : ((2 * n).choose (2 * k) : ℝ) * ((2 * k).factorial : ℝ) *
      ((2 * (n - k)).factorial : ℝ) = ((2 * n).factorial : ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show 2 * k ≤ 2 * n by omega)
    rw [show 2 * n - 2 * k = 2 * (n - k) by omega] at h
    exact_mod_cast h
  unfold momentScalar radialScalar
  rw [Nat.doubleFactorial_add_one (2 * (n - k)), Nat.factorial_succ]
  push_cast
  calc
    _ = (((2 * n).choose (2 * k) : ℝ) * ((2 * k).factorial : ℝ) *
        ((2 * (n - k)).factorial : ℝ)) *
        ((2 * (n - k : ℕ) + 1 : ℝ) * (Nat.doubleFactorial (2 * (n - k) - 1) : ℝ)) := by
      ring
    _ = _ := by rw [hc]

end QuaternionicSymmetry.QuaternionicSpectralCoefficients
