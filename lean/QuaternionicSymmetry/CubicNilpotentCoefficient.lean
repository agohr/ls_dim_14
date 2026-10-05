import QuaternionicSymmetry.CubicNilpotentSum
import Mathlib.Tactic

namespace QuaternionicSymmetry.CubicNilpotentSum

/-- The recursive top coefficient has the exact factorial normalization. -/
theorem two_pow_mul_topCoefficient (n : ℕ) :
    2 ^ n * topCoefficient n = (2 * n).factorial := by
  induction n with
  | zero => norm_num [topCoefficient]
  | succ n ih =>
      have hchoose : 2 * (2 * n + 2).choose 2 = (2 * n + 2) * (2 * n + 1) := by
        rw [Nat.choose_two_right]
        rw [show 2 * n + 2 - 1 = 2 * n + 1 by omega]
        apply Nat.mul_div_cancel'
        refine ⟨(n + 1) * (2 * n + 1), ?_⟩
        ring
      rw [show 2 * (n + 1) = 2 * n + 2 by omega]
      calc
        2 ^ (n + 1) * topCoefficient (n + 1) =
            (2 ^ n * topCoefficient n) * (2 * (2 * n + 2).choose 2) := by
              rw [pow_succ, topCoefficient]
              ring
        _ = (2 * n).factorial * (2 * (2 * n + 2).choose 2) := by rw [ih]
        _ = (2 * n).factorial * ((2 * n + 2) * (2 * n + 1)) := by rw [hchoose]
        _ = (2 * n + 2) * (2 * n + 1) * (2 * n).factorial := by
          calc
            (2 * n).factorial * ((2 * n + 2) * (2 * n + 1)) =
                ((2 * n + 2) * (2 * n + 1)) * (2 * n).factorial := by ac_rfl
            _ = ((2 * n + 1 + 1) * (2 * n + 1)) * (2 * n).factorial := by
              congr 2
            _ = (2 * n + 1 + 1) * ((2 * n + 1) * (2 * n).factorial) := by ac_rfl
            _ = (2 * n + 2) * ((2 * n + 1) * (2 * n).factorial) := by
              congr 1
            _ = (2 * n + 2) * (2 * n + 1) * (2 * n).factorial := by ac_rfl
        _ = (2 * n + 2).factorial := by
          rw [Nat.factorial_succ, Nat.factorial_succ]
          calc
            (2 * n + 2) * (2 * n + 1) * (2 * n).factorial =
                ((2 * n + 1 + 1) * (2 * n + 1)) * (2 * n).factorial := by
                  congr 2
            _ = (2 * n + 1 + 1) * ((2 * n + 1) * (2 * n).factorial) := by ac_rfl


/-- The same normalization after casting to any semiring. -/
theorem cast_two_pow_mul_topCoefficient {R : Type*} [Semiring R] (n : ℕ) :
    (2 : R) ^ n * (topCoefficient n : R) = ((2 * n).factorial : R) := by
  change ((2 : ℕ) : R) ^ n * (topCoefficient n : R) = ((2 * n).factorial : R)
  rw [← Nat.cast_pow, ← Nat.cast_mul]
  exact congrArg (fun z : ℕ => (z : R)) (two_pow_mul_topCoefficient n)

end QuaternionicSymmetry.CubicNilpotentSum
