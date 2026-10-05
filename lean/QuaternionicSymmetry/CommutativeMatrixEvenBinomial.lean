import QuaternionicSymmetry.QuaternionicTangentEvenBinomial

/-! Even trace powers of a commuting matrix sum when one summand has scalar
square and all odd mixed traces vanish. Valid over any commutative ring. -/
namespace QuaternionicSymmetry.CommutativeMatrixEvenBinomial
noncomputable section
variable {R κ : Type*} [CommRing R] [Fintype κ] [DecidableEq κ]
variable (P S : Matrix κ κ R) (t : R)

private theorem even_pow (hsq : S ^ 2 = (-t) • (1 : Matrix κ κ R))
    (j : ℕ) : S ^ (2 * j) = (-t) ^ j • (1 : Matrix κ κ R) := by
  rw [pow_mul, hsq, smul_pow]
  simp

private theorem odd_pow (hsq : S ^ 2 = (-t) • (1 : Matrix κ κ R))
    (j : ℕ) : S ^ (2 * j + 1) = (-t) ^ j • S := by
  rw [pow_succ, even_pow S t hsq]
  simp

private theorem trace_even_mix (hsq : S ^ 2 = (-t) • (1 : Matrix κ κ R))
    (m j : ℕ) :
    Matrix.trace (P ^ m * S ^ (2 * j)) =
      (-t) ^ j * Matrix.trace (P ^ m) := by
  rw [even_pow S t hsq, mul_smul_comm, mul_one]
  exact (Matrix.traceLinearMap κ R R).map_smul ((-t) ^ j) (P ^ m)

private theorem trace_odd_mix (hsq : S ^ 2 = (-t) • (1 : Matrix κ κ R))
    (hodd : ∀ m, Matrix.trace (P ^ m * S) = 0)
    (m j : ℕ) : Matrix.trace (P ^ m * S ^ (2 * j + 1)) = 0 := by
  rw [odd_pow S t hsq, mul_smul_comm]
  change (Matrix.traceLinearMap κ R R) ((-t) ^ j • (P ^ m * S)) = 0
  rw [(Matrix.traceLinearMap κ R R).map_smul]
  change (-t) ^ j • Matrix.trace (P ^ m * S) = 0
  rw [hodd]
  simp

theorem trace_binomial_even (hcomm : Commute P S)
    (hsq : S ^ 2 = (-t) • (1 : Matrix κ κ R))
    (hodd : ∀ m, Matrix.trace (P ^ m * S) = 0)
    (j : ℕ) :
    Matrix.trace ((P + S) ^ (2 * j)) =
      ∑ m ∈ Finset.range (2 * j + 1),
        (if Even (2 * j - m) then
          (-t) ^ ((2 * j - m) / 2) * Matrix.trace (P ^ m)
         else 0) * (Nat.choose (2 * j) m : R) := by
  rw [hcomm.add_pow]
  change (Matrix.traceLinearMap κ R R)
    (∑ m ∈ Finset.range (2 * j + 1),
      P ^ m * S ^ (2 * j - m) * (Nat.choose (2 * j) m : Matrix κ κ R)) = _
  rw [map_sum]
  change (∑ m ∈ Finset.range (2 * j + 1),
    Matrix.trace (P ^ m * S ^ (2 * j - m) *
      (Nat.choose (2 * j) m : Matrix κ κ R))) = _
  apply Finset.sum_congr rfl
  intro m hm
  have hnat (X : Matrix κ κ R) (n : ℕ) :
      Matrix.trace (X * (n : Matrix κ κ R)) =
        (n : R) * Matrix.trace X := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Nat.cast_succ, mul_add]
        change (Matrix.traceLinearMap κ R R) (X * (n : Matrix κ κ R) + X * 1) = _
        rw [map_add]
        change Matrix.trace (X * (n : Matrix κ κ R)) + Matrix.trace (X * 1) = _
        rw [ih]
        simp [add_mul]
  rw [hnat]
  rw [mul_comm (Nat.choose (2 * j) m : R)]
  change Matrix.trace (P ^ m * S ^ (2 * j - m)) *
    (Nat.choose (2 * j) m : R) = _
  by_cases he : Even (2 * j - m)
  · simp only [if_pos he]
    obtain ⟨k, hk⟩ := he
    rw [hk]
    have hdiv : (k + k) / 2 = k := by omega
    rw [hdiv, show k + k = 2 * k by omega]
    rw [trace_even_mix P S t hsq m k]
  · simp only [if_neg he]
    obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp he
    rw [hk]
    rw [trace_odd_mix P S t hsq hodd m k]

end
end QuaternionicSymmetry.CommutativeMatrixEvenBinomial
