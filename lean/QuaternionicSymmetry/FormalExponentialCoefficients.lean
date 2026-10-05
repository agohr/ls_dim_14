import QuaternionicSymmetry.QuaternionicRootRecoveryNaturality
import QuaternionicSymmetry.DimensionElevenTwelveDensity

/-! Coefficients of a formal exponential with zero logarithmic constant
term, defined by the usual derivative recurrence. This definition uses only
rational scalar multiplication and is valid in rings with nilpotents. -/
namespace QuaternionicSymmetry.FormalExponentialCoefficients
noncomputable section
variable {R : Type} [CommRing R] [Algebra ℚ R]

def coefficient (b : ℕ → R) : ℕ → R
  | 0 => 1
  | n+1 => algebraMap ℚ R (1/(n+1 : ℚ)) *
      ∑ j : Fin (n+1), (j.val+1 : R) * b (j.val+1) * coefficient b (n-j.val)
termination_by n => n

theorem coefficient_zero (b : ℕ → R) : coefficient b 0 = 1 := by
  rw [coefficient]

theorem coefficient_succ (b : ℕ → R) (n : ℕ) :
    coefficient b (n+1) = algebraMap ℚ R (1/(n+1 : ℚ)) *
      ∑ j : Fin (n+1), (j.val+1 : R) * b (j.val+1) * coefficient b (n-j.val) := by
  rw [coefficient]

theorem coefficient_congr (b c : ℕ → R) (n : ℕ)
    (h : ∀ j, 1 ≤ j → j ≤ n → b j = c j) :
    coefficient b n = coefficient c n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [coefficient_zero]
    | succ n =>
      rw [coefficient_succ, coefficient_succ]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [h (j.val+1) (by omega) (by omega)]
      rw [ih (n-j.val) (by omega) (fun k hk hkn => h k hk (by omega))]

variable {S : Type} [CommRing S] [Algebra ℚ S]

theorem map_coefficient (f : R →+* S) (b : ℕ → R) (n : ℕ) :
    f (coefficient b n) = coefficient (fun j => f (b j)) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [coefficient_zero]
    | succ n =>
      rw [coefficient_succ, coefficient_succ, map_mul,
        RingHom.map_rat_algebraMap, map_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [map_mul, map_mul, map_add, map_natCast, map_one, ih (n-j.val) (by omega)]

/-- The recurrence is the coefficient form of `A' = B' A`. -/
theorem recurrence (b : ℕ → R) (n : ℕ) :
    (n+1 : R) * coefficient b (n+1) =
      ∑ j : Fin (n+1), (j.val+1 : R) * b (j.val+1) * coefficient b (n-j.val) := by
  rw [coefficient_succ, ← mul_assoc]
  have h : (n+1 : R) * algebraMap ℚ R (1/(n+1 : ℚ)) = 1 := by
    have hq : (n+1 : ℚ) * (1/(n+1 : ℚ)) = 1 := by field_simp
    simpa only [map_mul, map_add, map_natCast, map_one] using
      congrArg (algebraMap ℚ R) hq
  rw [h, one_mul]

end
end QuaternionicSymmetry.FormalExponentialCoefficients
