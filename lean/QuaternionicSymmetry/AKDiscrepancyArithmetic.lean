import Mathlib.Tactic

/-! The finite sign calculation in Chapter 10's effective-nonvanishing
argument. The existence of the divisors, the base-locus codimension bound,
and the log-canonical discrepancy/coefficients are explicit hypotheses;
these statements do not construct algebraic varieties or divisors. -/

namespace QuaternionicSymmetry.AKDiscrepancyArithmetic

open scoped BigOperators

/-- If each of the `n+1` divisors contains a center with multiplicity at
least one, their total multiplicity is at least `n+1`. -/
theorem sum_multiplicities_lower_bound (n : ℕ)
    (m : Fin (n + 1) → ℕ) (hm : ∀ i, 1 ≤ m i) :
    n + 1 ≤ ∑ i, m i := by
  calc
    n + 1 = ∑ _i : Fin (n + 1), (1 : ℕ) := by simp
    _ ≤ ∑ i, m i := by
      apply Finset.sum_le_sum
      intro i _
      exact hm i

/-- The actual exceptional-divisor discrepancy formula, together with the
log-canonical lower bound, forces the codimension to be at least `n+1`.
This branch applies only to a smooth center of codimension at least two. -/
theorem codimension_lower_bound (n c : ℕ) (m : Fin (n + 1) → ℕ)
    (hm : ∀ i, 1 ≤ m i)
    (hlc : (-1 : ℤ) ≤ (c : ℤ) - 1 - (∑ i, m i : ℕ)) :
    n + 1 ≤ c := by
  have hs := sum_multiplicities_lower_bound n m hm
  omega

/-- The codimension-at-least-two branch contradicts a base-locus component
of codimension at most three once `n≥5`. -/
theorem exceptional_branch_contradiction (n c d : ℕ)
    (m : Fin (n + 1) → ℕ) (hn : 5 ≤ n) (hc : 2 ≤ c)
    (hm : ∀ i, 1 ≤ m i)
    (hlc : (-1 : ℤ) ≤ (c : ℤ) - 1 - (∑ i, m i : ℕ))
    (hcd : c ≤ d) (hd : d ≤ 3) : False := by
  have hnondivisorial : c ≠ 1 := by omega
  have h := codimension_lower_bound n c m hm hlc
  omega

/-- Codimension one is separate: a component contained in every reduced
divisor has coefficient at least `n+1`, while log canonicity allows at most
one. The coefficient upper bound is the explicit geometric input. -/
theorem divisorial_branch_contradiction (n : ℕ) (hn : 5 ≤ n)
    (hcoefficient : n + 1 ≤ 1) : False := by
  omega

/-- The complete finite dichotomy, after the geometric construction has
supplied the correct hypothesis for the actual codimension. -/
theorem finite_ladder_contradiction (n c d : ℕ)
    (m : Fin (n + 1) → ℕ) (hn : 5 ≤ n) (hc : 1 ≤ c)
    (hcd : c ≤ d) (hd : d ≤ 3)
    (hdivisorial : c = 1 → n + 1 ≤ 1)
    (hexceptional : 2 ≤ c →
      (∀ i, 1 ≤ m i) ∧
      (-1 : ℤ) ≤ (c : ℤ) - 1 - (∑ i, m i : ℕ)) : False := by
  by_cases hfirst : c = 1
  · exact divisorial_branch_contradiction n hn (hdivisorial hfirst)
  · have htwo : 2 ≤ c := by omega
    obtain ⟨hm, hlc⟩ := hexceptional htwo
    exact exceptional_branch_contradiction n c d m hn htwo hm hlc hcd hd

end QuaternionicSymmetry.AKDiscrepancyArithmetic
