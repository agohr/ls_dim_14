import QuaternionicSymmetry.QuaternionicAbstractRootInversion
import QuaternionicSymmetry.QuaternionicActualTangentTraceBinomial

/-! The signs and quarter/half trace factors converting an actual real
quaternionic matrix binomial to corrected spectral power sums. -/
namespace QuaternionicSymmetry.QuaternionicScaledBinomialNormalization
open QuaternionicAbstractRootInversion
noncomputable section
set_option maxHeartbeats 1000000

variable {R κ : Type} [CommRing R] [Algebra ℚ R]
  [Fintype κ] [DecidableEq κ]

def scaledU (c z : R) : R := c * z
def scaledSpPower (c : R) (A : Matrix κ κ R) (j : ℕ) : R :=
  (-c) ^ j * algebraMap ℚ R (1 / 4) * Matrix.trace (A ^ (2 * j))
def scaledTangentHalfTrace (c : R) (A C : Matrix κ κ R) (j : ℕ) : R :=
  (-c) ^ j * algebraMap ℚ R (1 / 2) * Matrix.trace ((A + C) ^ (2 * j))

theorem scaledSpPower_zero (c : R) (A : Matrix κ κ R) (n : ℕ)
    (hcard : Fintype.card κ = 4 * n) :
    scaledSpPower c A 0 = (n : R) := by
  have hquarter : (4 : R) * algebraMap ℚ R (1 / 4) = 1 := by
    have h := map_mul (algebraMap ℚ R) (4 : ℚ) (1 / 4 : ℚ)
    norm_num at h
    simpa only [map_ofNat] using h.symm
  calc
    scaledSpPower c A 0 =
      algebraMap ℚ R (1 / 4) * (Fintype.card κ : R) := by
        simp [scaledSpPower]
    _ = algebraMap ℚ R (1 / 4) * (4 * (n : R)) := by
      rw [hcard, Nat.cast_mul]
      norm_num
    _ =
      ((4 : R) * algebraMap ℚ R (1 / 4)) * n := by ring
    _ = n := by rw [hquarter]; ring

theorem scaled_trace_eq_binomial (n : ℕ) (c z : R)
    (A C : Matrix κ κ R)
    (hbin : ∀ j : ℕ,
      Matrix.trace ((A + C) ^ (2 * j)) =
        ∑ m ∈ Finset.range (2 * j + 1),
          (if Even (2 * j - m) then
            (-z) ^ ((2 * j - m) / 2) * Matrix.trace (A ^ m)
           else 0) * (Nat.choose (2 * j) m : R))
    (j : ℕ) (hj : j ≤ 6) :
    scaledTangentHalfTrace c A C j =
      binomialTangentTrace n (scaledU c z) (scaledSpPower c A) j := by
  have hhalf : algebraMap ℚ R (1 / 2) =
      2 * algebraMap ℚ R (1 / 4) := by
    rw [show (1 / 2 : ℚ) = 1 / 4 + 1 / 4 by norm_num, map_add]
    ring
  unfold scaledTangentHalfTrace
  rw [hbin j]
  interval_cases j <;>
    norm_num [binomialTangentTrace,
      scaledSpPower, scaledU,
      Finset.sum_range_succ, Nat.choose, hhalf] <;> ring

end
end QuaternionicSymmetry.QuaternionicScaledBinomialNormalization
