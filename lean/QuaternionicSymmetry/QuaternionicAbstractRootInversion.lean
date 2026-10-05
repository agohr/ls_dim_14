import QuaternionicSymmetry.QuaternionicTangentRootConversion

/-! The corrected-root triangular formulas invert the even binomial
trace transform for arbitrary commutative rational algebras. No choice
of spectral roots is needed, so this applies to nilpotent exterior forms. -/
namespace QuaternionicSymmetry.QuaternionicAbstractRootInversion
open QuaternionicTangentRootConversion Finset
noncomputable section

variable {R : Type} [CommRing R] [Algebra ℚ R]

def binomialTangentTrace (_n : ℕ) (u : R) (q : ℕ → R) (j : ℕ) : R :=
  2 * (∑ v ∈ range (j + 1),
    (Nat.choose (2 * j) (2 * v) : R) * u ^ (j - v) * q v)

private theorem half_mul_two : (half (R := R)) * (2 : R) = 1 := by
  dsimp [half]
  have h := map_mul (algebraMap ℚ R) (1 / 2 : ℚ) (2 : ℚ)
  norm_num at h
  simpa only [map_ofNat] using h.symm

theorem recoveredQ1_binomial (n : ℕ) (u : R) (q : ℕ → R)
    (hq0 : q 0 = (n : R)) :
    recoveredQ1 n u (binomialTangentTrace n u q) = q 1 := by
  simp [recoveredQ1, binomialTangentTrace, Finset.sum_range_succ,
    Nat.choose, hq0]
  calc
    _ = (half (R := R) * 2) * (u * (n : R) + q 1) - u * n := by ring
    _ = q 1 := by rw [half_mul_two]; ring

theorem recoveredQ2_binomial (n : ℕ) (u : R) (q : ℕ → R)
    (hq0 : q 0 = (n : R)) :
    recoveredQ2 n u (binomialTangentTrace n u q) = q 2 := by
  rw [recoveredQ2, recoveredQ1_binomial n u q hq0]
  simp [binomialTangentTrace, Finset.sum_range_succ,
    Nat.choose, hq0]
  calc
    _ = (half (R := R) * 2) *
      (6 * u * q 1 + u ^ 2 * (n : R) + q 2) -
        6 * u * q 1 - u ^ 2 * n := by ring
    _ = q 2 := by rw [half_mul_two]; ring

omit [Algebra ℚ R] in
theorem binomialTangentTrace_three (n : ℕ) (u : R) (q : ℕ → R)
    (hq0 : q 0 = (n : R)) :
    binomialTangentTrace n u q 3 =
      2 * ((n : R) * u ^ 3 + 15 * u ^ 2 * q 1 +
        15 * u * q 2 + q 3) := by
  simp [binomialTangentTrace, Finset.sum_range_succ, Nat.choose, hq0]
  ring

theorem recoveredQ3_binomial (n : ℕ) (u : R) (q : ℕ → R)
    (hq0 : q 0 = (n : R)) :
    recoveredQ3 n u (binomialTangentTrace n u q) = q 3 := by
  rw [recoveredQ3, recoveredQ1_binomial n u q hq0,
    recoveredQ2_binomial n u q hq0,
    binomialTangentTrace_three n u q hq0]
  calc
    _ = (half (R := R) * 2) *
      ((n : R) * u ^ 3 + 15 * u ^ 2 * q 1 +
        15 * u * q 2 + q 3) -
        (n : R) * u ^ 3 - 15 * u ^ 2 * q 1 -
          15 * u * q 2 := by ring
    _ = q 3 := by rw [half_mul_two]; ring

omit [Algebra ℚ R] in
theorem binomialTangentTrace_four (n : ℕ) (u : R) (q : ℕ → R)
    (hq0 : q 0 = (n : R)) :
    binomialTangentTrace n u q 4 =
      2 * ((n : R) * u ^ 4 + 28 * u ^ 3 * q 1 +
        70 * u ^ 2 * q 2 + 28 * u * q 3 + q 4) := by
  simp [binomialTangentTrace, Finset.sum_range_succ, Nat.choose, hq0]
  ring

theorem recoveredQ4_binomial (n : ℕ) (u : R) (q : ℕ → R)
    (hq0 : q 0 = (n : R)) :
    recoveredQ4 n u (binomialTangentTrace n u q) = q 4 := by
  rw [recoveredQ4, recoveredQ1_binomial n u q hq0,
    recoveredQ2_binomial n u q hq0,
    recoveredQ3_binomial n u q hq0,
    binomialTangentTrace_four n u q hq0]
  calc
    _ = (half (R := R) * 2) *
      ((n : R) * u ^ 4 + 28 * u ^ 3 * q 1 +
        70 * u ^ 2 * q 2 + 28 * u * q 3 + q 4) -
        (n : R) * u ^ 4 - 28 * u ^ 3 * q 1 -
          70 * u ^ 2 * q 2 - 28 * u * q 3 := by ring
    _ = q 4 := by rw [half_mul_two]; ring

omit [Algebra ℚ R] in
theorem binomialTangentTrace_five (n : ℕ) (u : R) (q : ℕ → R)
    (hq0 : q 0 = (n : R)) :
    binomialTangentTrace n u q 5 =
      2 * ((n : R) * u ^ 5 + 45 * u ^ 4 * q 1 +
        210 * u ^ 3 * q 2 + 210 * u ^ 2 * q 3 +
        45 * u * q 4 + q 5) := by
  simp [binomialTangentTrace, Finset.sum_range_succ, Nat.choose, hq0]
  ring

theorem recoveredQ5_binomial (n : ℕ) (u : R) (q : ℕ → R)
    (hq0 : q 0 = (n : R)) :
    recoveredQ5 n u (binomialTangentTrace n u q) = q 5 := by
  rw [recoveredQ5, recoveredQ1_binomial n u q hq0,
    recoveredQ2_binomial n u q hq0,
    recoveredQ3_binomial n u q hq0,
    recoveredQ4_binomial n u q hq0,
    binomialTangentTrace_five n u q hq0]
  calc
    _ = (half (R := R) * 2) *
      ((n : R) * u ^ 5 + 45 * u ^ 4 * q 1 +
        210 * u ^ 3 * q 2 + 210 * u ^ 2 * q 3 +
        45 * u * q 4 + q 5) -
        (n : R) * u ^ 5 - 45 * u ^ 4 * q 1 -
          210 * u ^ 3 * q 2 - 210 * u ^ 2 * q 3 -
            45 * u * q 4 := by ring
    _ = q 5 := by rw [half_mul_two]; ring

omit [Algebra ℚ R] in
theorem binomialTangentTrace_six (n : ℕ) (u : R) (q : ℕ → R)
    (hq0 : q 0 = (n : R)) :
    binomialTangentTrace n u q 6 =
      2 * ((n : R) * u ^ 6 + 66 * u ^ 5 * q 1 +
        495 * u ^ 4 * q 2 + 924 * u ^ 3 * q 3 +
        495 * u ^ 2 * q 4 + 66 * u * q 5 + q 6) := by
  simp [binomialTangentTrace, Finset.sum_range_succ, Nat.choose, hq0]
  ring

theorem recoveredQ6_binomial (n : ℕ) (u : R) (q : ℕ → R)
    (hq0 : q 0 = (n : R)) :
    recoveredQ6 n u (binomialTangentTrace n u q) = q 6 := by
  rw [recoveredQ6, recoveredQ1_binomial n u q hq0,
    recoveredQ2_binomial n u q hq0,
    recoveredQ3_binomial n u q hq0,
    recoveredQ4_binomial n u q hq0,
    recoveredQ5_binomial n u q hq0,
    binomialTangentTrace_six n u q hq0]
  calc
    _ = (half (R := R) * 2) *
      ((n : R) * u ^ 6 + 66 * u ^ 5 * q 1 +
        495 * u ^ 4 * q 2 + 924 * u ^ 3 * q 3 +
        495 * u ^ 2 * q 4 + 66 * u * q 5 + q 6) -
        (n : R) * u ^ 6 - 66 * u ^ 5 * q 1 -
          495 * u ^ 4 * q 2 - 924 * u ^ 3 * q 3 -
            495 * u ^ 2 * q 4 - 66 * u * q 5 := by ring
    _ = q 6 := by rw [half_mul_two]; ring

theorem recoveredSymplecticPowers_binomial (n : ℕ) (u : R) (q : ℕ → R)
    (hq0 : q 0 = (n : R)) (j : Fin 7) :
    recoveredSymplecticPowers n u (binomialTangentTrace n u q) j = q j.val := by
  fin_cases j
  · simpa [recoveredSymplecticPowers] using hq0.symm
  · exact recoveredQ1_binomial n u q hq0
  · exact recoveredQ2_binomial n u q hq0
  · exact recoveredQ3_binomial n u q hq0
  · exact recoveredQ4_binomial n u q hq0
  · exact recoveredQ5_binomial n u q hq0
  · exact recoveredQ6_binomial n u q hq0

/-- Full corrected standard power sum identity through weight six in
any rational commutative algebra, with no spectral-root premise. -/
theorem recoveredStandardPower_binomial (n : ℕ) (u : R) (q : ℕ → R)
    (hq0 : q 0 = (n : R)) (j : Fin 7) :
    recoveredStandardPower n u (binomialTangentTrace n u q) j =
      (-1 : R) ^ j.val * (q j.val + u ^ j.val) := by
  simp only [recoveredStandardPower,
    recoveredSymplecticPowers_binomial n u q hq0]

theorem recoveredStandardPower_congr (n : ℕ) (u : R) (t s : ℕ → R)
    (h : ∀ m, m ≤ 6 → t m = s m) (j : Fin 7) :
    recoveredStandardPower n u t j = recoveredStandardPower n u s j := by
  fin_cases j <;>
    simp [recoveredStandardPower, recoveredSymplecticPowers,
      recoveredQ1, recoveredQ2, recoveredQ3, recoveredQ4,
      recoveredQ5, recoveredQ6, h 1 (by omega), h 2 (by omega),
      h 3 (by omega), h 4 (by omega), h 5 (by omega), h 6 (by omega)]

end
end QuaternionicSymmetry.QuaternionicAbstractRootInversion
