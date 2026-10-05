import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Finite root conversion for the invariant characteristic forms in `main.tex`,
not a claim about the pointwise spectrum of corrected Weyl curvature.

`x_a` and `h` are formal splitting roots of local `E` and `H`, with
`TℂM ≅ E ⊗ H`. The normalized tangent root pairs are `±(h+x_a)` and
`±(h-x_a)`. Thus `tangentHalfTrace j` is one half of the even power trace
of those `4n` roots. The corrected standard-bundle power sum is instead
`(-1)^j (Σ x_a^(2j) + h^(2j))`. All identities below are polynomial identities
over a rational algebra and therefore apply to invariant Chern–Weil forms
once the geometric curvature normalizations have been separately identified.
-/

namespace QuaternionicSymmetry.QuaternionicTangentRootConversion

open Finset

set_option linter.unusedSectionVars false

variable {R : Type} [CommRing R] [Algebra ℚ R]

noncomputable def half : R := algebraMap ℚ R (1 / 2)

private theorem two_mul_half : (2 : R) * half = 1 := by
  have h := map_mul (algebraMap ℚ R) (2 : ℚ) (1 / 2 : ℚ)
  norm_num at h
  simpa [half, map_ofNat] using h.symm

private theorem half_mul_two : half * (2 : R) = 1 := by
  simpa only [mul_comm] using (two_mul_half (R := R))

def scalarRootSquare (h : R) : R := h ^ 2

/-- The formal roots `2h,0,-2h` of the rank-three quaternionic bundle
give the exact characteristic identity `p₁(Q)=4u`. -/
theorem rankThreePontryaginRoot (h : R) :
    (2 * h) ^ 2 = 4 * scalarRootSquare h := by
  unfold scalarRootSquare
  ring

def symplecticRootPower (n : ℕ) (x : Fin n → R) (j : ℕ) : R :=
  ∑ a : Fin n, x a ^ (2 * j)

/-- Half of the even trace of the `4n` tangent roots
`±(h+x_a), ±(h-x_a)`. -/
def tangentHalfTrace (n : ℕ) (h : R) (x : Fin n → R) (j : ℕ) : R :=
  ∑ a : Fin n, ((h + x a) ^ (2 * j) + (h - x a) ^ (2 * j))

/-- The paper's corrected standard-bundle power sum in the formal
Levi–Civita splitting calculation. -/
def standardPowerSum (n : ℕ) (h : R) (x : Fin n → R) (j : ℕ) : R :=
  (-1 : R) ^ j * (symplecticRootPower n x j + scalarRootSquare h ^ j)

theorem symplecticRootPower_zero (n : ℕ) (x : Fin n → R) :
    symplecticRootPower n x 0 = (n : R) := by
  simp [symplecticRootPower]

/-- Exact tangent trace binomial identity through weight six. The finite
degree bound covers every `p_j` needed in dimensions at most fourteen. -/
theorem tangentHalfTrace_formula (n : ℕ) (h : R) (x : Fin n → R)
    (j : ℕ) (hj : j ≤ 6) :
    tangentHalfTrace n h x j =
      2 * (∑ v ∈ range (j + 1),
        (Nat.choose (2 * j) (2 * v) : R) *
          scalarRootSquare h ^ (j - v) * symplecticRootPower n x v) := by
  unfold tangentHalfTrace
  have hp (a : Fin n) : (h + x a) ^ (2 * j) + (h - x a) ^ (2 * j) =
      2 * (∑ v ∈ range (j + 1),
        (Nat.choose (2 * j) (2 * v) : R) *
          scalarRootSquare h ^ (j - v) * x a ^ (2 * v)) := by
    interval_cases j <;>
      norm_num [Finset.sum_range_succ, scalarRootSquare, Nat.choose] <;> ring
  calc
    (∑ a : Fin n, ((h + x a) ^ (2 * j) + (h - x a) ^ (2 * j))) =
        ∑ a : Fin n, 2 * (∑ v ∈ range (j + 1),
          (Nat.choose (2 * j) (2 * v) : R) *
            scalarRootSquare h ^ (j - v) * x a ^ (2 * v)) := by
      apply sum_congr rfl
      intro a _
      exact hp a
    _ = 2 * (∑ v ∈ range (j + 1),
          (Nat.choose (2 * j) (2 * v) : R) *
            scalarRootSquare h ^ (j - v) * symplecticRootPower n x v) := by
      simp only [symplecticRootPower, Finset.mul_sum]
      rw [Finset.sum_comm]

/-- The tangent half trace at power 1, with all even-binomial coefficients. -/
theorem tangentHalfTrace_one (n : ℕ) (h : R) (x : Fin n → R) :
    tangentHalfTrace n h x 1 = 2 * (
      (n : R) * scalarRootSquare h ^ 1 +
      symplecticRootPower n x 1) := by
  rw [tangentHalfTrace_formula n h x 1 (by omega)]
  simp [Finset.sum_range_succ, symplecticRootPower_zero, Nat.choose]
  ring

/-- The tangent half trace at power 2, with all even-binomial coefficients. -/
theorem tangentHalfTrace_two (n : ℕ) (h : R) (x : Fin n → R) :
    tangentHalfTrace n h x 2 = 2 * (
      (n : R) * scalarRootSquare h ^ 2 +
      6 * scalarRootSquare h ^ 1 * symplecticRootPower n x 1 +
      symplecticRootPower n x 2) := by
  rw [tangentHalfTrace_formula n h x 2 (by omega)]
  simp [Finset.sum_range_succ, symplecticRootPower_zero, Nat.choose]
  ring

/-- The tangent half trace at power 3, with all even-binomial coefficients. -/
theorem tangentHalfTrace_three (n : ℕ) (h : R) (x : Fin n → R) :
    tangentHalfTrace n h x 3 = 2 * (
      (n : R) * scalarRootSquare h ^ 3 +
      15 * scalarRootSquare h ^ 2 * symplecticRootPower n x 1 +
      15 * scalarRootSquare h ^ 1 * symplecticRootPower n x 2 +
      symplecticRootPower n x 3) := by
  rw [tangentHalfTrace_formula n h x 3 (by omega)]
  simp [Finset.sum_range_succ, symplecticRootPower_zero, Nat.choose]
  ring

/-- The tangent half trace at power 4, with all even-binomial coefficients. -/
theorem tangentHalfTrace_four (n : ℕ) (h : R) (x : Fin n → R) :
    tangentHalfTrace n h x 4 = 2 * (
      (n : R) * scalarRootSquare h ^ 4 +
      28 * scalarRootSquare h ^ 3 * symplecticRootPower n x 1 +
      70 * scalarRootSquare h ^ 2 * symplecticRootPower n x 2 +
      28 * scalarRootSquare h ^ 1 * symplecticRootPower n x 3 +
      symplecticRootPower n x 4) := by
  rw [tangentHalfTrace_formula n h x 4 (by omega)]
  simp [Finset.sum_range_succ, symplecticRootPower_zero, Nat.choose]
  ring

/-- The tangent half trace at power 5, with all even-binomial coefficients. -/
theorem tangentHalfTrace_five (n : ℕ) (h : R) (x : Fin n → R) :
    tangentHalfTrace n h x 5 = 2 * (
      (n : R) * scalarRootSquare h ^ 5 +
      45 * scalarRootSquare h ^ 4 * symplecticRootPower n x 1 +
      210 * scalarRootSquare h ^ 3 * symplecticRootPower n x 2 +
      210 * scalarRootSquare h ^ 2 * symplecticRootPower n x 3 +
      45 * scalarRootSquare h ^ 1 * symplecticRootPower n x 4 +
      symplecticRootPower n x 5) := by
  rw [tangentHalfTrace_formula n h x 5 (by omega)]
  simp [Finset.sum_range_succ, symplecticRootPower_zero, Nat.choose]
  ring

/-- The tangent half trace at power 6, with all even-binomial coefficients. -/
theorem tangentHalfTrace_six (n : ℕ) (h : R) (x : Fin n → R) :
    tangentHalfTrace n h x 6 = 2 * (
      (n : R) * scalarRootSquare h ^ 6 +
      66 * scalarRootSquare h ^ 5 * symplecticRootPower n x 1 +
      495 * scalarRootSquare h ^ 4 * symplecticRootPower n x 2 +
      924 * scalarRootSquare h ^ 3 * symplecticRootPower n x 3 +
      495 * scalarRootSquare h ^ 2 * symplecticRootPower n x 4 +
      66 * scalarRootSquare h ^ 1 * symplecticRootPower n x 5 +
      symplecticRootPower n x 6) := by
  rw [tangentHalfTrace_formula n h x 6 (by omega)]
  simp [Finset.sum_range_succ, symplecticRootPower_zero, Nat.choose]
  ring

/-- The 1th symplectic root sum recovered from normalized tangent
half traces and `u=h²`; only lower recovered sums occur on the right. -/
noncomputable def recoveredQ1 (n : ℕ) (u : R) (t : ℕ → R) : R :=
  half * t 1 -
    (n : R) * u ^ 1

theorem recoveredQ1_eq_root (n : ℕ) (h : R) (x : Fin n → R) :
    recoveredQ1 n (scalarRootSquare h) (tangentHalfTrace n h x) =
      symplecticRootPower n x 1 := by
  unfold recoveredQ1
  rw [tangentHalfTrace_one]
  rw [← mul_assoc, half_mul_two, one_mul]
  ring

/-- The 2th symplectic root sum recovered from normalized tangent
half traces and `u=h²`; only lower recovered sums occur on the right. -/
noncomputable def recoveredQ2 (n : ℕ) (u : R) (t : ℕ → R) : R :=
  half * t 2 -
    (n : R) * u ^ 2 -
    6 * u ^ 1 * recoveredQ1 n u t

theorem recoveredQ2_eq_root (n : ℕ) (h : R) (x : Fin n → R) :
    recoveredQ2 n (scalarRootSquare h) (tangentHalfTrace n h x) =
      symplecticRootPower n x 2 := by
  unfold recoveredQ2
  rw [tangentHalfTrace_two]
  rw [recoveredQ1_eq_root]
  rw [← mul_assoc, half_mul_two, one_mul]
  ring

/-- The 3th symplectic root sum recovered from normalized tangent
half traces and `u=h²`; only lower recovered sums occur on the right. -/
noncomputable def recoveredQ3 (n : ℕ) (u : R) (t : ℕ → R) : R :=
  half * t 3 -
    (n : R) * u ^ 3 -
    15 * u ^ 2 * recoveredQ1 n u t -
    15 * u ^ 1 * recoveredQ2 n u t

theorem recoveredQ3_eq_root (n : ℕ) (h : R) (x : Fin n → R) :
    recoveredQ3 n (scalarRootSquare h) (tangentHalfTrace n h x) =
      symplecticRootPower n x 3 := by
  unfold recoveredQ3
  rw [tangentHalfTrace_three]
  rw [recoveredQ1_eq_root]
  rw [recoveredQ2_eq_root]
  rw [← mul_assoc, half_mul_two, one_mul]
  ring

/-- The 4th symplectic root sum recovered from normalized tangent
half traces and `u=h²`; only lower recovered sums occur on the right. -/
noncomputable def recoveredQ4 (n : ℕ) (u : R) (t : ℕ → R) : R :=
  half * t 4 -
    (n : R) * u ^ 4 -
    28 * u ^ 3 * recoveredQ1 n u t -
    70 * u ^ 2 * recoveredQ2 n u t -
    28 * u ^ 1 * recoveredQ3 n u t

theorem recoveredQ4_eq_root (n : ℕ) (h : R) (x : Fin n → R) :
    recoveredQ4 n (scalarRootSquare h) (tangentHalfTrace n h x) =
      symplecticRootPower n x 4 := by
  unfold recoveredQ4
  rw [tangentHalfTrace_four]
  rw [recoveredQ1_eq_root]
  rw [recoveredQ2_eq_root]
  rw [recoveredQ3_eq_root]
  rw [← mul_assoc, half_mul_two, one_mul]
  ring

/-- The 5th symplectic root sum recovered from normalized tangent
half traces and `u=h²`; only lower recovered sums occur on the right. -/
noncomputable def recoveredQ5 (n : ℕ) (u : R) (t : ℕ → R) : R :=
  half * t 5 -
    (n : R) * u ^ 5 -
    45 * u ^ 4 * recoveredQ1 n u t -
    210 * u ^ 3 * recoveredQ2 n u t -
    210 * u ^ 2 * recoveredQ3 n u t -
    45 * u ^ 1 * recoveredQ4 n u t

theorem recoveredQ5_eq_root (n : ℕ) (h : R) (x : Fin n → R) :
    recoveredQ5 n (scalarRootSquare h) (tangentHalfTrace n h x) =
      symplecticRootPower n x 5 := by
  unfold recoveredQ5
  rw [tangentHalfTrace_five]
  rw [recoveredQ1_eq_root]
  rw [recoveredQ2_eq_root]
  rw [recoveredQ3_eq_root]
  rw [recoveredQ4_eq_root]
  rw [← mul_assoc, half_mul_two, one_mul]
  ring

/-- The 6th symplectic root sum recovered from normalized tangent
half traces and `u=h²`; only lower recovered sums occur on the right. -/
noncomputable def recoveredQ6 (n : ℕ) (u : R) (t : ℕ → R) : R :=
  half * t 6 -
    (n : R) * u ^ 6 -
    66 * u ^ 5 * recoveredQ1 n u t -
    495 * u ^ 4 * recoveredQ2 n u t -
    924 * u ^ 3 * recoveredQ3 n u t -
    495 * u ^ 2 * recoveredQ4 n u t -
    66 * u ^ 1 * recoveredQ5 n u t

theorem recoveredQ6_eq_root (n : ℕ) (h : R) (x : Fin n → R) :
    recoveredQ6 n (scalarRootSquare h) (tangentHalfTrace n h x) =
      symplecticRootPower n x 6 := by
  unfold recoveredQ6
  rw [tangentHalfTrace_six]
  rw [recoveredQ1_eq_root]
  rw [recoveredQ2_eq_root]
  rw [recoveredQ3_eq_root]
  rw [recoveredQ4_eq_root]
  rw [recoveredQ5_eq_root]
  rw [← mul_assoc, half_mul_two, one_mul]
  ring

/-- The complete recovered symplectic-root sequence through weight six. -/
noncomputable def recoveredSymplecticPowers (n : ℕ) (u : R) (t : ℕ → R) :
    Fin 7 → R :=
  ![(n : R), recoveredQ1 n u t, recoveredQ2 n u t,
    recoveredQ3 n u t, recoveredQ4 n u t,
    recoveredQ5 n u t, recoveredQ6 n u t]

/-- The paper's corrected standard-bundle `p_j` reconstructed from the
normalized tangent half traces and the scalar root square. -/
noncomputable def recoveredStandardPower (n : ℕ) (u : R) (t : ℕ → R)
    (j : Fin 7) : R :=
  (-1 : R) ^ j.val * (recoveredSymplecticPowers n u t j + u ^ j.val)

/-- The first corrected power sum contains an essential scalar correction;
it is not the signed tangent half trace by itself. -/
theorem recoveredStandardPower_one (n : ℕ) (u : R) (t : ℕ → R) :
    recoveredStandardPower n u t 1 =
      -half * t 1 + ((n : R) - 1) * u := by
  simp [recoveredStandardPower, recoveredSymplecticPowers, recoveredQ1]
  ring

theorem recoveredStandardPower_two (n : ℕ) (u : R) (t : ℕ → R) :
    recoveredStandardPower n u t 2 =
      half * t 2 - 3 * u * t 1 + (5 * (n : R) + 1) * u ^ 2 := by
  simp [recoveredStandardPower, recoveredSymplecticPowers, recoveredQ2, recoveredQ1]
  linear_combination (-3 * u * t 1) * (half_mul_two (R := R))

theorem recoveredSymplecticPowers_eq_root (n : ℕ) (h : R)
    (x : Fin n → R) (j : Fin 7) :
    recoveredSymplecticPowers n (scalarRootSquare h)
        (tangentHalfTrace n h x) j = symplecticRootPower n x j.val := by
  fin_cases j
  · simp [recoveredSymplecticPowers, symplecticRootPower_zero]
  · exact recoveredQ1_eq_root n h x
  · exact recoveredQ2_eq_root n h x
  · exact recoveredQ3_eq_root n h x
  · exact recoveredQ4_eq_root n h x
  · exact recoveredQ5_eq_root n h x
  · exact recoveredQ6_eq_root n h x

/-- Finite algebraic conversion from the normalized tangent root half
traces plus `u=h²` to the paper's corrected standard-bundle power sums
through `j=6`. This is an identity of invariant characteristic roots;
it does not identify the corrected Weyl curvature's pointwise spectrum. -/
theorem recoveredStandardPower_eq_standardPower (n : ℕ) (h : R)
    (x : Fin n → R) (j : Fin 7) :
    recoveredStandardPower n (scalarRootSquare h)
        (tangentHalfTrace n h x) j = standardPowerSum n h x j.val := by
  simp only [recoveredStandardPower, standardPowerSum,
    recoveredSymplecticPowers_eq_root]

end QuaternionicSymmetry.QuaternionicTangentRootConversion
