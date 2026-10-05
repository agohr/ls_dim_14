import Mathlib.Tactic

/-!
# Finite arithmetic from the printed certificates

This file records only numerical consequences of the formulas in Chapters 9 and
10 of the textbook.  In particular, `delta`, `scalarCoefficient`, and the
dimension functions below are definitions of finite arithmetic expressions.  No
geometric, index-theoretic, or curvature statement is assumed here.
-/

namespace QuaternionicSymmetry

/- The offset in `d - delta n` from the virtual-character calculation. -/
def delta (n : ℕ) : ℕ := if n % 2 = 0 then n + 3 else n + 1

/- The scalar coefficient in the printed positivity certificates. -/
def scalarCoefficient (n : ℕ) : ℕ :=
  if n % 2 = 0 then 2 * n * (n + 2) else 2 * (n + 1) ^ 2

/- The dimensions used in the text's dimension table. -/
def baseRealDimension (n : ℕ) : ℕ := 4 * n
def twistorComplexDimension (n : ℕ) : ℕ := 2 * n + 1

theorem delta_even {n : ℕ} (h : n % 2 = 0) : delta n = n + 3 := by
  simp [delta, h]

theorem delta_odd {n : ℕ} (h : n % 2 ≠ 0) : delta n = n + 1 := by
  simp [delta, h]

theorem scalarCoefficient_even {n : ℕ} (h : n % 2 = 0) :
    scalarCoefficient n = 2 * n * (n + 2) := by
  simp [scalarCoefficient, h]

theorem scalarCoefficient_odd {n : ℕ} (h : n % 2 ≠ 0) :
    scalarCoefficient n = 2 * (n + 1) ^ 2 := by
  simp [scalarCoefficient, h]

/- The calibration identity on quaternionic projective space, as an identity
   of natural-number polynomials. -/
theorem delta_add_scalarCoefficient (n : ℕ) :
    delta n + scalarCoefficient n = (n + 1) * (2 * n + 3) := by
  have hmod : n % 2 < 2 := Nat.mod_lt n (by omega)
  by_cases h : n % 2 = 0
  · simp [delta, scalarCoefficient, h]
    ring
  · have hone : n % 2 = 1 := by omega
    simp [delta, scalarCoefficient, hone]
    ring

theorem scalarCoefficient_pos {n : ℕ} (hn : 0 < n) :
    0 < scalarCoefficient n := by
  have hmod : n % 2 < 2 := Nat.mod_lt n (by omega)
  by_cases h : n % 2 = 0
  · simp [scalarCoefficient, h]
    positivity
  · have hone : n % 2 = 1 := by omega
    simp [scalarCoefficient, hone]

/-
Pure arithmetic transfer lemma.  The hypothesis `hindex` is deliberately
explicit: it is the only place where a prospective geometric/index argument
would enter.  The theorem itself merely says that a positive `C * U` term
forces a one-unit strict improvement over the offset.
-/
theorem lower_bound_of_positive_certificate
    {n d C : ℕ} {U R : ℝ}
    (hindex : (d : ℝ) = (delta n : ℝ) + (C : ℝ) * U + R)
    (hC : 0 < C)
    (hU : 0 < U)
    (hR : 0 ≤ R) :
    delta n + 1 ≤ d := by
  have hC' : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hC
  have hCU : 0 < (C : ℝ) * U := mul_pos hC' hU
  have hstrict : (delta n : ℝ) < (d : ℝ) := by
    nlinarith
  have hstrictNat : delta n < d := by exact_mod_cast hstrict
  omega

/- The same transfer with the printed coefficient substituted. -/
theorem lower_bound_of_printed_certificate
    {n d : ℕ} {U R : ℝ}
    (hindex : (d : ℝ) = (delta n : ℝ) + (scalarCoefficient n : ℝ) * U + R)
    (hn : 0 < n)
    (hU : 0 < U)
    (hR : 0 ≤ R) :
    delta n + 1 ≤ d := by
  exact lower_bound_of_positive_certificate hindex (scalarCoefficient_pos hn) hU hR

theorem delta_values_2_to_10 :
    delta 2 = 5 ∧ delta 3 = 4 ∧ delta 4 = 7 ∧ delta 5 = 6 ∧
      delta 6 = 9 ∧ delta 7 = 8 ∧ delta 8 = 11 ∧ delta 9 = 10 ∧
      delta 10 = 13 := by
  norm_num [delta]

theorem scalarCoefficient_values_2_to_10 :
    scalarCoefficient 2 = 16 ∧ scalarCoefficient 3 = 32 ∧
      scalarCoefficient 4 = 48 ∧ scalarCoefficient 5 = 72 ∧
      scalarCoefficient 6 = 96 ∧ scalarCoefficient 7 = 128 ∧
      scalarCoefficient 8 = 160 ∧ scalarCoefficient 9 = 200 ∧
      scalarCoefficient 10 = 240 := by
  norm_num [scalarCoefficient]

theorem baseRealDimension_values_2_to_10 :
    baseRealDimension 2 = 8 ∧ baseRealDimension 3 = 12 ∧
      baseRealDimension 4 = 16 ∧ baseRealDimension 5 = 20 ∧
      baseRealDimension 6 = 24 ∧ baseRealDimension 7 = 28 ∧
      baseRealDimension 8 = 32 ∧ baseRealDimension 9 = 36 ∧
      baseRealDimension 10 = 40 := by
  norm_num [baseRealDimension]

theorem twistorComplexDimension_values_2_to_10 :
    twistorComplexDimension 2 = 5 ∧ twistorComplexDimension 3 = 7 ∧
      twistorComplexDimension 4 = 9 ∧ twistorComplexDimension 5 = 11 ∧
      twistorComplexDimension 6 = 13 ∧ twistorComplexDimension 7 = 15 ∧
      twistorComplexDimension 8 = 17 ∧ twistorComplexDimension 9 = 19 ∧
      twistorComplexDimension 10 = 21 := by
  norm_num [twistorComplexDimension]

theorem numerical_lower_bound_values_2_to_10 :
    delta 2 + 1 = 6 ∧ delta 3 + 1 = 5 ∧ delta 4 + 1 = 8 ∧
      delta 5 + 1 = 7 ∧ delta 6 + 1 = 10 ∧ delta 7 + 1 = 9 ∧
      delta 8 + 1 = 12 ∧ delta 9 + 1 = 11 ∧ delta 10 + 1 = 14 := by
  norm_num [delta]

/- These are conditional arithmetic corollaries of the preceding transfer
   lemma.  The real variables make the volume and any other nonnegative
   certificate terms explicit; no geometric fact is hidden in these results. -/
theorem printed_certificate_bound_2
    {d : ℕ} {U R : ℝ}
    (hindex : (d : ℝ) = (delta 2 : ℝ) + (scalarCoefficient 2 : ℝ) * U + R)
    (hU : 0 < U) (hR : 0 ≤ R) : 6 ≤ d := by
  have h := lower_bound_of_printed_certificate (n := 2) hindex (by norm_num) hU hR
  norm_num [delta] at h ⊢
  exact h

theorem printed_certificate_bound_3
    {d : ℕ} {U R : ℝ}
    (hindex : (d : ℝ) = (delta 3 : ℝ) + (scalarCoefficient 3 : ℝ) * U + R)
    (hU : 0 < U) (hR : 0 ≤ R) : 5 ≤ d := by
  have h := lower_bound_of_printed_certificate (n := 3) hindex (by norm_num) hU hR
  norm_num [delta] at h ⊢
  exact h

theorem printed_certificate_bound_4
    {d : ℕ} {U R : ℝ}
    (hindex : (d : ℝ) = (delta 4 : ℝ) + (scalarCoefficient 4 : ℝ) * U + R)
    (hU : 0 < U) (hR : 0 ≤ R) : 8 ≤ d := by
  have h := lower_bound_of_printed_certificate (n := 4) hindex (by norm_num) hU hR
  norm_num [delta] at h ⊢
  exact h

theorem printed_certificate_bound_5
    {d : ℕ} {U R : ℝ}
    (hindex : (d : ℝ) = (delta 5 : ℝ) + (scalarCoefficient 5 : ℝ) * U + R)
    (hU : 0 < U) (hR : 0 ≤ R) : 7 ≤ d := by
  have h := lower_bound_of_printed_certificate (n := 5) hindex (by norm_num) hU hR
  norm_num [delta] at h ⊢
  exact h

theorem printed_certificate_bound_6
    {d : ℕ} {U R : ℝ}
    (hindex : (d : ℝ) = (delta 6 : ℝ) + (scalarCoefficient 6 : ℝ) * U + R)
    (hU : 0 < U) (hR : 0 ≤ R) : 10 ≤ d := by
  have h := lower_bound_of_printed_certificate (n := 6) hindex (by norm_num) hU hR
  norm_num [delta] at h ⊢
  exact h

theorem printed_certificate_bound_7
    {d : ℕ} {U R : ℝ}
    (hindex : (d : ℝ) = (delta 7 : ℝ) + (scalarCoefficient 7 : ℝ) * U + R)
    (hU : 0 < U) (hR : 0 ≤ R) : 9 ≤ d := by
  have h := lower_bound_of_printed_certificate (n := 7) hindex (by norm_num) hU hR
  norm_num [delta] at h ⊢
  exact h

theorem printed_certificate_bound_8
    {d : ℕ} {U R : ℝ}
    (hindex : (d : ℝ) = (delta 8 : ℝ) + (scalarCoefficient 8 : ℝ) * U + R)
    (hU : 0 < U) (hR : 0 ≤ R) : 12 ≤ d := by
  have h := lower_bound_of_printed_certificate (n := 8) hindex (by norm_num) hU hR
  norm_num [delta] at h ⊢
  exact h

theorem printed_certificate_bound_9
    {d : ℕ} {U R : ℝ}
    (hindex : (d : ℝ) = (delta 9 : ℝ) + (scalarCoefficient 9 : ℝ) * U + R)
    (hU : 0 < U) (hR : 0 ≤ R) : 11 ≤ d := by
  have h := lower_bound_of_printed_certificate (n := 9) hindex (by norm_num) hU hR
  norm_num [delta] at h ⊢
  exact h

theorem printed_certificate_bound_10
    {d : ℕ} {U R : ℝ}
    (hindex : (d : ℝ) = (delta 10 : ℝ) + (scalarCoefficient 10 : ℝ) * U + R)
    (hU : 0 < U) (hR : 0 ≤ R) : 14 ≤ d := by
  have h := lower_bound_of_printed_certificate (n := 10) hindex (by norm_num) hU hR
  norm_num [delta] at h ⊢
  exact h

theorem printed_certificate_implies_gt_three_5_to_10
    {n d : ℕ} {U R : ℝ}
    (hn5 : 5 ≤ n) (hn10 : n ≤ 10)
    (hindex : (d : ℝ) = (delta n : ℝ) + (scalarCoefficient n : ℝ) * U + R)
    (hU : 0 < U) (hR : 0 ≤ R) : 3 < d := by
  have hbound := lower_bound_of_printed_certificate hindex (by omega) hU hR
  have hdelta : 4 ≤ delta n := by
    by_cases h : n % 2 = 0
    · rw [delta_even h]
      omega
    · rw [delta_odd h]
      omega
  omega

end QuaternionicSymmetry
