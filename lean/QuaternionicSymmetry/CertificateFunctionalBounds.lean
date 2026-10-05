import QuaternionicSymmetry.AlgebraCertificates
import Mathlib.Tactic

/-!
Linear-functional lower bounds obtained from the universal certificate
identities.  The hypotheses below state nonnegativity separately for every
complete top-weight polynomial term.  No positivity is asserted for arbitrary
polynomials and no geometric interpretation of the functional is assumed.
-/

namespace QuaternionicSymmetry.CertificateFunctionalBounds

open QuaternionicSymmetry.AlgebraCertificates

noncomputable section

variable {L : P →ₗ[ℚ] ℝ}

private theorem map_c_mul (q : ℚ) (p : P) :
    L (c q * p) = (q : ℝ) * L p := by
  change L (MvPolynomial.C q * p) = (q : ℝ) * L p
  rw [← MvPolynomial.smul_eq_C_mul, L.map_smul]
  rfl

private theorem map_c_mul_mul (q : ℚ) (p r : P) :
    L ((c q * p) * r) = (q : ℝ) * L (p * r) := by
  rw [mul_assoc, map_c_mul]

theorem lower_bound_2 : (16 : ℝ) * L (U ^ 2) ≤ L K₂ := by
  rw [polynomial_certificate₂, RHS₂, map_c_mul]
  norm_num

theorem lower_bound_3 (hZ : 0 ≤ L (Z₁ * U ^ 2)) :
    (32 : ℝ) * L (U ^ 3) ≤ L K₃ := by
  rw [polynomial_certificate₃]
  simp only [RHS₃, map_add, map_c_mul, map_c_mul_mul]
  linarith

theorem lower_bound_4 (hZ : 0 ≤ L (Z₁ * U ^ 3)) :
    (48 : ℝ) * L (U ^ 4) ≤ L K₄ := by
  rw [polynomial_certificate₄]
  simp only [RHS₄, map_add, map_c_mul, map_c_mul_mul]
  linarith

/-- Dimension five: the leading certificate term dominates under the stated signs. -/
theorem lower_bound_5
    (hZ : 0 ≤ L (Z₁ * U ^ 4))
    (hF : 0 ≤ L (F₂ * U ^ 3)) :
    (72 : ℝ) * L (U ^ 5) ≤ L K₅ := by
  rw [polynomial_certificate₅]
  simp only [RHS₅, map_add, map_c_mul, map_c_mul_mul]
  linarith

theorem strict_positive_5
    (hU : 0 < L (U ^ 5))
    (hZ : 0 ≤ L (Z₁ * U ^ 4))
    (hF : 0 ≤ L (F₂ * U ^ 3)) :
    0 < L K₅ := by
  exact lt_of_lt_of_le (mul_pos (by norm_num) hU) (lower_bound_5 hZ hF)

/-- Dimension six: the leading certificate term dominates under the stated signs. -/
theorem lower_bound_6
    (hZ : 0 ≤ L (Z₁ * U ^ 5))
    (hF : 0 ≤ L (F₂ * U ^ 4)) :
    (96 : ℝ) * L (U ^ 6) ≤ L K₆ := by
  rw [polynomial_certificate₆]
  simp only [RHS₆, map_add, map_c_mul, map_c_mul_mul]
  linarith

theorem strict_positive_6
    (hU : 0 < L (U ^ 6))
    (hZ : 0 ≤ L (Z₁ * U ^ 5))
    (hF : 0 ≤ L (F₂ * U ^ 4)) :
    0 < L K₆ := by
  exact lt_of_lt_of_le (mul_pos (by norm_num) hU) (lower_bound_6 hZ hF)

/-- Dimension seven: every displayed remainder generator has its own sign hypothesis. -/
theorem lower_bound_7
    (hZ : 0 ≤ L (Z₁ * U ^ 6))
    (hM : 0 ≤ L (M₂₁ 16 * U ^ 5))
    (hZ2 : 0 ≤ L (Z₁ ^ 2 * U ^ 5))
    (hF : 0 ≤ L (F₃ * U ^ 4)) :
    (128 : ℝ) * L (U ^ 7) ≤ L K₇ := by
  rw [polynomial_certificate₇]
  simp only [RHS₇, map_add, add_mul, map_c_mul, map_c_mul_mul]
  linarith

theorem strict_positive_7
    (hU : 0 < L (U ^ 7))
    (hZ : 0 ≤ L (Z₁ * U ^ 6))
    (hM : 0 ≤ L (M₂₁ 16 * U ^ 5))
    (hZ2 : 0 ≤ L (Z₁ ^ 2 * U ^ 5))
    (hF : 0 ≤ L (F₃ * U ^ 4)) :
    0 < L K₇ := by
  exact lt_of_lt_of_le (mul_pos (by norm_num) hU) (lower_bound_7 hZ hM hZ2 hF)

/-- Dimension eight: every displayed remainder generator has its own sign hypothesis. -/
theorem lower_bound_8
    (hZ : 0 ≤ L (Z₁ * U ^ 7))
    (hM : 0 ≤ L (M₂₁ 18 * U ^ 6))
    (hZ2 : 0 ≤ L (Z₁ ^ 2 * U ^ 6))
    (hF : 0 ≤ L (F₃ * U ^ 5)) :
    (160 : ℝ) * L (U ^ 8) ≤ L K₈ := by
  rw [polynomial_certificate₈]
  simp only [RHS₈, map_add, add_mul, map_c_mul, map_c_mul_mul]
  linarith

theorem strict_positive_8
    (hU : 0 < L (U ^ 8))
    (hZ : 0 ≤ L (Z₁ * U ^ 7))
    (hM : 0 ≤ L (M₂₁ 18 * U ^ 6))
    (hZ2 : 0 ≤ L (Z₁ ^ 2 * U ^ 6))
    (hF : 0 ≤ L (F₃ * U ^ 5)) :
    0 < L K₈ := by
  exact lt_of_lt_of_le (mul_pos (by norm_num) hU) (lower_bound_8 hZ hM hZ2 hF)

/-- Dimension nine: every displayed remainder generator has its own sign hypothesis. -/
theorem lower_bound_9
    (hZ : 0 ≤ L (Z₁ * U ^ 8))
    (hM : 0 ≤ L (M₂₁ 20 * U ^ 7))
    (hZ2 : 0 ≤ L (Z₁ ^ 2 * U ^ 7))
    (hM31 : 0 ≤ L (M₃₁ 20 * U ^ 6))
    (hM32 : 0 ≤ L (M₃₂ 20 * U ^ 6))
    (hZ3 : 0 ≤ L (Z₁ ^ 3 * U ^ 6))
    (hF : 0 ≤ L (F₄ * U ^ 5)) :
    (200 : ℝ) * L (U ^ 9) ≤ L K₉ := by
  rw [polynomial_certificate₉]
  simp only [RHS₉, map_add, add_mul, map_c_mul, map_c_mul_mul]
  linarith

theorem strict_positive_9
    (hU : 0 < L (U ^ 9))
    (hZ : 0 ≤ L (Z₁ * U ^ 8))
    (hM : 0 ≤ L (M₂₁ 20 * U ^ 7))
    (hZ2 : 0 ≤ L (Z₁ ^ 2 * U ^ 7))
    (hM31 : 0 ≤ L (M₃₁ 20 * U ^ 6))
    (hM32 : 0 ≤ L (M₃₂ 20 * U ^ 6))
    (hZ3 : 0 ≤ L (Z₁ ^ 3 * U ^ 6))
    (hF : 0 ≤ L (F₄ * U ^ 5)) :
    0 < L K₉ := by
  exact lt_of_lt_of_le (mul_pos (by norm_num) hU)
    (lower_bound_9 hZ hM hZ2 hM31 hM32 hZ3 hF)

/-- Dimension ten: every displayed remainder generator has its own sign hypothesis. -/
theorem lower_bound_10
    (hZ : 0 ≤ L (Z₁ * U ^ 9))
    (hM : 0 ≤ L (M₂₁ 22 * U ^ 8))
    (hZ2 : 0 ≤ L (Z₁ ^ 2 * U ^ 8))
    (hM31 : 0 ≤ L (M₃₁ 22 * U ^ 7))
    (hM32 : 0 ≤ L (M₃₂ 22 * U ^ 7))
    (hZ3 : 0 ≤ L (Z₁ ^ 3 * U ^ 7))
    (hF : 0 ≤ L (F₄ * U ^ 6)) :
    (240 : ℝ) * L (U ^ 10) ≤ L K₁₀ := by
  rw [polynomial_certificate₁₀]
  simp only [RHS₁₀, map_add, add_mul, map_c_mul, map_c_mul_mul]
  linarith

theorem strict_positive_10
    (hU : 0 < L (U ^ 10))
    (hZ : 0 ≤ L (Z₁ * U ^ 9))
    (hM : 0 ≤ L (M₂₁ 22 * U ^ 8))
    (hZ2 : 0 ≤ L (Z₁ ^ 2 * U ^ 8))
    (hM31 : 0 ≤ L (M₃₁ 22 * U ^ 7))
    (hM32 : 0 ≤ L (M₃₂ 22 * U ^ 7))
    (hZ3 : 0 ≤ L (Z₁ ^ 3 * U ^ 7))
    (hF : 0 ≤ L (F₄ * U ^ 6)) :
    0 < L K₁₀ := by
  exact lt_of_lt_of_le (mul_pos (by norm_num) hU)
    (lower_bound_10 hZ hM hZ2 hM31 hM32 hZ3 hF)

end
end QuaternionicSymmetry.CertificateFunctionalBounds
