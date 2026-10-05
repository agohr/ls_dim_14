import QuaternionicSymmetry.PSDQuarticTargetSeparators

/-!
# Quaternionic zonal quartic moments and the PSD separators

The five `C_λ` below are the C-normalized quaternionic zonal polynomials
(Jack parameter `α = 1/2`) in the ordered power-sum basis
`p₁⁴, p₁²p₂, p₂², p₁p₃, p₄`. Their independent monomial-symmetric coefficients
are those of Li--Xue, *Zonal polynomials and hypergeometric functions of
quaternion matrix argument*, arXiv:0901.3379, Table on p. 8. The normalized
product formula used for `moment` is their Theorem 3.3. We retain its
quaternionic trace normalization: `p_j` is the power sum of the `n`
quaternionic eigenvalues, or half the complex trace `z_j` in the textbook.

This module checks the complete symbolic quartic identity in a rational
polynomial ring. It does not establish the analytic quaternionic Haar integral
or the reduction from arbitrary complex PSD matrices; those remain geometric
interpretation obligations.
-/

namespace QuaternionicSymmetry.PSDQuarticZonal

open MvPolynomial PSDQuarticTargetSeparators

noncomputable section

abbrev Spectrum := MvPolynomial (Fin 4) ℚ
abbrev Moment := MvPolynomial (Fin 4) Spectrum

/-- C-normalized Jack/zonal functions in the five quartic power sums. -/
def c4 : Fin 5 → ℚ := ![2/15, 2/5, 1/10, 4/15, 1/10]
def c31 : Fin 5 → ℚ := ![8/15, 4/15, -4/15, -4/15, -4/15]
def c22 : Fin 5 → ℚ := ![2/15, -2/15, 7/30, -4/15, 1/30]
def c211 : Fin 5 → ℚ := ![4/21, -10/21, -2/21, 4/21, 4/21]
def c1111 : Fin 5 → ℚ := ![1/105, -2/35, 1/35, 8/105, -2/35]

/-- Ordinary monomial symmetric functions, in the same power-sum basis. -/
def m4 : Fin 5 → ℚ := ![0, 0, 0, 0, 1]
def m31 : Fin 5 → ℚ := ![0, 0, 0, 1, -1]
def m22 : Fin 5 → ℚ := ![0, 0, 1/2, 0, -1/2]
def m211 : Fin 5 → ℚ := ![0, 1/2, -1/2, -1, 1]
def m1111 : Fin 5 → ℚ := ![1/24, -1/4, 1/8, 1/3, -1/4]

/-- Verify all five rows of the primary-source monomial coefficient table. -/
theorem zonal_monomial_table :
    c4 = (fun i => m4 i + 8/5 * m31 i + 9/5 * m22 i +
      12/5 * m211 i + 16/5 * m1111 i) ∧
    c31 = (fun i => 12/5 * m31 i + 16/5 * m22 i +
      104/15 * m211 i + 64/5 * m1111 i) ∧
    c22 = (fun i => m22 i + 4/3 * m211 i + 16/5 * m1111 i) ∧
    c211 = (fun i => 4/3 * m211 i + 32/7 * m1111 i) ∧
    c1111 = (fun i => 8/35 * m1111 i) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals
    funext i
    fin_cases i <;> norm_num [c4, c31, c22, c211, c1111,
      m4, m31, m22, m211, m1111, Matrix.cons_val]

/-- The C-normalization is `Σ_{λ⊢4} C_λ = p₁⁴`. -/
theorem zonal_sum :
    quartic c4 + quartic c31 + quartic c22 + quartic c211 + quartic c1111 =
      (X 0 : Spectrum) ^ 4 := by
  apply MvPolynomial.funext
  intro v
  simp [quartic, c4, c31, c22, c211, c1111]
  ring

/-- Jack's power-sum inner product at `α=1/2` in this ordered basis. -/
def jackInner (a b : Fin 5 → ℚ) : ℚ :=
  3/2 * a 0 * b 0 + 1/2 * a 1 * b 1 + 2 * a 2 * b 2 +
    3/4 * a 3 * b 3 + 2 * a 4 * b 4

/-- The five sourced C-polynomials are pairwise orthogonal for the
quaternionic Jack inner product, independently of the separator identities. -/
theorem zonal_orthogonal :
    jackInner c4 c31 = 0 ∧ jackInner c4 c22 = 0 ∧
    jackInner c4 c211 = 0 ∧ jackInner c4 c1111 = 0 ∧
    jackInner c31 c22 = 0 ∧ jackInner c31 c211 = 0 ∧
    jackInner c31 c1111 = 0 ∧ jackInner c22 c211 = 0 ∧
    jackInner c22 c1111 = 0 ∧ jackInner c211 c1111 = 0 := by
  dsimp [jackInner, c4, c31, c22, c211, c1111, Fin.cons]
  norm_num

/-- Evaluation at `1^n`: each spectral power sum equals `n`. -/
def zonalNorm (n : ℕ) (c : Fin 5 → ℚ) : ℚ :=
  c 0 * n ^ 4 + c 1 * n ^ 3 + c 2 * n ^ 2 + c 3 * n ^ 2 + c 4 * n

theorem norms11 :
    zonalNorm 11 c4 = 2530 ∧ zonalNorm 11 c31 = 8096 ∧
    zonalNorm 11 c22 = 1771 ∧ zonalNorm 11 c211 = 15180/7 ∧
    zonalNorm 11 c1111 = 528/7 := by
  dsimp [zonalNorm, c4, c31, c22, c211, c1111, Fin.cons]
  norm_num

theorem norms12 :
    zonalNorm 12 c4 = 3510 ∧ zonalNorm 12 c31 = 11440 ∧
    zonalNorm 12 c22 = 2530 ∧ zonalNorm 12 c211 = 22000/7 ∧
    zonalNorm 12 c1111 = 792/7 := by
  dsimp [zonalNorm, c4, c31, c22, c211, c1111, Fin.cons]
  norm_num

/-- The universal `n`-dimensional quaternionic zonal moment coefficients:
`Σ C_λ(a) C_λ(p)/C_λ(1^n)`. The definition is independent of the two
separating functionals. -/
def momentCoefficient (n : ℕ) (i : Fin 5) : Spectrum :=
  C (c4 i / zonalNorm n c4) * quartic c4 +
  C (c31 i / zonalNorm n c31) * quartic c31 +
  C (c22 i / zonalNorm n c22) * quartic c22 +
  C (c211 i / zonalNorm n c211) * quartic c211 +
  C (c1111 i / zonalNorm n c1111) * quartic c1111

/-- The full quartic polynomial in `p_j`, with polynomial coefficients in
the independent spectral power sums `A_j`. -/
def moment (n : ℕ) : Moment :=
  C (momentCoefficient n 0) * X 0 ^ 4 +
  C (momentCoefficient n 1) * X 0 ^ 2 * X 1 +
  C (momentCoefficient n 2) * X 1 ^ 2 +
  C (momentCoefficient n 3) * X 0 * X 2 +
  C (momentCoefficient n 4) * X 3

/-- Coefficient pairing with a quartic functional is exactly its action on
`moment`, whose five coefficients are given above. -/
def separatorOnMoment (n : ℕ) (v : Fin 5 → ℚ) : Spectrum :=
  C (v 0) * momentCoefficient n 0 + C (v 1) * momentCoefficient n 1 +
  C (v 2) * momentCoefficient n 2 + C (v 3) * momentCoefficient n 3 +
  C (v 4) * momentCoefficient n 4

/-- Chapter 8's dimension-eleven PSD separator is a square on an arbitrary
formal spectrum, without specializing `A₁,…,A₄` to sample matrices. -/
theorem P11_zonal_square :
    separatorOnMoment 11 P11 =
      C (1 / 55) * (9 * X 1 - 4 * X 0 ^ 2) ^ 2 := by
  apply MvPolynomial.funext
  intro v
  simp [separatorOnMoment, momentCoefficient, zonalNorm,
    P11, c4, c31, c22, c211, c1111, quartic]
  ring

/-- The corresponding dimension-twelve square identity. -/
theorem P12_zonal_square :
    separatorOnMoment 12 P12 =
      C (1 / 8) * (7 * X 1 - 3 * X 0 ^ 2) ^ 2 := by
  apply MvPolynomial.funext
  intro v
  simp [separatorOnMoment, momentCoefficient, zonalNorm,
    P12, c4, c31, c22, c211, c1111, quartic]
  ring

/-- The symbolic identities survive evaluation in any commutative rational
algebra, including algebras with nilpotents. -/
theorem P11_zonal_square_eval {R : Type*} [CommRing R] [Algebra ℚ R]
    (a : Fin 4 → R) :
    aeval a (separatorOnMoment 11 P11) =
      algebraMap ℚ R (1 / 55) * (9 * a 1 - 4 * a 0 ^ 2) ^ 2 := by
  rw [P11_zonal_square]
  simp

theorem P12_zonal_square_eval {R : Type*} [CommRing R] [Algebra ℚ R]
    (a : Fin 4 → R) :
    aeval a (separatorOnMoment 12 P12) =
      algebraMap ℚ R (1 / 8) * (7 * a 1 - 3 * a 0 ^ 2) ^ 2 := by
  rw [P12_zonal_square]
  simp

/-- These exact polynomial generators have nonnegative separator values at
every real spectrum. No assumption on the signs of the spectrum entries is
needed for the square identity itself. -/
theorem P11_zonal_nonneg (a : Fin 4 → ℝ) :
    0 ≤ aeval a (separatorOnMoment 11 P11) := by
  rw [P11_zonal_square_eval]
  positivity

theorem P12_zonal_nonneg (a : Fin 4 → ℝ) :
    0 ≤ aeval a (separatorOnMoment 12 P12) := by
  rw [P12_zonal_square_eval]
  positivity

end
end QuaternionicSymmetry.PSDQuarticZonal
