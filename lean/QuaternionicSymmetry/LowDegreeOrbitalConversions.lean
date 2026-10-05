import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Tactic

/-! Exact low-degree projection-to-orbital formulas from Chapter 8.
The statements are rational-polynomial identities. The symplectic Haar
interpretation and the pointwise sign of an orbital are not assumed here. -/

namespace QuaternionicSymmetry.LowDegreeOrbitalConversions

open MvPolynomial
noncomputable section

abbrev P := MvPolynomial (Fin 2) ℚ
def p1 : P := X 0
def p2 : P := X 1

/-- The first two finite type-C orbitals at the spectra `e₁` and `e_n`. -/
def orbital1 (n : ℚ) : P :=
  C (2 / (n * (2 * n + 1))) * p1

def orbital2One (n : ℚ) : P :=
  C (2 / (n * (n + 1) * (2 * n + 1) * (2 * n + 3))) *
    (p1 ^ 2 + p2)

def orbital2Full (n : ℚ) : P :=
  C (2 / ((2 * n - 1) * (2 * n + 1) * (2 * n + 3))) *
    (C (2 * n + 1) * p1 ^ 2 - 2 * p2)

/-- Schur--Weyl projection polynomials with ambient complex rank `2n+2`
and projection rank `ell`, in the convention `z_j=2p_j`. -/
def projection1 (n ell : ℚ) : P :=
  C (ell / (n + 1)) * p1

def projection2 (n ell : ℚ) : P :=
  C (ell * (ell + 1) / ((2 * n + 2) * (2 * n + 3))) *
      (2 * p1 ^ 2 + p2) +
  C (ell * (ell - 1) / ((2 * n + 2) * (2 * n + 1))) *
      (2 * p1 ^ 2 - p2)

def coefficientA (n ell : ℚ) : ℚ :=
  ell * n * (6 * ell * n + 7 * ell + 4 * n ^ 2 + 6 * n - 2) /
    (2 * (2 * n + 3))

def coefficientB (n ell : ℚ) : ℚ :=
  ell * (2 * n - 1) * (4 * ell * n + 5 * ell - 2 * n - 4) /
    (2 * (n + 1) * (2 * n + 3))

private theorem denominator_signs (n : ℚ) (hn : 2 ≤ n) :
    0 < n ∧ 0 < n + 1 ∧ 0 < 2 * n - 1 ∧ 0 < 2 * n + 1 ∧
    0 < 2 * n + 2 ∧ 0 < 2 * n + 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem projection1_orbital (n ell : ℚ) (hn : 2 ≤ n) :
    projection1 n ell =
      C (ell * n * (2 * n + 1) / (2 * (n + 1))) * orbital1 n := by
  obtain ⟨hn0, hn1, _, hn2, _, _⟩ := denominator_signs n hn
  apply MvPolynomial.funext
  intro v
  simp [projection1, orbital1, p1]
  field_simp

theorem projection1_coefficient_pos (n ell : ℚ)
    (hn : 2 ≤ n) (hell : 1 ≤ ell) :
    0 < ell * n * (2 * n + 1) / (2 * (n + 1)) := by
  have hn0 : 0 < n := by linarith
  have hn1 : 0 < n + 1 := by linarith
  have hn2 : 0 < 2 * n + 1 := by linarith
  have hell0 : 0 < ell := by linarith
  positivity

theorem projection2_orbital (n ell : ℚ) (hn : 2 ≤ n) :
    projection2 n ell =
      C (coefficientA n ell) * orbital2One n +
      C (coefficientB n ell) * orbital2Full n := by
  obtain ⟨hn0, hn1, hnm1, hn2, hnr, hnr1⟩ := denominator_signs n hn
  apply MvPolynomial.funext
  intro v
  simp [projection2, orbital2One, orbital2Full, coefficientA,
    coefficientB, p1, p2]
  field_simp
  ring

theorem coefficientA_pos (n ell : ℚ) (hn : 2 ≤ n) (hell : 1 ≤ ell) :
    0 < coefficientA n ell := by
  unfold coefficientA
  have hfactor : 0 < 6 * ell * n + 7 * ell + 4 * n ^ 2 + 6 * n - 2 := by
    nlinarith [sq_nonneg n]
  have hnm1 : 0 < 2 * n - 1 := by linarith
  have hnp1 : 0 < n + 1 := by linarith
  have hnp3 : 0 < 2 * n + 3 := by linarith
  have hell0 : 0 < ell := by linarith
  positivity

theorem coefficientB_pos (n ell : ℚ) (hn : 2 ≤ n) (hell : 1 ≤ ell) :
    0 < coefficientB n ell := by
  unfold coefficientB
  have hfactor : 0 < 4 * ell * n + 5 * ell - 2 * n - 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hell) (show (0 : ℚ) ≤ 4 * n + 5 by linarith)]
  have hnm1 : 0 < 2 * n - 1 := by linarith
  have hnp1 : 0 < n + 1 := by linarith
  have hnp3 : 0 < 2 * n + 3 := by linarith
  have hell0 : 0 < ell := by linarith
  positivity

/-- The first two Gaussian coefficient polynomials in the same power-sum
normalization. -/
def gaussian1 : P := C (1 / 12) * p1
def gaussian2 : P := C (1 / 1440) * (5 * p1 ^ 2 + p2)

theorem gaussian1_orbital (n : ℚ) (hn : 2 ≤ n) :
    gaussian1 = C (n * (2 * n + 1) / 24) * orbital1 n := by
  obtain ⟨hn0, _, _, hn2, _, _⟩ := denominator_signs n hn
  apply MvPolynomial.funext
  intro v
  simp [gaussian1, orbital1, p1]
  field_simp
  ring

theorem gaussian1_coefficient_pos (n : ℚ) (hn : 2 ≤ n) :
    0 < n * (2 * n + 1) / 24 := by
  have hn0 : 0 < n := by linarith
  have hn2 : 0 < 2 * n + 1 := by linarith
  positivity

theorem gaussian2_orbital (n : ℚ) (hn : 2 ≤ n) :
    gaussian2 =
      C (n * (n + 1) * (2 * n + 1) * (2 * n + 11) / 2880) *
        orbital2One n +
      C ((2 * n - 1) * (2 * n + 1) / 720) *
        orbital2Full n := by
  obtain ⟨hn0, hn1, hnm1, hn2, _, hnr1⟩ := denominator_signs n hn
  apply MvPolynomial.funext
  intro v
  simp [gaussian2, orbital2One, orbital2Full, p1, p2]
  have hnm1' : -1 + n * 2 ≠ 0 := by nlinarith
  field_simp [hnm1']
  ring_nf
  field_simp [hnm1']
  ring

theorem gaussian2_coefficients_pos (n : ℚ) (hn : 2 ≤ n) :
    0 < n * (n + 1) * (2 * n + 1) * (2 * n + 11) / 2880 ∧
    0 < (2 * n - 1) * (2 * n + 1) / 720 := by
  have hnm1 : 0 < 2 * n - 1 := by linarith
  have hnp1 : 0 < n + 1 := by linarith
  have hn2 : 0 < 2 * n + 1 := by linarith
  have hnp11 : 0 < 2 * n + 11 := by linarith
  have hn0 : 0 < n := by linarith
  constructor <;> positivity

end
end QuaternionicSymmetry.LowDegreeOrbitalConversions
