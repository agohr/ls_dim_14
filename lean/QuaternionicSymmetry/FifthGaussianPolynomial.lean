import QuaternionicSymmetry.WeightFiveAhat
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Tactic

/-! The universal fifth Gaussian coefficient printed in Chapter 6.

This is an equality of rational polynomials in the reduced power sums
`p₁,…,p₅`; it has no probabilistic or curvature-form interpretation built in.
-/

namespace QuaternionicSymmetry.FifthGaussianPolynomial

open MvPolynomial

noncomputable section

abbrev P := MvPolynomial (Fin 5) ℚ

def p1 : P := X 0
def p2 : P := X 1
def p3 : P := X 2
def p4 : P := X 3
def p5 : P := X 4

/-- The pure Weyl logarithmic coefficients: `z_j=2p_j`, `u=0`. -/
def b1 : P := C (1 / 12) * p1
def b2 : P := C (1 / 1440) * p2
def b3 : P := C (1 / 90720) * p3
def b4 : P := C (1 / 4838400) * p4
def b5 : P := C (1 / 239500800) * p5

/-- The expanded fifth exponential coefficient from the Chapter 6 recurrence. -/
def F5 : P :=
  b5 + b1 * b4 + b2 * b3 + C (1 / 2) * b1 ^ 2 * b3 +
    C (1 / 2) * b1 * b2 ^ 2 + C (1 / 6) * b1 ^ 3 * b2 +
    C (1 / 120) * b1 ^ 5

theorem F5_printed :
    F5 = C (1 / 11496038400) *
      (C 385 * p1 ^ 5 + C 770 * p1 ^ 3 * p2 + C 440 * p1 ^ 2 * p3 +
       C 231 * p1 * p2 ^ 2 + C 198 * p1 * p4 +
       C 88 * p2 * p3 + C 48 * p5) := by
  apply MvPolynomial.funext
  intro v
  simp [F5, b1, b2, b3, b4, b5, p1, p2, p3, p4, p5]
  ring

/-- Every rational coefficient displayed in the seven-term formula is
strictly positive; this arithmetic fact does not assert positivity after
substituting arbitrary power sums. -/
theorem F5_printed_coefficients_positive :
    (0 : ℚ) < 1 / 11496038400 ∧
    (0 : ℚ) < 385 ∧ (0 : ℚ) < 770 ∧ (0 : ℚ) < 440 ∧
    (0 : ℚ) < 231 ∧ (0 : ℚ) < 198 ∧ (0 : ℚ) < 88 ∧
    (0 : ℚ) < 48 := by
  norm_num

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The same fifth coefficient specializes to any commutative rational
algebra, including algebras with nilpotents. -/
theorem F5_evaluate (v : Fin 5 → R) :
    aeval v F5 =
      (algebraMap ℚ R (1 / 11496038400)) *
        (385 * v 0 ^ 5 + 770 * v 0 ^ 3 * v 1 + 440 * v 0 ^ 2 * v 2 +
         231 * v 0 * v 1 ^ 2 + 198 * v 0 * v 3 +
         88 * v 1 * v 2 + 48 * v 4) := by
  rw [F5_printed]
  simp [p1, p2, p3, p4, p5, map_add, map_mul, map_pow]
  simp only [_root_.map_ofNat]

theorem F5_rational_recurrence (v : Fin 5 → ℚ) :
    aeval v F5 =
      LogAhat.A5 (v 0 / 12) (v 1 / 1440) (v 2 / 90720)
        (v 3 / 4838400) (v 4 / 239500800) := by
  simp [F5, b1, b2, b3, b4, b5, p1, p2, p3, p4, p5,
    LogAhat.A5, div_eq_mul_inv]
  ring

end
end QuaternionicSymmetry.FifthGaussianPolynomial
