import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Tactic

/-! Chapter 6's Newton dictionary in the formal Chern variables
`c₂,c₄,c₆`. These are polynomial identities only. The names `C1`, `H2`,
and `S3` here stand for their integrands; no Chern class, integrated
characteristic number, or sign is constructed by this module. -/

namespace QuaternionicSymmetry.CharacteristicMomentDictionary

open MvPolynomial
noncomputable section

abbrev P := MvPolynomial (Fin 3) ℚ
def c2 : P := X 0
def c4 : P := X 1
def c6 : P := X 2

/-- Newton identities in the corrected standard-root convention. -/
def z1 : P := 2 * c2
def z2 : P := 2 * c2 ^ 2 - 4 * c4
def z3 : P := 2 * c2 ^ 3 - 6 * c2 * c4 + 6 * c6

def C1 : P := c2
def C2 : P := c2 ^ 2
def C3 : P := c2 ^ 3
def H2 : P := 3 * c2 ^ 2 - 2 * c4
def H3 : P := 2 * c2 ^ 3 - 3 * c2 * c4 + c6
def S3 : P := 10 * c2 ^ 3 - 9 * c2 * c4 + 2 * c6

def m1 (r ell : ℚ) : P := C (ell / r) * z1
def m2Full : P := z1 ^ 2
def m2One (r : ℚ) : P := C (1 / (r * (r + 1))) * (z1 ^ 2 + z2)
def m2 (r ell : ℚ) : P :=
  C (ell * (ell + 1) / (2 * r * (r + 1))) * (z1 ^ 2 + z2) +
  C (ell * (ell - 1) / (2 * r * (r - 1))) * (z1 ^ 2 - z2)
def m3Full : P := z1 ^ 3
def m3One (r : ℚ) : P :=
  C (1 / (r * (r + 1) * (r + 2))) *
    (z1 ^ 3 + 3 * z1 * z2 + 2 * z3)
def m3Two (r : ℚ) : P :=
  C (4 / (r * (r - 1) * (r + 1) * (r + 2))) *
    (C (2 * r + 1) * z1 ^ 3 + C (3 * (r - 1)) * z1 * z2 +
      C (r - 4) * z3)

theorem first_full (r : ℚ) (hr : 2 < r) : m1 r r = 2 * C1 := by
  have hr0 : r ≠ 0 := by linarith
  apply MvPolynomial.funext
  intro v
  simp [m1, C1, z1, c2]
  field_simp

theorem first_general (r ell : ℚ) (hr : 0 < r) :
    m1 r ell = C (2 * ell / r) * C1 := by
  have hr0 : r ≠ 0 := by linarith
  apply MvPolynomial.funext
  intro v
  simp [m1, C1, z1, c2]
  field_simp

theorem second_full : m2Full = 4 * C2 := by
  simp [m2Full, C2, z1, c2]
  ring

theorem second_one (r : ℚ) (hr : 2 < r) :
    m2One r = C (2 / (r * (r + 1))) * H2 := by
  have hr0 : r ≠ 0 := by linarith
  have hpr1 : r + 1 ≠ 0 := by linarith
  apply MvPolynomial.funext
  intro v
  simp [m2One, H2, z1, z2, c2, c4]
  field_simp
  ring

theorem second_general (r ell : ℚ) (hr : 2 < r) :
    m2 r ell =
      C (4 * ell * (ell - 1) / (r * (r - 1))) * C2 +
      C (2 * ell * (r - ell) / (r * (r - 1) * (r + 1))) * H2 := by
  have hr0 : r ≠ 0 := by linarith
  have hr1 : r - 1 ≠ 0 := by linarith
  have hpr1 : r + 1 ≠ 0 := by linarith
  apply MvPolynomial.funext
  intro v
  simp [m2, C2, H2, z1, z2, c2, c4]
  field_simp
  ring

theorem third_full : m3Full = 8 * C3 := by
  simp [m3Full, C3, z1, c2]
  ring

theorem third_one (r : ℚ) (hr : 2 < r) :
    m3One r = C (12 / (r * (r + 1) * (r + 2))) * H3 := by
  have hr0 : r ≠ 0 := by linarith
  have hpr1 : r + 1 ≠ 0 := by linarith
  have hpr2 : r + 2 ≠ 0 := by linarith
  apply MvPolynomial.funext
  intro v
  simp [m3One, H3, z1, z2, z3, c2, c4, c6]
  field_simp
  ring

theorem cubic_combination (r : ℚ) (hr : 2 < r) :
    S3 = C (3 / 16) * m3Full +
      C (r * (r + 1) * (r + 20) / 24) * m3One r +
      C (r * (r - 1) * (r + 1) / 16) * m3Two r := by
  have hr0 : r ≠ 0 := by linarith
  have hr1 : r - 1 ≠ 0 := by linarith
  have hpr1 : r + 1 ≠ 0 := by linarith
  have hpr2 : r + 2 ≠ 0 := by linarith
  apply MvPolynomial.funext
  intro v
  simp [S3, m3Full, m3One, m3Two, z1, z2, z3, c2, c4, c6]
  field_simp
  ring

end
end QuaternionicSymmetry.CharacteristicMomentDictionary
