import QuaternionicSymmetry.DimensionElevenTwelveDensity
import Mathlib.Algebra.MvPolynomial.Funext

/-!
The lower-weight projection-moment certificates in dimensions eleven and twelve.
The variables are the six independent rational-polynomial variables `u,p₁,…,p₅`
of `DimensionElevenTwelveDensity`; `z_j=2p_j` is imposed only by a polynomial
substitution. The quartic orbital and quintic Gaussian terms are retained
unchanged in the complete identities.
-/

namespace QuaternionicSymmetry.ElevenTwelveProjectionCertificates

open MvPolynomial
open DimensionElevenTwelveDensity

noncomputable section

abbrev P := DimensionElevenTwelveDensity.P

def z1 : P := 2 * p1
def z2 : P := 2 * p2
def z3 : P := 2 * p3

/-- The rank-`r` full projection moment in weight one. -/
def m1Full : P := z1

/-- The rank-one and full projection moments in weight two. -/
def m2One (r : ℚ) : P := C (1 / (r * (r + 1))) * (z1 ^ 2 + z2)
def m2Full : P := z1 ^ 2

/-- The three Schur functions of weight three, expressed in power sums. -/
def schur3 : P := C (1 / 6) * (z1 ^ 3 + C 3 * z1 * z2 + C 2 * z3)
def schur21 : P := C (1 / 3) * (z1 ^ 3 - z3)
def schur111 : P := C (1 / 6) * (z1 ^ 3 - C 3 * z1 * z2 + C 2 * z3)

/-- The exact Schur–Weyl rank-`ℓ` projection polynomial in weight three.
Its three coefficients are `f^λ s_λ(1^ℓ)/s_λ(1^r)` for the partitions of three. -/
def m3 (r ell : ℚ) : P :=
  C (ell * (ell + 1) * (ell + 2) / (r * (r + 1) * (r + 2))) * schur3
    + C (2 * ell * (ell - 1) * (ell + 1) / (r * (r - 1) * (r + 1))) * schur21
    + C (ell * (ell - 1) * (ell - 2) / (r * (r - 1) * (r - 2))) * schur111

/-- The Schur formula agrees with the existing rank-one quadratic interface. -/
theorem m2One_old_24 : m2One 24 = old (AlgebraCertificates.M₂₁ 24) := by
  apply MvPolynomial.funext
  intro v
  simp [m2One, old, AlgebraCertificates.M₂₁, AlgebraCertificates.evaluate,
    AlgebraCertificates.c, AlgebraCertificates.Z₁, AlgebraCertificates.Z₂,
    z1, z2, p1, p2, u]

theorem m2One_old_26 : m2One 26 = old (AlgebraCertificates.M₂₁ 26) := by
  apply MvPolynomial.funext
  intro v
  simp [m2One, old, AlgebraCertificates.M₂₁, AlgebraCertificates.evaluate,
    AlgebraCertificates.c, AlgebraCertificates.Z₁, AlgebraCertificates.Z₂,
    z1, z2, p1, p2, u]

theorem m3_old_26_one : m3 26 1 = old (AlgebraCertificates.M₃₁ 26) := by
  apply MvPolynomial.funext
  intro v
  simp [m3, schur3, schur21, schur111, old, AlgebraCertificates.M₃₁,
    AlgebraCertificates.evaluate, AlgebraCertificates.c, AlgebraCertificates.Z₁,
    AlgebraCertificates.Z₂, AlgebraCertificates.Z₃, z1, z2, z3, p1, p2, p3, u]
  all_goals ring

theorem m3_old_24_two : m3 24 2 = old (AlgebraCertificates.M₃₂ 24) := by
  apply MvPolynomial.funext
  intro v
  simp [m3, schur3, schur21, schur111, old, AlgebraCertificates.M₃₂,
    AlgebraCertificates.evaluate, AlgebraCertificates.c, AlgebraCertificates.Z₁,
    AlgebraCertificates.Z₂, AlgebraCertificates.Z₃, z1, z2, z3, p1, p2, p3, u]
  all_goals ring

theorem m3_old_26_two : m3 26 2 = old (AlgebraCertificates.M₃₂ 26) := by
  apply MvPolynomial.funext
  intro v
  simp [m3, schur3, schur21, schur111, old, AlgebraCertificates.M₃₂,
    AlgebraCertificates.evaluate, AlgebraCertificates.c, AlgebraCertificates.Z₁,
    AlgebraCertificates.Z₂, AlgebraCertificates.Z₃, z1, z2, z3, p1, p2, p3, u]
  all_goals ring

/-- The full printed dimension-eleven certificate, retaining every `u` power. -/
def rhs11 : P :=
  C 288 * u ^ 11 + C (2482652 / 51975) * m1Full * u ^ 10
    + (C (3094720 / 6237) * m2One 24 + C (214814 / 93555) * m2Full) * u ^ 9
    + (C (164360 / 2673) * m3 24 2 + C (10048 / 891) * m3 24 3
       + C (922051 / 93555) * m3 24 4) * u ^ 8
    + q11 * u ^ 7 + C 8192 * f5 * u ^ 6

/-- The full printed dimension-twelve certificate, retaining every `u` power. -/
def rhs12 : P :=
  C 336 * u ^ 12 + C (3050776 / 51975) * m1Full * u ^ 11
    + (C (12506936 / 17325) * m2One 26 + C (1445966 / 467775) * m2Full) * u ^ 10
    + (C (472784 / 155925) * m3 26 1 + C (152711 / 18711) * m3 26 2
       + C (1771432 / 18711) * m3 26 3) * u ^ 9
    + q12 * u ^ 8 + C 16384 * f5 * u ^ 7

theorem certificate11 : density11 = rhs11 := by
  rw [density11_printed]
  apply MvPolynomial.funext
  intro v
  simp [printed11, rhs11, m1Full, m2One, m2Full, m3,
    schur3, schur21, schur111, z1, z2, z3, u, p1, p2, p3]
  ring

theorem certificate12 : density12 = rhs12 := by
  rw [density12_printed]
  apply MvPolynomial.funext
  intro v
  simp [printed12, rhs12, m1Full, m2One, m2Full, m3,
    schur3, schur21, schur111, z1, z2, z3, u, p1, p2, p3]
  ring

/-- Polynomial certificate identities remain valid after evaluation in any
commutative rational algebra, including one with nilpotents. -/
theorem certificate11_evaluate {R : Type*} [CommRing R] [Algebra ℚ R]
    (v : Fin 6 → R) :
    MvPolynomial.aeval v density11 = MvPolynomial.aeval v rhs11 := by
  rw [certificate11]

theorem certificate12_evaluate {R : Type*} [CommRing R] [Algebra ℚ R]
    (v : Fin 6 → R) :
    MvPolynomial.aeval v density12 = MvPolynomial.aeval v rhs12 := by
  rw [certificate12]

/-- Every explicit lower-weight coefficient in the dimension-eleven identity
is strictly positive. -/
theorem coefficient_signs11 :
    (0 : ℚ) < 288 ∧ 0 < 2482652 / 51975 ∧
      0 < 3094720 / 6237 ∧ 0 < 214814 / 93555 ∧
      0 < 164360 / 2673 ∧ 0 < 10048 / 891 ∧
      0 < 922051 / 93555 ∧ 0 < 8192 := by
  norm_num

theorem coefficient_signs12 :
    (0 : ℚ) < 336 ∧ 0 < 3050776 / 51975 ∧
      0 < 12506936 / 17325 ∧ 0 < 1445966 / 467775 ∧
      0 < 472784 / 155925 ∧ 0 < 152711 / 18711 ∧
      0 < 1771432 / 18711 ∧ 0 < 16384 := by
  norm_num

end
end QuaternionicSymmetry.ElevenTwelveProjectionCertificates
