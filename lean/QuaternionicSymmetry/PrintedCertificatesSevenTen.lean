import QuaternionicSymmetry.ReconstructionExamples

/-! The exact Chapter 7 projection tables in dimensions 7–10, in the same
full-`u` six-variable ring as the higher certificates. The dimension 9–10
Gaussian term is the independently recognized `F₄`; analytic signs remain
separate. -/

namespace QuaternionicSymmetry.PrintedCertificatesSevenTen

open MvPolynomial
open DimensionElevenTwelveDensity
open ElevenTwelveProjectionCertificates
open ReconstructionExamples
noncomputable section

abbrev P := DimensionElevenTwelveDensity.P

def m1 (r ell : ℚ) : P := C (ell / r) * z1
def m3Full : P := z1 ^ 3

def rhs7 : P :=
  C 128 * u ^ 7 + C (28080 / 1890) * m1 16 16 * u ^ 6 +
    (C (668 / 1890) * m2Full + C (100096 / 1890) * m2One 16) * u ^ 5 +
    (C (3 / 1890) * m3Full + C (6528 / 1890) * m3 16 1 +
      C (4080 / 1890) * m3 16 2) * u ^ 4

theorem certificate7 : old AlgebraCertificates.K₇ = rhs7 := by
  rw [AlgebraCertificates.polynomial_certificate₇]
  apply MvPolynomial.funext
  intro v
  simp [old, AlgebraCertificates.evaluate, AlgebraCertificates.RHS₇,
    AlgebraCertificates.F₃, AlgebraCertificates.M₂₁,
    AlgebraCertificates.c, AlgebraCertificates.U, AlgebraCertificates.Z₁,
    AlgebraCertificates.Z₂, AlgebraCertificates.Z₃,
    rhs7, m1, m2One, m2Full, m3Full, m3,
    schur3, schur21, schur111, z1, z2, z3, u, p1, p2, p3]
  ring

def rhs8 : P :=
  C 160 * u ^ 8 + C (96720 / 4725) * m1 18 18 * u ^ 7 +
    (C (2710 / 4725) * m2Full + C (485640 / 4725) * m2One 18) * u ^ 6 +
    (C (15 / 4725) * m3Full + C (43320 / 4725) * m3 18 1 +
      C (29070 / 4725) * m3 18 2) * u ^ 5

theorem certificate8 : old AlgebraCertificates.K₈ = rhs8 := by
  rw [AlgebraCertificates.polynomial_certificate₈]
  apply MvPolynomial.funext
  intro v
  simp [old, AlgebraCertificates.evaluate, AlgebraCertificates.RHS₈,
    AlgebraCertificates.F₃, AlgebraCertificates.M₂₁,
    AlgebraCertificates.c, AlgebraCertificates.U, AlgebraCertificates.Z₁,
    AlgebraCertificates.Z₂, AlgebraCertificates.Z₃,
    rhs8, m1, m2One, m2Full, m3Full, m3,
    schur3, schur21, schur111, z1, z2, z3, u, p1, p2, p3]
  ring

def rhs9 : P :=
  C 200 * u ^ 9 + C (180512 / 315) * m1 20 1 * u ^ 8 +
    (C (8752 / 45) * m2One 20 + C (14704 / 14175) * m2Full) * u ^ 7 +
    (C (2992 / 405) * m3 20 1 + C (2090 / 81) * m3 20 2 +
      C (239 / 28350) * m3Full) * u ^ 6 + C 2048 * f4 * u ^ 5

theorem certificate9 : old AlgebraCertificates.K₉ = rhs9 := by
  rw [AlgebraCertificates.polynomial_certificate₉]
  apply MvPolynomial.funext
  intro v
  simp [old, AlgebraCertificates.evaluate, AlgebraCertificates.RHS₉,
    AlgebraCertificates.F₄, AlgebraCertificates.M₂₁,
    AlgebraCertificates.M₃₁, AlgebraCertificates.M₃₂,
    AlgebraCertificates.c, AlgebraCertificates.U, AlgebraCertificates.Z₁,
    AlgebraCertificates.Z₂, AlgebraCertificates.Z₃, AlgebraCertificates.Z₄,
    rhs9, m1, m2One, m2Full, m3Full, m3, f4,
    schur3, schur21, schur111, z1, z2, z3, u, p1, p2, p3, p4]
  ring

def rhs10 : P :=
  C 240 * u ^ 10 + C (182336 / 225) * m1 22 1 * u ^ 9 +
    (C (1495736 / 4725) * m2One 22 + C (21278 / 14175) * m2Full) * u ^ 8 +
    (C (4048 / 4725) * m3 22 1 + C (23276 / 405) * m3 22 2 +
      C (194 / 14175) * m3Full) * u ^ 7 + C 4096 * f4 * u ^ 6

theorem certificate10 : old AlgebraCertificates.K₁₀ = rhs10 := by
  rw [AlgebraCertificates.polynomial_certificate₁₀]
  apply MvPolynomial.funext
  intro v
  simp [old, AlgebraCertificates.evaluate, AlgebraCertificates.RHS₁₀,
    AlgebraCertificates.F₄, AlgebraCertificates.M₂₁,
    AlgebraCertificates.M₃₁, AlgebraCertificates.M₃₂,
    AlgebraCertificates.c, AlgebraCertificates.U, AlgebraCertificates.Z₁,
    AlgebraCertificates.Z₂, AlgebraCertificates.Z₃, AlgebraCertificates.Z₄,
    rhs10, m1, m2One, m2Full, m3Full, m3, f4,
    schur3, schur21, schur111, z1, z2, z3, u, p1, p2, p3, p4]
  ring

/-- The six non-scalar moment coefficients in each printed identity are
positive; the scalar reserves and Gaussian coefficients are positive too. -/
theorem signs7 :
    (0 : ℚ) < 128 ∧ (0 : ℚ) < 28080 / 1890 ∧ (0 : ℚ) < 668 / 1890 ∧
      (0 : ℚ) < 100096 / 1890 ∧ (0 : ℚ) < 3 / 1890 ∧ (0 : ℚ) < 6528 / 1890 ∧
      (0 : ℚ) < 4080 / 1890 := by norm_num

theorem signs8 :
    (0 : ℚ) < 160 ∧ (0 : ℚ) < 96720 / 4725 ∧ (0 : ℚ) < 2710 / 4725 ∧
      (0 : ℚ) < 485640 / 4725 ∧ (0 : ℚ) < 15 / 4725 ∧ (0 : ℚ) < 43320 / 4725 ∧
      (0 : ℚ) < 29070 / 4725 := by norm_num

theorem signs9 :
    (0 : ℚ) < 200 ∧ (0 : ℚ) < 180512 / 315 ∧ (0 : ℚ) < 8752 / 45 ∧
      (0 : ℚ) < 14704 / 14175 ∧ (0 : ℚ) < 2992 / 405 ∧ (0 : ℚ) < 2090 / 81 ∧
      (0 : ℚ) < 239 / 28350 ∧ (0 : ℚ) < 2048 := by norm_num

theorem signs10 :
    (0 : ℚ) < 240 ∧ (0 : ℚ) < 182336 / 225 ∧ (0 : ℚ) < 1495736 / 4725 ∧
      (0 : ℚ) < 21278 / 14175 ∧ (0 : ℚ) < 4048 / 4725 ∧ (0 : ℚ) < 23276 / 405 ∧
      (0 : ℚ) < 194 / 14175 ∧ (0 : ℚ) < 4096 := by norm_num

end
end QuaternionicSymmetry.PrintedCertificatesSevenTen
