import QuaternionicSymmetry.ElevenTwelveProjectionCertificates

/-! The explicit dimension-five/six worked calculations and the dimension-nine
fourth Gaussian recognition from Chapter 6. All statements retain powers of
`u` and use `z_j=2p_j` inside a universal rational polynomial ring. -/

namespace QuaternionicSymmetry.ReconstructionExamples

open MvPolynomial
open DimensionElevenTwelveDensity
open ElevenTwelveProjectionCertificates
noncomputable section

abbrev P := DimensionElevenTwelveDensity.P

def k5 : P := old AlgebraCertificates.K₅
def k6 : P := old AlgebraCertificates.K₆

theorem dimension_five_power_sums :
    k5 = C 72 * u ^ 5 + C (536 / 45) * p1 * u ^ 4 +
      C (4 / 9) * p1 ^ 2 * u ^ 3 + C (4 / 45) * p2 * u ^ 3 := by
  apply MvPolynomial.funext
  intro v
  simp [k5, old, AlgebraCertificates.evaluate, AlgebraCertificates.K₅,
    AlgebraCertificates.A₂, AlgebraCertificates.A₁, AlgebraCertificates.A₀,
    AlgebraCertificates.b₂, AlgebraCertificates.b₁,
    AlgebraCertificates.c, AlgebraCertificates.U, AlgebraCertificates.Z₁,
    AlgebraCertificates.Z₂, u, p1, p2]
  ring

theorem dimension_six_power_sums :
    k6 = C 96 * u ^ 6 + C (832 / 45) * p1 * u ^ 5 +
      C (8 / 9) * p1 ^ 2 * u ^ 4 + C (8 / 45) * p2 * u ^ 4 := by
  apply MvPolynomial.funext
  intro v
  simp [k6, old, AlgebraCertificates.evaluate, AlgebraCertificates.K₆,
    AlgebraCertificates.A₂, AlgebraCertificates.A₁, AlgebraCertificates.A₀,
    AlgebraCertificates.b₂, AlgebraCertificates.b₁,
    AlgebraCertificates.c, AlgebraCertificates.U, AlgebraCertificates.Z₁,
    AlgebraCertificates.Z₂, u, p1, p2]
  ring

theorem dimension_five_projection :
    k5 = C 72 * u ^ 5 + C (268 / 45) * m1Full * u ^ 4 +
      C (1 / 15) * m2Full * u ^ 3 + C (104 / 15) * m2One 12 * u ^ 3 := by
  rw [dimension_five_power_sums]
  apply MvPolynomial.funext
  intro v
  simp [m1Full, m2Full, m2One, z1, z2, u, p1, p2]
  ring

theorem dimension_six_projection :
    k6 = C 96 * u ^ 6 + C (416 / 45) * m1Full * u ^ 5 +
      C (2 / 15) * m2Full * u ^ 4 + C (56 / 3) * m2One 14 * u ^ 4 := by
  rw [dimension_six_power_sums]
  apply MvPolynomial.funext
  intro v
  simp [m1Full, m2Full, m2One, z1, z2, u, p1, p2]
  ring

theorem dimension_five_coefficients_pos :
    (0 : ℚ) < 72 ∧ (0 : ℚ) < 268 / 45 ∧
      (0 : ℚ) < 1 / 15 ∧ (0 : ℚ) < 104 / 15 := by norm_num

theorem dimension_six_coefficients_pos :
    (0 : ℚ) < 96 ∧ (0 : ℚ) < 416 / 45 ∧
      (0 : ℚ) < 2 / 15 ∧ (0 : ℚ) < 56 / 3 := by norm_num

/-- The fourth Gaussian coefficient is the precise Chapter 6 quartic in
the reduced power sums. -/
def f4 : P := C (1 / 87091200) *
  (C 175 * p1 ^ 4 + C 210 * p1 ^ 2 * p2 + C 21 * p2 ^ 2 +
    C 80 * p1 * p3 + C 18 * p4)

theorem f4_from_existing : old AlgebraCertificates.F₄ = f4 := by
  apply MvPolynomial.funext
  intro v
  simp [old, AlgebraCertificates.evaluate, AlgebraCertificates.F₄,
    AlgebraCertificates.c, AlgebraCertificates.Z₁, AlgebraCertificates.Z₂,
    AlgebraCertificates.Z₃, AlgebraCertificates.Z₄,
    f4, p1, p2, p3, p4, u]
  ring

/-- The top quartic term of the dimension-nine certificate is exactly
`2^11 F₄ u^5`, with the independent reduced `F₄` formula. -/
theorem dimension_nine_quartic :
    old (AlgebraCertificates.c 2048 * AlgebraCertificates.F₄ *
      AlgebraCertificates.U ^ 5) = C 2048 * f4 * u ^ 5 := by
  calc
    _ = old (AlgebraCertificates.c 2048) *
        old AlgebraCertificates.F₄ * old AlgebraCertificates.U ^ 5 := by
          simp [old, AlgebraCertificates.evaluate]
    _ = C 2048 * f4 * u ^ 5 := by
          rw [f4_from_existing]
          simp [old, AlgebraCertificates.evaluate, AlgebraCertificates.c,
            AlgebraCertificates.U, u]

end
end QuaternionicSymmetry.ReconstructionExamples
