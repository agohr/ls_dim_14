import QuaternionicSymmetry.PrintedSevenTenLinearAssembly

/-! Exact full-u polynomial certificates through quaternionic dimension six,
in the same six-variable ring as the higher printed certificates. -/
namespace QuaternionicSymmetry.PrintedTwoSixLinearAssembly
open MvPolynomial DimensionElevenTwelveDensity
  ElevenTwelveProjectionCertificates ReconstructionExamples
noncomputable section

abbrev P := DimensionElevenTwelveDensity.P

def density2 : P := old AlgebraCertificates.K₂
def density3 : P := old AlgebraCertificates.K₃
def density4 : P := old AlgebraCertificates.K₄

theorem density2_formula : density2 = C 16 * u ^ 2 := by
  rw [density2, AlgebraCertificates.polynomial_certificate₂]
  simp [old, AlgebraCertificates.evaluate, AlgebraCertificates.RHS₂,
    AlgebraCertificates.c, AlgebraCertificates.U, u]

theorem density3_formula : density3 = C 32 * u ^ 3 + C (4/3) * m1Full * u ^ 2 := by
  rw [density3, AlgebraCertificates.polynomial_certificate₃]
  simp [old, AlgebraCertificates.evaluate, AlgebraCertificates.RHS₃,
    AlgebraCertificates.c, AlgebraCertificates.U, AlgebraCertificates.Z₁,
    m1Full, z1, p1, u]

theorem density4_formula : density4 = C 48 * u ^ 4 + C (8/3) * m1Full * u ^ 3 := by
  rw [density4, AlgebraCertificates.polynomial_certificate₄]
  simp [old, AlgebraCertificates.evaluate, AlgebraCertificates.RHS₄,
    AlgebraCertificates.c, AlgebraCertificates.U, AlgebraCertificates.Z₁,
    m1Full, z1, p1, u]


theorem linear_density2 (L : P →ₗ[ℚ] ℝ) :
    L density2 = (16:ℝ) * L (u^2) := by
  rw [density2_formula]
  simp only [← smul_eq_C_mul, map_smul, Rat.smul_def]
  norm_num

theorem linear_density3 (L : P →ₗ[ℚ] ℝ) :
    L density3 = (32:ℝ) * L (u^3) +
      (4/3:ℝ) * L (m1Full*u^2) := by
  rw [density3_formula, mul_assoc (C (4/3)) m1Full (u^2)]
  simp only [map_add, ← smul_eq_C_mul, map_smul]
  rw [Rat.smul_def (4/3:ℚ) (L (m1Full*u^2)),
    Rat.smul_def (32:ℚ) (L (u^3))]
  norm_num

theorem linear_density4 (L : P →ₗ[ℚ] ℝ) :
    L density4 = (48:ℝ) * L (u^4) +
      (8/3:ℝ) * L (m1Full*u^3) := by
  rw [density4_formula, mul_assoc (C (8/3)) m1Full (u^3)]
  simp only [map_add, ← smul_eq_C_mul, map_smul]
  rw [Rat.smul_def (8/3:ℚ) (L (m1Full*u^3)),
    Rat.smul_def (48:ℚ) (L (u^4))]
  norm_num

end
end QuaternionicSymmetry.PrintedTwoSixLinearAssembly
