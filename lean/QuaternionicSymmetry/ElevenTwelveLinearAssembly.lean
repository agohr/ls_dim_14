import QuaternionicSymmetry.ElevenTwelveProjectionCertificates
import QuaternionicSymmetry.QuarticOrbitalDensityBridge
import QuaternionicSymmetry.ConditionalC12Bounds

/-!
# Dimension 11 and 12 finite linear-functional assembly

The twelve generators below are full-`u` rational polynomials: six projection
moments, five finite orbital polynomials, and one Gaussian coefficient.
The polynomial equalities are unconditional. The numerical conclusions use an
arbitrary rational-linear functional to `ℝ`; identifying this functional with
integration of forms or cohomology classes, and proving the required signs,
are separate geometric obligations.
-/

namespace QuaternionicSymmetry.ElevenTwelveLinearAssembly

open MvPolynomial
open scoped BigOperators
open DimensionElevenTwelveDensity
open ElevenTwelveProjectionCertificates
open QuarticOrbitalDensityBridge
open ConditionalC12Bounds

noncomputable section

abbrev P := DimensionElevenTwelveDensity.P

def generators11 : Fin 12 → P := ![
  m1Full * u ^ 10,
  m2One 24 * u ^ 9,
  m2Full * u ^ 9,
  m3 24 2 * u ^ 8,
  m3 24 3 * u ^ 8,
  m3 24 4 * u ^ 8,
  orbital11 QuarticOrbitalEleven.a₁ * u ^ 7,
  orbital11 QuarticOrbitalEleven.a₂ * u ^ 7,
  orbital11 QuarticOrbitalEleven.a₃ * u ^ 7,
  orbital11 QuarticOrbitalEleven.a₄ * u ^ 7,
  orbital11 QuarticOrbitalEleven.a₅ * u ^ 7,
  f5 * u ^ 6]

def generators12 : Fin 12 → P := ![
  m1Full * u ^ 11,
  m2One 26 * u ^ 10,
  m2Full * u ^ 10,
  m3 26 1 * u ^ 9,
  m3 26 2 * u ^ 9,
  m3 26 3 * u ^ 9,
  orbital12 QuarticOrbitalTwelve.b₁ * u ^ 8,
  orbital12 QuarticOrbitalTwelve.b₂ * u ^ 8,
  orbital12 QuarticOrbitalTwelve.b₃ * u ^ 8,
  orbital12 QuarticOrbitalTwelve.b₄ * u ^ 8,
  orbital12 QuarticOrbitalTwelve.b₅ * u ^ 8,
  f5 * u ^ 7]

/-- The complete density is the scalar reserve plus the twelve actual
full-`u` polynomial generators with the printed rational coefficients. -/
theorem density11_generators :
    density11 = C 288 * u ^ 11 +
      ∑ i, C (coefficients11 i) * generators11 i := by
  rw [certificate11]
  simp only [rhs11, q11_orbital]
  simp [Fin.sum_univ_succ, generators11, coefficients11,
    QuarticOrbitalEleven.c₁, QuarticOrbitalEleven.c₂,
    QuarticOrbitalEleven.c₃, QuarticOrbitalEleven.c₄,
    QuarticOrbitalEleven.c₅]
  ring

theorem density12_generators :
    density12 = C 336 * u ^ 12 +
      ∑ i, C (coefficients12 i) * generators12 i := by
  rw [certificate12]
  simp only [rhs12, q12_orbital]
  simp [Fin.sum_univ_succ, generators12, coefficients12,
    QuarticOrbitalTwelve.c₁, QuarticOrbitalTwelve.c₂,
    QuarticOrbitalTwelve.c₃, QuarticOrbitalTwelve.c₄,
    QuarticOrbitalTwelve.c₅]
  ring

/-- Applying any rational-linear functional preserves the exact finite
certificate. Its value on the scalar reserve is kept explicit. -/
theorem linear_density11 (L : P →ₗ[ℚ] ℝ) :
    L density11 = (288 : ℝ) * L (u ^ 11) +
      ∑ i, (coefficients11 i : ℝ) * L (generators11 i) := by
  rw [density11_generators]
  simp only [map_add, map_sum, ← smul_eq_C_mul, map_smul, Rat.smul_def]
  norm_num

theorem linear_density12 (L : P →ₗ[ℚ] ℝ) :
    L density12 = (336 : ℝ) * L (u ^ 12) +
      ∑ i, (coefficients12 i : ℝ) * L (generators12 i) := by
  rw [density12_generators]
  simp only [map_add, map_sum, ← smul_eq_C_mul, map_smul, Rat.smul_def]
  norm_num

/-- A numerical index interpretation of the full polynomial density,
positivity of the scalar volume, and signs of its twelve actual generators
force the dimension-eleven symmetry bound. -/
theorem bound11 {d : ℕ} (L : P →ₗ[ℚ] ℝ)
    (hindex : (d : ℝ) = (QuaternionicSymmetry.delta 11 : ℝ) + L density11)
    (hU : 0 < L (u ^ 11))
    (hgenerators : ∀ i, 0 ≤ L (generators11 i)) : 13 ≤ d := by
  rw [linear_density11] at hindex
  apply ConditionalC12Bounds.bound11 (U := L (u ^ 11))
    (fun i => L (generators11 i))
  · simpa [remainder11, QuaternionicSymmetry.scalarCoefficient, add_assoc] using hindex
  · exact hU
  · exact hgenerators

theorem bound12 {d : ℕ} (L : P →ₗ[ℚ] ℝ)
    (hindex : (d : ℝ) = (QuaternionicSymmetry.delta 12 : ℝ) + L density12)
    (hU : 0 < L (u ^ 12))
    (hgenerators : ∀ i, 0 ≤ L (generators12 i)) : 16 ≤ d := by
  rw [linear_density12] at hindex
  apply ConditionalC12Bounds.bound12 (U := L (u ^ 12))
    (fun i => L (generators12 i))
  · simpa [remainder12, QuaternionicSymmetry.scalarCoefficient, add_assoc] using hindex
  · exact hU
  · exact hgenerators

theorem no_small_symmetry11 {d : ℕ} (L : P →ₗ[ℚ] ℝ)
    (hindex : (d : ℝ) = (QuaternionicSymmetry.delta 11 : ℝ) + L density11)
    (hU : 0 < L (u ^ 11))
    (hgenerators : ∀ i, 0 ≤ L (generators11 i))
    (hsmall : d ≤ 3) : False := by
  have h := bound11 L hindex hU hgenerators
  omega

theorem no_small_symmetry12 {d : ℕ} (L : P →ₗ[ℚ] ℝ)
    (hindex : (d : ℝ) = (QuaternionicSymmetry.delta 12 : ℝ) + L density12)
    (hU : 0 < L (u ^ 12))
    (hgenerators : ∀ i, 0 ≤ L (generators12 i))
    (hsmall : d ≤ 3) : False := by
  have h := bound12 L hindex hU hgenerators
  omega

end
end QuaternionicSymmetry.ElevenTwelveLinearAssembly
