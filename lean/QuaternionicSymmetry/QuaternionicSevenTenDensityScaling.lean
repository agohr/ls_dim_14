import QuaternionicSymmetry.PrintedCertificatesSevenTen
import QuaternionicSymmetry.QuaternionicNormalizedDensityValues

/-! Exact weighted scaling for the printed dimensions seven through ten,
valid in any commutative rational algebra, including exterior algebras with
nilpotents. -/
namespace QuaternionicSymmetry.QuaternionicSevenTenDensityScaling
open Module MvPolynomial ElevenTwelveDensityScaling
open PrintedCertificatesSevenTen ElevenTwelveProjectionCertificates
open ReconstructionExamples
open QuaternionicFundamental QuaternionicTracePositivity PrintedProjectionCubicPositivity
open DimensionElevenTwelveDensity
noncomputable section
variable {R : Type*} [CommRing R] [Algebra ℚ R]

theorem rhs7_eval_scale (r : R) (v : Fin 6 → R) :
    aeval (weightedValues r v) rhs7 = r ^ 7 * aeval v rhs7 := by
  simp [rhs7, m1, m2Full, m2One, m3, m3Full,
    schur3, schur21, schur111, z1, z2, z3,
    u, p1, p2, p3, weightedValues]
  ring

theorem rhs8_eval_scale (r : R) (v : Fin 6 → R) :
    aeval (weightedValues r v) rhs8 = r ^ 8 * aeval v rhs8 := by
  simp [rhs8, m1, m2Full, m2One, m3, m3Full,
    schur3, schur21, schur111, z1, z2, z3,
    u, p1, p2, p3, weightedValues]
  ring

theorem rhs9_eval_scale (r : R) (v : Fin 6 → R) :
    aeval (weightedValues r v) rhs9 = r ^ 9 * aeval v rhs9 := by
  simp [rhs9, m1, m2Full, m2One, m3, m3Full, f4,
    schur3, schur21, schur111, z1, z2, z3,
    u, p1, p2, p3, p4, weightedValues]
  ring

theorem rhs10_eval_scale (r : R) (v : Fin 6 → R) :
    aeval (weightedValues r v) rhs10 = r ^ 10 * aeval v rhs10 := by
  simp [rhs10, m1, m2Full, m2One, m3, m3Full, f4,
    schur3, schur21, schur111, z1, z2, z3,
    u, p1, p2, p3, p4, weightedValues]
  ring

variable {ι β κ V : Type*} [Fintype ι] [Fintype β] [Fintype κ]
  [DecidableEq κ] [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem normalized_rhs7 (Q : QuaternionicStructure V) (b : Basis ι ℝ V)
    (s : ℝ) (hs : s ≠ 0) (B : β → Matrix κ κ ℂ) (η : β → E V) :
    aeval (QuaternionicNormalizedDensityValues.normalizedValues Q b s B η) rhs7 =
      s ^ 14 • aeval (densityValues Q b
        (fun a => s⁻¹ • B a) η) rhs7 := by
  rw [← QuaternionicNormalizedDensityValues.weighted_inverse_eq Q b s hs B η,
    rhs7_eval_scale]
  simp only [← map_pow, ← pow_mul, ← Algebra.smul_def]

theorem normalized_rhs8 (Q : QuaternionicStructure V) (b : Basis ι ℝ V)
    (s : ℝ) (hs : s ≠ 0) (B : β → Matrix κ κ ℂ) (η : β → E V) :
    aeval (QuaternionicNormalizedDensityValues.normalizedValues Q b s B η) rhs8 =
      s ^ 16 • aeval (densityValues Q b
        (fun a => s⁻¹ • B a) η) rhs8 := by
  rw [← QuaternionicNormalizedDensityValues.weighted_inverse_eq Q b s hs B η,
    rhs8_eval_scale]
  simp only [← map_pow, ← pow_mul, ← Algebra.smul_def]

theorem normalized_rhs9 (Q : QuaternionicStructure V) (b : Basis ι ℝ V)
    (s : ℝ) (hs : s ≠ 0) (B : β → Matrix κ κ ℂ) (η : β → E V) :
    aeval (QuaternionicNormalizedDensityValues.normalizedValues Q b s B η) rhs9 =
      s ^ 18 • aeval (densityValues Q b
        (fun a => s⁻¹ • B a) η) rhs9 := by
  rw [← QuaternionicNormalizedDensityValues.weighted_inverse_eq Q b s hs B η,
    rhs9_eval_scale]
  simp only [← map_pow, ← pow_mul, ← Algebra.smul_def]

theorem normalized_rhs10 (Q : QuaternionicStructure V) (b : Basis ι ℝ V)
    (s : ℝ) (hs : s ≠ 0) (B : β → Matrix κ κ ℂ) (η : β → E V) :
    aeval (QuaternionicNormalizedDensityValues.normalizedValues Q b s B η) rhs10 =
      s ^ 20 • aeval (densityValues Q b
        (fun a => s⁻¹ • B a) η) rhs10 := by
  rw [← QuaternionicNormalizedDensityValues.weighted_inverse_eq Q b s hs B η,
    rhs10_eval_scale]
  simp only [← map_pow, ← pow_mul, ← Algebra.smul_def]

end
end QuaternionicSymmetry.QuaternionicSevenTenDensityScaling
