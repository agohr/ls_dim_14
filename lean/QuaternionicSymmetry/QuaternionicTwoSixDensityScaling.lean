import QuaternionicSymmetry.QuaternionicSevenTenDensityScaling
import QuaternionicSymmetry.PrintedTwoSixLinearAssembly

/-! Exact weighted scaling for the printed dimensions two through six. -/
namespace QuaternionicSymmetry.QuaternionicTwoSixDensityScaling
open Module MvPolynomial ElevenTwelveDensityScaling
open DimensionElevenTwelveDensity ReconstructionExamples
open QuaternionicFundamental QuaternionicTracePositivity PrintedProjectionCubicPositivity
noncomputable section
variable {R : Type*} [CommRing R] [Algebra ℚ R]

theorem density2_eval_scale (r : R) (v : Fin 6 → R) :
    aeval (weightedValues r v) PrintedTwoSixLinearAssembly.density2 =
      r ^ 2 * aeval v PrintedTwoSixLinearAssembly.density2 := by
  rw [PrintedTwoSixLinearAssembly.density2_formula]
  simp [u, weightedValues]
  ring

theorem density3_eval_scale (r : R) (v : Fin 6 → R) :
    aeval (weightedValues r v) PrintedTwoSixLinearAssembly.density3 =
      r ^ 3 * aeval v PrintedTwoSixLinearAssembly.density3 := by
  rw [PrintedTwoSixLinearAssembly.density3_formula]
  simp [ElevenTwelveProjectionCertificates.m1Full,
    ElevenTwelveProjectionCertificates.z1, u, p1, weightedValues]
  ring

theorem density4_eval_scale (r : R) (v : Fin 6 → R) :
    aeval (weightedValues r v) PrintedTwoSixLinearAssembly.density4 =
      r ^ 4 * aeval v PrintedTwoSixLinearAssembly.density4 := by
  rw [PrintedTwoSixLinearAssembly.density4_formula]
  simp [ElevenTwelveProjectionCertificates.m1Full,
    ElevenTwelveProjectionCertificates.z1, u, p1, weightedValues]
  ring

theorem k5_eval_scale (r : R) (v : Fin 6 → R) :
    aeval (weightedValues r v) k5 = r ^ 5 * aeval v k5 := by
  rw [dimension_five_power_sums]
  simp [u, p1, p2, weightedValues]
  ring

theorem k6_eval_scale (r : R) (v : Fin 6 → R) :
    aeval (weightedValues r v) k6 = r ^ 6 * aeval v k6 := by
  rw [dimension_six_power_sums]
  simp [u, p1, p2, weightedValues]
  ring

variable {ι β κ V : Type*} [Fintype ι] [Fintype β] [Fintype κ]
  [DecidableEq κ] [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem normalized_density2 (Q : QuaternionicStructure V) (b : Basis ι ℝ V)
    (s : ℝ) (hs : s ≠ 0) (B : β → Matrix κ κ ℂ) (η : β → E V) :
    aeval (QuaternionicNormalizedDensityValues.normalizedValues Q b s B η)
        PrintedTwoSixLinearAssembly.density2 =
      s ^ 4 • aeval (densityValues Q b (fun a => s⁻¹ • B a) η)
        PrintedTwoSixLinearAssembly.density2 := by
  rw [← QuaternionicNormalizedDensityValues.weighted_inverse_eq Q b s hs B η,
    density2_eval_scale]
  simp only [← map_pow, ← pow_mul, ← Algebra.smul_def]

theorem normalized_density3 (Q : QuaternionicStructure V) (b : Basis ι ℝ V)
    (s : ℝ) (hs : s ≠ 0) (B : β → Matrix κ κ ℂ) (η : β → E V) :
    aeval (QuaternionicNormalizedDensityValues.normalizedValues Q b s B η)
        PrintedTwoSixLinearAssembly.density3 =
      s ^ 6 • aeval (densityValues Q b (fun a => s⁻¹ • B a) η)
        PrintedTwoSixLinearAssembly.density3 := by
  rw [← QuaternionicNormalizedDensityValues.weighted_inverse_eq Q b s hs B η,
    density3_eval_scale]
  simp only [← map_pow, ← pow_mul, ← Algebra.smul_def]

theorem normalized_density4 (Q : QuaternionicStructure V) (b : Basis ι ℝ V)
    (s : ℝ) (hs : s ≠ 0) (B : β → Matrix κ κ ℂ) (η : β → E V) :
    aeval (QuaternionicNormalizedDensityValues.normalizedValues Q b s B η)
        PrintedTwoSixLinearAssembly.density4 =
      s ^ 8 • aeval (densityValues Q b (fun a => s⁻¹ • B a) η)
        PrintedTwoSixLinearAssembly.density4 := by
  rw [← QuaternionicNormalizedDensityValues.weighted_inverse_eq Q b s hs B η,
    density4_eval_scale]
  simp only [← map_pow, ← pow_mul, ← Algebra.smul_def]

theorem normalized_k5 (Q : QuaternionicStructure V) (b : Basis ι ℝ V)
    (s : ℝ) (hs : s ≠ 0) (B : β → Matrix κ κ ℂ) (η : β → E V) :
    aeval (QuaternionicNormalizedDensityValues.normalizedValues Q b s B η) k5 =
      s ^ 10 • aeval (densityValues Q b (fun a => s⁻¹ • B a) η) k5 := by
  rw [← QuaternionicNormalizedDensityValues.weighted_inverse_eq Q b s hs B η,
    k5_eval_scale]
  simp only [← map_pow, ← pow_mul, ← Algebra.smul_def]

theorem normalized_k6 (Q : QuaternionicStructure V) (b : Basis ι ℝ V)
    (s : ℝ) (hs : s ≠ 0) (B : β → Matrix κ κ ℂ) (η : β → E V) :
    aeval (QuaternionicNormalizedDensityValues.normalizedValues Q b s B η) k6 =
      s ^ 12 • aeval (densityValues Q b (fun a => s⁻¹ • B a) η) k6 := by
  rw [← QuaternionicNormalizedDensityValues.weighted_inverse_eq Q b s hs B η,
    k6_eval_scale]
  simp only [← map_pow, ← pow_mul, ← Algebra.smul_def]

end
end QuaternionicSymmetry.QuaternionicTwoSixDensityScaling
