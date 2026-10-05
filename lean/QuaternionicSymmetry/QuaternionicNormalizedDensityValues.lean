import QuaternionicSymmetry.MatrixTraceScaling
import QuaternionicSymmetry.ElevenTwelveDensityScaling
import QuaternionicSymmetry.QuaternionicC12DensityBound

/-! A positive rescaling of the fundamental four-form is compatible with
the exact weighted density identities and reciprocal matrix rescaling. -/
namespace QuaternionicSymmetry.QuaternionicNormalizedDensityValues
open Module MvPolynomial QuaternionicFundamental QuaternionicTracePositivity
open PrintedProjectionCubicPositivity MatrixTracePolynomial MatrixTraceScaling
open ElevenTwelveDensityScaling DimensionElevenTwelveDensity
noncomputable section
variable {ι β κ V : Type*} [Fintype ι] [Fintype β] [Fintype κ] [DecidableEq κ]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def normalizedValues (Q : QuaternionicStructure V) (b : Basis ι ℝ V) (s : ℝ)
    (B : β → Matrix κ κ ℂ) (η : β → E V) : Fin 6 → CE V :=
  ![s ^ 2 • embed (V := V) (form Q b),
    embed (V := V) (signedTracePower (complexifiedMatrix B η) 1),
    embed (V := V) (signedTracePower (complexifiedMatrix B η) 2),
    embed (V := V) (signedTracePower (complexifiedMatrix B η) 3),
    embed (V := V) (signedTracePower (complexifiedMatrix B η) 4),
    embed (V := V) (signedTracePower (complexifiedMatrix B η) 5)]

theorem inverse_scaled_trace (B : β → Matrix κ κ ℂ) (η : β → E V)
    (s : ℝ) (hs : s ≠ 0) (j : ℕ) :
    s ^ (2 * j) • embed (V := V)
      (signedTracePower (complexifiedMatrix (fun a => s⁻¹ • B a) η) j) =
    embed (V := V) (signedTracePower (complexifiedMatrix B η) j) := by
  rw [signedTrace_coefficients_smul]
  have hm := (embed (V := V)).toLinearMap.map_smul (s⁻¹ ^ (2 * j))
    (signedTracePower (complexifiedMatrix B η) j)
  change embed (V := V) (s⁻¹ ^ (2 * j) • signedTracePower (complexifiedMatrix B η) j) =
    s⁻¹ ^ (2 * j) • embed (V := V) (signedTracePower (complexifiedMatrix B η) j) at hm
  rw [hm, smul_smul]
  simp [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hs)]

theorem weighted_inverse_eq (Q : QuaternionicStructure V) (b : Basis ι ℝ V)
    (s : ℝ) (hs : s ≠ 0) (B : β → Matrix κ κ ℂ) (η : β → E V) :
    weightedValues (algebraMap ℝ (CE V) (s ^ 2))
      (densityValues Q b (fun a => s⁻¹ • B a) η) = normalizedValues Q b s B η := by
  funext i
  fin_cases i <;>
    simp only [weightedValues, densityValues, normalizedValues, Matrix.cons_val_zero,
      ← map_pow, ← Algebra.smul_def, ← pow_mul]
  · rfl
  · exact inverse_scaled_trace B η s hs 1
  · exact inverse_scaled_trace B η s hs 2
  · exact inverse_scaled_trace B η s hs 3
  · exact inverse_scaled_trace B η s hs 4
  · exact inverse_scaled_trace B η s hs 5

theorem normalized_density11 (Q : QuaternionicStructure V) (b : Basis ι ℝ V)
    (s : ℝ) (hs : s ≠ 0) (B : β → Matrix κ κ ℂ) (η : β → E V) :
    aeval (normalizedValues Q b s B η) density11 =
      s ^ 22 • aeval (densityValues Q b (fun a => s⁻¹ • B a) η) density11 := by
  rw [← weighted_inverse_eq Q b s hs B η, density11_eval_scale]
  simp only [← map_pow, ← pow_mul, ← Algebra.smul_def]

theorem normalized_density12 (Q : QuaternionicStructure V) (b : Basis ι ℝ V)
    (s : ℝ) (hs : s ≠ 0) (B : β → Matrix κ κ ℂ) (η : β → E V) :
    aeval (normalizedValues Q b s B η) density12 =
      s ^ 24 • aeval (densityValues Q b (fun a => s⁻¹ • B a) η) density12 := by
  rw [← weighted_inverse_eq Q b s hs B η, density12_eval_scale]
  simp only [← map_pow, ← pow_mul, ← Algebra.smul_def]

end
end QuaternionicSymmetry.QuaternionicNormalizedDensityValues
