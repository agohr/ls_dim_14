import QuaternionicSymmetry.ComplexAlgebraWedgePowers
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! Exact i/(2π) and half-complex-trace normalization for genuine matrix
wedge powers. The alternating signs cancel in every even power. -/
namespace QuaternionicSymmetry.ComplexEvenTraceNormalization
open ContinuousAlgebraWedgePowers ComplexAlgebraWedgePowers
open LocalChernWeilTracePowers
noncomputable section

theorem imaginary_scale_even (r : ℝ) (z : ℂ) (j : ℕ) :
    ((-1 : ℝ) ^ j / 2) * (((r : ℂ) * Complex.I) ^ (2 * j) * z).re =
      (r ^ (2 * j) / 2) * z.re := by
  have hc : ((r : ℂ) * Complex.I) ^ (2 * j) =
      (((-1 : ℝ) ^ j * r ^ (2 * j) : ℝ) : ℂ) := by
    rw [mul_pow, pow_mul Complex.I, Complex.I_sq]
    push_cast
    ring
  rw [hc, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hs : ((-1 : ℝ) ^ j) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm j 2, pow_mul]
    norm_num
  calc
    _ = (((-1 : ℝ) ^ j) ^ 2) * (r ^ (2 * j) / 2 * z.re) := by ring
    _ = _ := by rw [hs, one_mul]

variable {E κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype κ] [DecidableEq κ]
local instance : NormedRing (Matrix κ κ ℂ) := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ (Matrix κ κ ℂ) := Matrix.linftyOpNormedAlgebra
local instance : NormedAlgebra ℂ (Matrix κ κ ℂ) := Matrix.linftyOpNormedAlgebra
local instance : NormedSpace ℝ (Matrix κ κ ℂ) := NormedAlgebra.toNormedSpace _

theorem signed_even_trace (r : ℝ) (α : E [⋀^Fin 2]→L[ℝ] Matrix κ κ ℂ)
    (j : ℕ) (hj : 0 < j) (v : Fin (powerDegree (2 * j - 1)) → E) :
    ((-1 : ℝ) ^ j / 2) *
        (power (((r : ℂ) * Complex.I) • α) (2 * j - 1) v).trace.re =
      (r ^ (2 * j) / 2) * (power α (2 * j - 1) v).trace.re := by
  rw [power_smul]
  have he : 2 * j - 1 + 1 = 2 * j := by omega
  rw [he]
  simp only [ContinuousAlternatingMap.smul_apply, Matrix.trace_smul, smul_eq_mul]
  exact imaginary_scale_even r _ j

end
end QuaternionicSymmetry.ComplexEvenTraceNormalization
