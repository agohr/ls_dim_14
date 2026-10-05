import QuaternionicSymmetry.UnitaryProjectionCubic
import QuaternionicSymmetry.UnitaryProjectionMoments
import QuaternionicSymmetry.HermitianQuadraticForm

/-! Spectral conjugation transfers the rank-two cubic formula from diagonal
matrices to all numerical Hermitian matrices. -/

namespace QuaternionicSymmetry.HermitianProjectionMoments

open Matrix MeasureTheory UnitaryProjectionDiagonal
open scoped BigOperators

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem trace_diagonal (s : Finset κ) (U : Matrix.unitaryGroup κ ℂ) (y : κ → ℝ) :
    (Matrix.trace (UnitaryProjection.projection s U * Matrix.diagonal (fun i => (y i : ℂ)))).re =
      ∑ i, y i * entry s U i := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    entry_eq_re, mul_comm]

theorem trace_conjugate (s : Finset κ) (U V : Matrix.unitaryGroup κ ℂ)
    (Y : Matrix κ κ ℂ) :
    Matrix.trace (UnitaryProjection.projection s U *
      ((V : Matrix κ κ ℂ) * Y * star (V : Matrix κ κ ℂ))) =
    Matrix.trace (UnitaryProjection.projection s (V⁻¹ * U) * Y) := by
  rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  simp only [UnitaryProjection.projection, Matrix.UnitaryGroup.mul_val,
    Matrix.UnitaryGroup.inv_val, Matrix.star_mul, star_star, Matrix.mul_assoc]

theorem integral_trace_cube (s : Finset κ) (hs : s.card = 2)
    (hr : 3 ≤ Fintype.card κ) (Y : Matrix κ κ ℂ) (hY : Y.IsHermitian) :
    (∫ U : Matrix.unitaryGroup κ ℂ, (Matrix.trace (UnitaryProjection.projection s U * Y)).re ^ 3
      ∂UnitaryHaarMeasure.probability) =
    4 * ((2 * (Fintype.card κ : ℝ) + 1) * (Matrix.trace Y).re ^ 3 +
      3 * (Fintype.card κ - 1) * (Matrix.trace Y).re * (Matrix.trace (Y ^ 2)).re +
      (Fintype.card κ - 4) * (Matrix.trace (Y ^ 3)).re) /
      ((Fintype.card κ : ℝ) * (Fintype.card κ - 1) * (Fintype.card κ + 1) *
        (Fintype.card κ + 2)) := by
  have he (U : Matrix.unitaryGroup κ ℂ) :
      (Matrix.trace (UnitaryProjection.projection s U * Y)).re =
        ∑ i, hY.eigenvalues i * entry s (hY.eigenvectorUnitary⁻¹ * U) i := by
    conv_lhs => rw [hY.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply]
    rw [trace_conjugate]
    exact trace_diagonal s _ hY.eigenvalues
  simp_rw [he]
  rw [UnitaryHaarMeasure.integral_mul_left
    (fun U => (∑ i, hY.eigenvalues i * entry s U i) ^ 3) hY.eigenvectorUnitary⁻¹]
  rw [UnitaryProjectionCubic.integral_weighted_cube s hs hr]
  have h₁ := HermitianQuadraticForm.trace_pow_eq_sum_eigenvalues_pow Y hY 1
  simp only [pow_one] at h₁
  rw [h₁, HermitianQuadraticForm.trace_pow_eq_sum_eigenvalues_pow Y hY 2,
    HermitianQuadraticForm.trace_pow_eq_sum_eigenvalues_pow Y hY 3]

omit [Fintype κ] [DecidableEq κ] in
theorem ofReal_re_of_star_eq (z : ℂ) (h : star z = z) : (z.re : ℂ) = z := by
  apply Complex.ext
  · simp
  · have hi := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at hi
    simp only [Complex.ofReal_im]
    linarith

omit [DecidableEq κ] in
theorem ofReal_re_trace (Y : Matrix κ κ ℂ) (hY : Y.IsHermitian) :
    ((Matrix.trace Y).re : ℂ) = Matrix.trace Y := by
  apply ofReal_re_of_star_eq
  rw [← Matrix.trace_conjTranspose, hY.eq]

omit [DecidableEq κ] in
theorem ofReal_re_trace_mul (A Y : Matrix κ κ ℂ) (hA : A.IsHermitian) (hY : Y.IsHermitian) :
    ((Matrix.trace (A * Y)).re : ℂ) = Matrix.trace (A * Y) := by
  apply ofReal_re_of_star_eq
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA.eq, hY.eq,
    Matrix.trace_mul_comm]

theorem moment_eq_integral_real (s : Finset κ) (Y : Matrix κ κ ℂ) (hY : Y.IsHermitian) (k : ℕ) :
    UnitaryProjectionMoments.moment s Y k =
      ((∫ U : Matrix.unitaryGroup κ ℂ,
        (Matrix.trace (UnitaryProjection.projection s U * Y)).re ^ k
        ∂UnitaryHaarMeasure.probability : ℝ) : ℂ) := by
  have he (U : Matrix.unitaryGroup κ ℂ) :
      Matrix.trace ((UnitaryProjection.projection s U).map (algebraMap ℂ ℂ) * Y) ^ k =
        (((Matrix.trace (UnitaryProjection.projection s U * Y)).re ^ k : ℝ) : ℂ) := by
    simp only [Algebra.algebraMap_self, Matrix.map, RingHom.id_apply, Complex.ofReal_pow,
      ofReal_re_trace_mul _ _ (UnitaryProjection.projection_isHermitian s U) hY]
    rfl
  apply Complex.ext
  · have h := UnitaryProjectionMoments.integral_scalar s Y k Complex.reLm
    simp only [he, Complex.reLm_coe, Complex.ofReal_re] at h ⊢
    exact h.symm
  · have h := UnitaryProjectionMoments.integral_scalar s Y k Complex.imLm
    simp only [he, Complex.imLm_coe, Complex.ofReal_im, integral_zero] at h ⊢
    exact h.symm

theorem moment_three_complex (s : Finset κ) (hs : s.card = 2)
    (hr : 3 ≤ Fintype.card κ) (Y : Matrix κ κ ℂ) (hY : Y.IsHermitian) :
    UnitaryProjectionMoments.moment s Y 3 =
      (4 / ((Fintype.card κ : ℂ) * (Fintype.card κ - 1) * (Fintype.card κ + 1) *
        (Fintype.card κ + 2))) *
      ((2 * (Fintype.card κ : ℂ) + 1) * Matrix.trace Y ^ 3 +
        3 * (Fintype.card κ - 1) * Matrix.trace Y * Matrix.trace (Y ^ 2) +
        (Fintype.card κ - 4) * Matrix.trace (Y ^ 3)) := by
  rw [moment_eq_integral_real s Y hY, integral_trace_cube s hs hr Y hY]
  push_cast
  rw [ofReal_re_trace Y hY, ofReal_re_trace (Y ^ 2) (hY.pow 2),
    ofReal_re_trace (Y ^ 3) (hY.pow 3)]
  ring

end
end QuaternionicSymmetry.HermitianProjectionMoments
