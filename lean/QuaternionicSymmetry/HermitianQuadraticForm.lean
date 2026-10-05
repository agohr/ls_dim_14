import Mathlib.Analysis.Matrix.Spectrum

/-! Quadratic forms of finite Hermitian complex matrices and their unitary
spectral coordinates. -/

namespace QuaternionicSymmetry.HermitianQuadraticForm

open scoped BigOperators
open Matrix

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The real Hermitian quadratic form of a complex matrix. -/
def quad (Y : Matrix κ κ ℂ) (v : κ → ℂ) : ℝ :=
  (star v ⬝ᵥ (Y *ᵥ v)).re

/-- The rank-one matrix with column vector `v` and row vector `star v`. -/
def rankOne (v : κ → ℂ) : Matrix κ κ ℂ := Matrix.vecMulVec v (star v)

omit [DecidableEq κ] in
theorem trace_rankOne_mul (v : κ → ℂ) (Y : Matrix κ κ ℂ) :
    Matrix.trace (rankOne v * Y) = star v ⬝ᵥ (Y *ᵥ v) := by
  rw [rankOne, Matrix.vecMulVec_mul, Matrix.trace_vecMulVec, dotProduct_comm,
    Matrix.dotProduct_mulVec]

theorem quad_diagonal (lam : κ → ℝ) (v : κ → ℂ) :
    quad (Matrix.diagonal (fun i => (lam i : ℂ))) v = ∑ i, lam i * ‖v i‖ ^ 2 := by
  unfold quad
  unfold dotProduct
  simp_rw [Matrix.mulVec_diagonal]
  change (∑ i, star (v i) * ((lam i : ℂ) * v i)).re = ∑ i, lam i * ‖v i‖ ^ 2
  have hre : (∑ i, star (v i) * ((lam i : ℂ) * v i)).re =
      ∑ i, (star (v i) * ((lam i : ℂ) * v i)).re := by
    exact map_sum Complex.reAddGroupHom _ _
  rw [hre]
  apply Finset.sum_congr rfl
  intro i _
  rw [show star (v i) * ((lam i : ℂ) * v i) =
      (lam i : ℂ) * (star (v i) * v i) by ring]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

omit [DecidableEq κ] in
theorem quad_unitary_conjugate (U Y : Matrix κ κ ℂ) (v : κ → ℂ) :
    quad (U * Y * Uᴴ) v = quad Y (Uᴴ *ᵥ v) := by
  unfold quad
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec]
  have hstar : star (Uᴴ *ᵥ v) = star v ᵥ* U := by
    rw [Matrix.star_mulVec]
    simp
  rw [← hstar]

/-- The quadratic form in the canonical eigenvector coordinates. -/
theorem quad_spectral (Y : Matrix κ κ ℂ) (hY : Y.IsHermitian) (v : κ → ℂ) :
    quad Y v = ∑ i, hY.eigenvalues i *
      ‖(star (hY.eigenvectorUnitary : Matrix κ κ ℂ) *ᵥ v) i‖ ^ 2 := by
  conv_lhs => rw [hY.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply]
  rw [Matrix.star_eq_conjTranspose]
  rw [quad_unitary_conjugate]
  change quad (Matrix.diagonal (fun i => (hY.eigenvalues i : ℂ)))
    ((hY.eigenvectorUnitary : Matrix κ κ ℂ)ᴴ *ᵥ v) = _
  rw [quad_diagonal]

/-- Spectral coordinates for the quadratic form of a Hermitian matrix. -/
theorem isHermitian_spectral_quad (Y : Matrix κ κ ℂ) (hY : Y.IsHermitian) :
    ∃ (U : Matrix κ κ ℂ) (lam : κ → ℝ), U * Uᴴ = 1 ∧
      ∀ v, quad Y v = ∑ i, lam i * ‖(U *ᵥ v) i‖ ^ 2 := by
  let V : Matrix κ κ ℂ := hY.eigenvectorUnitary
  let U : Matrix κ κ ℂ := star V
  let lam : κ → ℝ := hY.eigenvalues
  refine ⟨U, lam, ?_, ?_⟩
  · dsimp [U, V]
    simpa [Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self hY.eigenvectorUnitary
  · intro v
    rw [hY.spectral_theorem]
    change quad (Unitary.conjStarAlgAut ℂ (Matrix κ κ ℂ) hY.eigenvectorUnitary
      (Matrix.diagonal (Complex.ofReal ∘ lam))) v = _
    simp only [Unitary.conjStarAlgAut_apply]
    change quad (V * Matrix.diagonal (Complex.ofReal ∘ lam) * Vᴴ) v = _
    rw [quad_unitary_conjugate]
    change quad (Matrix.diagonal (fun i => (lam i : ℂ))) (Vᴴ *ᵥ v) = _
    rw [quad_diagonal]
    simp [U, V, Matrix.star_eq_conjTranspose]


/-- The real trace of every power of a Hermitian matrix is the corresponding
power sum of its real eigenvalues. -/
theorem trace_pow_eq_sum_eigenvalues_pow (Y : Matrix κ κ ℂ) (hY : Y.IsHermitian) (k : ℕ) :
    (Matrix.trace (Y ^ k)).re = ∑ i, hY.eigenvalues i ^ k := by
  conv_lhs => rw [hY.spectral_theorem]
  rw [← map_pow]
  simp only [Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_cycle]
  rw [Unitary.coe_star_mul_self]
  simp only [Matrix.one_mul, Matrix.diagonal_pow, Matrix.trace_diagonal]
  have hre : (∑ i, ((hY.eigenvalues i : ℂ) ^ k)).re =
      ∑ i, ((hY.eigenvalues i : ℂ) ^ k).re := by
    exact map_sum Complex.reAddGroupHom _ _
  simp only [Function.comp_apply, Pi.pow_apply]
  change (∑ i, ((hY.eigenvalues i : ℂ) ^ k)).re = _
  rw [hre]
  apply Finset.sum_congr rfl
  intro i _
  norm_cast

end
end QuaternionicSymmetry.HermitianQuadraticForm
