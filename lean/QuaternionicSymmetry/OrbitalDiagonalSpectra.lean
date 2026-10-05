import QuaternionicSymmetry.OrbitalSourceConventions
import QuaternionicSymmetry.OrbitalHaarPositiveParameter

/-! Concrete diagonal spectra and their normalization in the orbital formula. -/

namespace QuaternionicSymmetry.OrbitalDiagonalSpectra

open Matrix CompactSymplecticHaar OrbitalSourceConventions OrbitalAnalyticOddKernel
  OrbitalOddDeterminantBase

noncomputable section

def hermitianDiagonal {n : ℕ} (x : Fin n → ℝ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  Matrix.diagonal (Sum.elim (fun i => (x i : ℂ)) (fun i => -(x i : ℂ)))

def antiHermitianDiagonal {n : ℕ} (x : Fin n → ℝ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  Complex.I • hermitianDiagonal x

theorem hermitianDiagonal_conjTranspose {n : ℕ} (x : Fin n → ℝ) :
    (hermitianDiagonal x)ᴴ = hermitianDiagonal x := by
  rw [hermitianDiagonal, Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  cases i <;> simp

theorem antiHermitianDiagonal_conjTranspose {n : ℕ} (x : Fin n → ℝ) :
    (antiHermitianDiagonal x)ᴴ = -antiHermitianDiagonal x := by
  simp [antiHermitianDiagonal, Matrix.conjTranspose_smul,
    hermitianDiagonal_conjTranspose, neg_smul]

theorem hermitianArgument_antiHermitianDiagonal {n : ℕ} (x : Fin n → ℝ) :
    hermitianArgument (antiHermitianDiagonal x) = hermitianDiagonal x := by
  simp [hermitianArgument, antiHermitianDiagonal, smul_smul]

theorem hermitianDiagonal_scale {n : ℕ} (x : Fin n → ℝ) (t : ℝ) :
    hermitianDiagonal (fun i => t * x i) = (t : ℂ) • hermitianDiagonal x := by
  ext i j
  simp only [hermitianDiagonal, Matrix.diagonal_apply, Matrix.smul_apply,
    smul_eq_mul]
  split_ifs with h
  · cases i <;> simp
  · simp

theorem halfTrace_diagonal_scale {n : ℕ} (x y : Fin n → ℝ) (t : ℝ)
    (g : CompactSymplecticHaar.Group n) :
    halfTrace (standardJ n) (hermitianDiagonal (fun i => t * x i))
      (hermitianDiagonal y) g =
      t * halfTrace (standardJ n) (hermitianDiagonal x) (hermitianDiagonal y) g := by
  rw [hermitianDiagonal_scale]
  simp only [halfTrace, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

def realOddVandermonde {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  (∏ i, x i) * ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, ((x j) ^ 2 - (x i) ^ 2)

theorem realOddVandermonde_rat {n : ℕ} (x : Fin n → ℚ) :
    realOddVandermonde (fun i => (x i : ℝ)) = (oddVandermonde x : ℝ) := by
  simp [realOddVandermonde, oddVandermonde]

theorem realOddVandermonde_eq_det {n : ℕ} (x : Fin n → ℝ) :
    realOddVandermonde x = (Matrix.of fun i j : Fin n => x i ^ (2 * j.val + 1)).det := by
  have hmatrix : (Matrix.of fun i j : Fin n => x i ^ (2 * j.val + 1)) =
      Matrix.of fun i j => x i * Matrix.vandermonde (fun i => x i ^ 2) i j := by
    ext i j
    simp only [Matrix.of_apply, Matrix.vandermonde_apply]
    ring
  rw [hmatrix, Matrix.det_mul_column, Matrix.det_vandermonde]
  rfl

theorem realOddVandermonde_scale {n : ℕ} (x : Fin n → ℝ) (t : ℝ) :
    realOddVandermonde (fun i => t * x i) = t ^ (n ^ 2) * realOddVandermonde x := by
  rw [realOddVandermonde_eq_det, realOddVandermonde_eq_det]
  simp only [mul_pow]
  rw [Matrix.det_mul_row, Finset.prod_pow_eq_pow_sum, sum_odd]
  rfl

def realSourceDeterminant {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  (Matrix.of fun i j => 2 * Real.sinh (x i * y j)).det

theorem realSourceDeterminant_rat_scale {n : ℕ} (x y : Fin n → ℚ) (t : ℝ) :
    realSourceDeterminant (fun i => t * (x i : ℝ)) (fun i => (y i : ℝ)) =
      (sourceDeterminant x y : ℝ → ℝ) t := by
  rw [sourceDeterminant_apply]
  unfold realSourceDeterminant
  congr 1
  ext i j
  simp only [Matrix.of_apply]
  congr 2
  ring

end
end QuaternionicSymmetry.OrbitalDiagonalSpectra
