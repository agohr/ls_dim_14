import QuaternionicSymmetry.QuaternionicE14OrbitalPointwise
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Zero-block enlargement for the paper's fixed orbital rank. -/
namespace QuaternionicSymmetry.KillingFieldsPaperMatrixPadding
open Matrix
noncomputable section
variable {n N : ℕ}

/-- The first `n` coordinate columns of the identity matrix of size `N`. -/
def inclusion (R : Type*) [Zero R] [One R] (h : n ≤ N) : Matrix (Fin N) (Fin n) R :=
  (1 : Matrix (Fin N) (Fin N) R).submatrix id (Fin.castLE h)

variable {R : Type*} [CommRing R]

theorem inclusion_transpose_mul (h : n ≤ N) :
    (inclusion R h)ᵀ * inclusion R h = 1 := by
  rw [show (inclusion R h)ᵀ =
    (1 : Matrix (Fin N) (Fin N) R).submatrix (Fin.castLE h) (Equiv.refl _) by
      ext i j; simp [inclusion, Matrix.one_apply, eq_comm]]
  rw [Matrix.one_submatrix_mul]
  ext i j
  simp [inclusion, Matrix.one_apply, Fin.ext_iff]

/-- Both quaternionic coordinate blocks are enlarged by the same injection. -/
def doubledInclusion (h : n ≤ N) : Matrix (Fin N ⊕ Fin N) (Fin n ⊕ Fin n) R :=
  Matrix.fromBlocks (inclusion R h) 0 0 (inclusion R h)

theorem doubled_transpose_mul (h : n ≤ N) :
    (doubledInclusion (R := R) h)ᵀ * doubledInclusion (R := R) h = 1 := by
  simp [doubledInclusion, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    inclusion_transpose_mul, Matrix.fromBlocks_one]

def pad (h : n ≤ N) (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) R :=
  doubledInclusion h * A * (doubledInclusion h)ᵀ

theorem pad_mul (h : n ≤ N) (A B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :
    pad h (A * B) = pad h A * pad h B := by
  simp only [pad, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (doubledInclusion h)ᵀ, doubled_transpose_mul, Matrix.one_mul]

theorem pad_pow (h : n ≤ N) (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
    (k : ℕ) (hk : 0 < k) : pad h (A ^ k) = pad h A ^ k := by
  cases k with
  | zero => omega
  | succ k =>
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ A, pad_mul, ih (by omega)]
      exact (pow_succ (pad h A) (k+1)).symm

theorem trace_pad (h : n ≤ N) (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :
    Matrix.trace (pad h A) = Matrix.trace A := by
  rw [pad, Matrix.trace_mul_comm, ← Matrix.mul_assoc, doubled_transpose_mul,
    Matrix.one_mul]

theorem doubled_J (h : n ≤ N) :
    CompactSymplecticHaar.standardJ N * doubledInclusion (R := ℂ) h =
      doubledInclusion h * CompactSymplecticHaar.standardJ n := by
  simp [doubledInclusion, CompactSymplecticHaar.standardJ, Matrix.fromBlocks_multiply]

theorem doubled_transpose_J (h : n ≤ N) :
    (doubledInclusion (R := ℂ) h)ᵀ * CompactSymplecticHaar.standardJ N =
      CompactSymplecticHaar.standardJ n * (doubledInclusion h)ᵀ := by
  simp [doubledInclusion, CompactSymplecticHaar.standardJ,
    Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]

theorem doubled_conjTranspose (h : n ≤ N) :
    (doubledInclusion (R := ℂ) h)ᴴ = (doubledInclusion h)ᵀ := by
  ext (i | i) (j | j) <;>
    simp [doubledInclusion, inclusion, Matrix.conjTranspose_apply, Matrix.one_apply]

theorem pad_hermitianAntiSelfDual (h : n ≤ N)
    (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hA : QuaternionicMatrixModel.HermitianAntiSelfDual A) :
    QuaternionicMatrixModel.HermitianAntiSelfDual (pad h A) := by
  constructor
  · simp only [pad, Matrix.conjTranspose_mul, hA.1, doubled_conjTranspose]
    have hc : ((doubledInclusion (R := ℂ) h)ᵀ)ᴴ = doubledInclusion h := by
      rw [← doubled_conjTranspose, Matrix.conjTranspose_conjTranspose]
    rw [hc, Matrix.mul_assoc]
  · have hs : Complex.I • pad h A = pad h (Complex.I • A) := by
      simp only [pad, Matrix.mul_smul, Matrix.smul_mul]
    rw [hs, pad, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    calc
      _ = doubledInclusion h *
          ((Complex.I • A)ᵀ * CompactSymplecticHaar.standardJ n +
            CompactSymplecticHaar.standardJ n * (Complex.I • A)) *
          (doubledInclusion h)ᵀ := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
        rw [doubled_transpose_J]
        rw [← Matrix.mul_assoc (CompactSymplecticHaar.standardJ N), doubled_J]
        simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hA.2]; simp

variable {β : Type*} [Fintype β]

open MatrixTracePolynomial

theorem combination_pad (h : n ≤ N)
    (A : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (x : β → ℝ) :
    matrixCombination (fun b => pad h (A b)) x = pad h (matrixCombination A x) := by
  simp only [matrixCombination, pad, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul]

theorem tracePowerPolynomial_pad (h : n ≤ N)
    (A : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (r : ℕ) (hr : 0 < r) :
    tracePowerPolynomial (fun b => pad h (A b)) r = tracePowerPolynomial A r := by
  apply MvPolynomial.funext
  intro x
  change MvPolynomial.eval x _ = MvPolynomial.eval x _
  rw [eval_tracePowerPolynomial, eval_tracePowerPolynomial, combination_pad]
  unfold CompactSymplecticTraceInvariants.evenTracePower
  rw [← pad_pow h _ (2*r) (by omega), trace_pad]

variable {T : Type*} [CommRing T] [Algebra ℝ T]

theorem signedTracePower_pad (h : n ≤ N)
    (A : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (η : β → T) (r : ℕ) (hr : 0 < r) :
    signedTracePower (complexifiedMatrix (fun b => pad h (A b)) η) r =
      signedTracePower (complexifiedMatrix A η) r := by
  unfold signedTracePower
  rw [← aeval_tracePowerPolynomial, ← aeval_tracePowerPolynomial,
    tracePowerPolynomial_pad h A r hr]

end
end QuaternionicSymmetry.KillingFieldsPaperMatrixPadding
