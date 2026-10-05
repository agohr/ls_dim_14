import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic

/-!
# The arbitrary-rank leading odd-determinant coefficient

The symplectic Harish--Chandra expression of Forrester--Ipsen--Liu--Zhang,
arXiv:1711.10691v1, Eq. (1.8), has the odd determinant
`det[2 sinh(t xᵢ yⱼ)]`. Here we compute the determinant formed from the
first `n` odd powers over `ℚ`, for arbitrary rank `n`. After multiplication
by the source's normalization constant, this finite determinant is exactly
`t^(n²)` times the two odd Vandermondes. Identifying it with the leading
term of the full odd kernel is a separate formal-series obligation. -/

namespace QuaternionicSymmetry.OrbitalOddDeterminantBase

open Matrix Finset

noncomputable section

def oddAlternant {n : ℕ} (x : Fin n → ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j => x i ^ (2 * j.val + 1)

def oddVandermonde {n : ℕ} (x : Fin n → ℚ) : ℚ :=
  (∏ i, x i) * ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, ((x j) ^ 2 - (x i) ^ 2)

theorem det_oddAlternant {n : ℕ} (x : Fin n → ℚ) :
    (oddAlternant x).det = oddVandermonde x := by
  have hmatrix : oddAlternant x =
      Matrix.of fun i j => x i * (Matrix.vandermonde (fun i => (x i) ^ 2)) i j := by
    ext i j
    simp [oddAlternant, Matrix.vandermonde_apply, pow_mul, pow_add]
    ring
  rw [hmatrix, Matrix.det_mul_column, Matrix.det_vandermonde]
  rfl

def oddWeight {n : ℕ} (t : ℚ) (k : Fin n) : ℚ :=
  t ^ (2 * k.val + 1) / (Nat.factorial (2 * k.val + 1) : ℚ)

/-- The finite odd-kernel matrix uses the first `n` terms of each `sinh`
entry. -/
def truncatedOddKernel {n : ℕ} (x y : Fin n → ℚ) (t : ℚ) :
    Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j => ∑ k : Fin n,
    (x i * y j * t) ^ (2 * k.val + 1) /
      (Nat.factorial (2 * k.val + 1) : ℚ)

theorem truncatedOddKernel_eq_mul {n : ℕ} (x y : Fin n → ℚ) (t : ℚ) :
    truncatedOddKernel x y t =
      oddAlternant x * Matrix.diagonal (oddWeight t) * (oddAlternant y)ᵀ := by
  ext i j
  simp [truncatedOddKernel, oddAlternant, oddWeight,
    Matrix.mul_apply, Matrix.diagonal_apply]
  apply Finset.sum_congr rfl
  intro k _
  ring

def normalizer (n : ℕ) : ℚ :=
  ∏ k : Fin n, (Nat.factorial (2 * k.val + 1) : ℚ)

/-- The constant `c_n^(odd) = ∏_{j=1}^n Γ(2j)/2` in the cited source. -/
def sourceConstant (n : ℕ) : ℚ :=
  ∏ k : Fin n, (Nat.factorial (2 * k.val + 1) : ℚ) / 2

theorem sourceConstant_mul_twoPow (n : ℕ) :
    sourceConstant n * (2 : ℚ) ^ n = normalizer n := by
  unfold sourceConstant normalizer
  calc
    (∏ k : Fin n, (Nat.factorial (2 * k.val + 1) : ℚ) / 2) * (2 : ℚ) ^ n =
        (∏ k : Fin n, (Nat.factorial (2 * k.val + 1) : ℚ) / 2) *
          (∏ _k : Fin n, (2 : ℚ)) := by simp
    _ = ∏ k : Fin n, ((Nat.factorial (2 * k.val + 1) : ℚ) / 2) * 2 := by
      rw [← Finset.prod_mul_distrib]
    _ = ∏ k : Fin n, (Nat.factorial (2 * k.val + 1) : ℚ) := by
      apply Finset.prod_congr rfl
      intro k _
      ring

def sourceTruncatedOddKernel {n : ℕ} (x y : Fin n → ℚ) (t : ℚ) :
    Matrix (Fin n) (Fin n) ℚ :=
  (2 : ℚ) • truncatedOddKernel x y t

theorem sum_odd (n : ℕ) :
    (∑ k : Fin n, (2 * k.val + 1)) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, ih]
      ring

/-- Exact all-rank normalization of the finite odd determinant. The
factor `normalizer` is the source constant `c_n^(odd) * 2^n`: the source
determinant has entries `2 sinh`, while this matrix has entries `sinh`. -/
theorem normalized_truncatedOddKernel {n : ℕ} (x y : Fin n → ℚ) (t : ℚ) :
    normalizer n * (truncatedOddKernel x y t).det =
      t ^ (n ^ 2) * oddVandermonde x * oddVandermonde y := by
  rw [truncatedOddKernel_eq_mul, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_diagonal, Matrix.det_transpose,
    det_oddAlternant, det_oddAlternant]
  have hweight : normalizer n * (∏ k : Fin n, oddWeight t k) =
      ∏ k : Fin n, t ^ (2 * k.val + 1) := by
    unfold normalizer
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro k _
    unfold oddWeight
    have hf : (Nat.factorial (2 * k.val + 1) : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero _
    field_simp
  rw [Finset.prod_pow_eq_pow_sum, sum_odd] at hweight
  calc
    normalizer n * ((oddVandermonde x * ∏ i : Fin n, oddWeight t i) * oddVandermonde y) =
        (normalizer n * ∏ i : Fin n, oddWeight t i) * oddVandermonde x * oddVandermonde y := by ring
    _ = t ^ (n ^ 2) * oddVandermonde x * oddVandermonde y := by rw [hweight]

/-- The same all-rank finite identity using exactly the source's
`c_n^(odd)` and `2 sinh` conventions. -/
theorem normalized_sourceTruncatedOddKernel {n : ℕ}
    (x y : Fin n → ℚ) (t : ℚ) :
    sourceConstant n * (sourceTruncatedOddKernel x y t).det =
      t ^ (n ^ 2) * oddVandermonde x * oddVandermonde y := by
  rw [sourceTruncatedOddKernel, Matrix.det_smul, Fintype.card_fin,
    ← mul_assoc, sourceConstant_mul_twoPow]
  exact normalized_truncatedOddKernel x y t

end
end QuaternionicSymmetry.OrbitalOddDeterminantBase
