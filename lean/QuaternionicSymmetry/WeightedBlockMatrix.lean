import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import QuaternionicSymmetry.HermitianQuadraticForm

/-! Weighted repeated blocks turn a finite sum of Gaussian quadratic forms
into one larger Hermitian quadratic form. -/

namespace QuaternionicSymmetry.WeightedBlockMatrix

open Matrix
open scoped BigOperators Kronecker

noncomputable section

variable {α κ : Type*} [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]

variable {S : Type*} [CommRing S] [Algebra ℝ S]

def block (q : α → ℝ) (Y : Matrix κ κ S) : Matrix (α × κ) (α × κ) S :=
  Matrix.kronecker (Matrix.diagonal (fun m => algebraMap ℝ S (q m))) Y

omit [Fintype α] [Fintype κ] [DecidableEq κ] in
theorem block_isHermitian (q : α → ℝ) (Y : Matrix κ κ ℂ) (hY : Y.IsHermitian) :
    (block q Y).IsHermitian := by
  change (block q Y)ᴴ = block q Y
  rw [block]
  change (Matrix.kroneckerMap (fun x y : ℂ => x * y)
    (Matrix.diagonal (fun m => (q m : ℂ))) Y)ᴴ =
      Matrix.kroneckerMap (fun x y : ℂ => x * y)
        (Matrix.diagonal (fun m => (q m : ℂ))) Y
  rw [Matrix.conjTranspose_kronecker, hY.eq]
  congr 1
  ext i j
  by_cases h : i = j
  · subst j
    simp [Matrix.diagonal]
  · have h' : ¬j = i := fun hji => h hji.symm
    simp [Matrix.diagonal, h, h']

theorem block_pow (q : α → ℝ) (Y : Matrix κ κ S) (k : ℕ) :
    block q Y ^ k = Matrix.kronecker
      (Matrix.diagonal (fun m => (algebraMap ℝ S (q m)) ^ k)) (Y ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ih]
      change Matrix.kroneckerMap (fun x y : S => x * y)
          (Matrix.diagonal (fun m => (algebraMap ℝ S (q m)) ^ k)) (Y ^ k) *
          Matrix.kroneckerMap (fun x y : S => x * y)
            (Matrix.diagonal (fun m => algebraMap ℝ S (q m))) Y = _
      rw [← Matrix.mul_kronecker_mul, Matrix.diagonal_mul_diagonal]
      change Matrix.kroneckerMap (fun x y : S => x * y)
          (Matrix.diagonal (fun m => (algebraMap ℝ S (q m)) ^ k * algebraMap ℝ S (q m)))
          (Y ^ k * Y) =
        Matrix.kroneckerMap (fun x y : S => x * y)
          (Matrix.diagonal (fun m => (algebraMap ℝ S (q m)) ^ (k + 1))) (Y ^ (k + 1))
      simp [pow_succ]

theorem trace_block_pow (q : α → ℝ) (Y : Matrix κ κ S) (k : ℕ) :
    Matrix.trace (block q Y ^ k) = (∑ m, algebraMap ℝ S (q m) ^ k) * Matrix.trace (Y ^ k) := by
  rw [block_pow]
  change Matrix.trace (Matrix.kroneckerMap (fun x y : S => x * y)
    (Matrix.diagonal (fun m => (algebraMap ℝ S (q m)) ^ k)) (Y ^ k)) = _
  rw [Matrix.trace_kronecker, Matrix.trace_diagonal]

theorem re_trace_block_pow (q : α → ℝ) (Y : Matrix κ κ ℂ) (k : ℕ) :
  (Matrix.trace (block q Y ^ k)).re =
      (∑ m, q m ^ k) * (Matrix.trace (Y ^ k)).re := by
  rw [trace_block_pow]
  change ((∑ m, (q m : ℂ) ^ k) * Matrix.trace (Y ^ k)).re = _
  rw [Complex.mul_re]
  have hre : (∑ m, ((q m : ℂ) ^ k).re) = ∑ m, q m ^ k := by
    apply Finset.sum_congr rfl
    intro m hm
    exact (congrArg Complex.re (Complex.ofReal_pow (q m) k)).symm.trans
      (Complex.ofReal_re _)
  have him : (∑ m, ((q m : ℂ) ^ k).im) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    exact (congrArg Complex.im (Complex.ofReal_pow (q m) k)).symm.trans
      (Complex.ofReal_im _)
  have hsumre : (∑ m, ((q m : ℂ) ^ k)).re =
      ∑ m, ((q m : ℂ) ^ k).re :=
    map_sum Complex.reAddGroupHom _ _
  have hsumim : (∑ m, ((q m : ℂ) ^ k)).im =
      ∑ m, ((q m : ℂ) ^ k).im :=
    map_sum Complex.imAddGroupHom _ _
  rw [hsumre, hsumim, hre, him]
  ring

omit [DecidableEq κ] in
theorem mulVec_block (q : α → ℝ) (Y : Matrix κ κ ℂ) (v : α × κ → ℂ)
    (m : α) (i : κ) :
    (block q Y *ᵥ v) (m, i) = (q m : ℂ) * (Y *ᵥ fun j => v (m, j)) i := by
  simp [block, Matrix.mulVec, dotProduct, Matrix.diagonal,
    Fintype.sum_prod_type, ← Finset.mul_sum, mul_assoc]

omit [DecidableEq κ] in
theorem quad_block (q : α → ℝ) (Y : Matrix κ κ ℂ) (v : α × κ → ℂ) :
    HermitianQuadraticForm.quad (block q Y) v =
      ∑ m, q m * HermitianQuadraticForm.quad Y (fun i => v (m, i)) := by
  unfold HermitianQuadraticForm.quad
  change (∑ p : α × κ, star (v p) * ((block q Y *ᵥ v) p)).re =
    ∑ m, q m * (∑ i, star (v (m, i)) *
      ((Y *ᵥ fun j => v (m, j)) i)).re
  have houter : (∑ p : α × κ, star (v p) * ((block q Y *ᵥ v) p)).re =
      ∑ p : α × κ, (star (v p) * ((block q Y *ᵥ v) p)).re :=
    map_sum Complex.reAddGroupHom _ _
  rw [houter]
  rw [Fintype.sum_prod_type]
  simp_rw [mulVec_block]
  apply Finset.sum_congr rfl
  intro m hm
  have hsum : (∑ x, (star (v (m, x)) *
      ((q m : ℂ) * (Y *ᵥ fun j => v (m, j)) x)).re) =
      ∑ x, q m * (star (v (m, x)) *
        ((Y *ᵥ fun j => v (m, j)) x)).re := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Complex.mul_re]
    simp [Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hreal : (∑ i, star (v (m, i)) *
      ((Y *ᵥ fun j => v (m, j)) i)).re =
      ∑ i, (star (v (m, i)) *
        ((Y *ᵥ fun j => v (m, j)) i)).re :=
    map_sum Complex.reAddGroupHom _ _
  rw [hreal, Finset.mul_sum]
  exact hsum

end
end QuaternionicSymmetry.WeightedBlockMatrix
