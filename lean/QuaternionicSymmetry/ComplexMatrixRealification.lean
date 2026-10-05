import QuaternionicSymmetry.ComplexGaussianVariable
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-! A unitary complex matrix acts by an orthogonal matrix on real and
imaginary coordinates, compatibly with the normalized Gaussian vector. -/

namespace QuaternionicSymmetry.ComplexMatrixRealification

open scoped BigOperators

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def realify (U : Matrix κ κ ℂ) : Matrix (κ × Fin 2) (κ × Fin 2) ℝ :=
  fun i j => if i.2 = 0 then
    (if j.2 = 0 then (U i.1 j.1).re else -(U i.1 j.1).im)
    else (if j.2 = 0 then (U i.1 j.1).im else (U i.1 j.1).re)

theorem realify_rows (U : Matrix κ κ ℂ) (hU : U * U.conjTranspose = 1)
    (i j : κ × Fin 2) :
    ∑ k, realify U i k * realify U j k = if i = j then 1 else 0 := by
  rcases i with ⟨i, a⟩
  rcases j with ⟨j, b⟩
  have hc : ∑ k, U i k * star (U j k) = if i = j then 1 else 0 := by
    have h := congrArg (fun M : Matrix κ κ ℂ => M i j) hU
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using h
  have hr : (∑ k, ((U i k).re * (U j k).re + (U i k).im * (U j k).im)) =
      if i = j then 1 else 0 := by
    simpa [Complex.mul_re, apply_ite] using congrArg Complex.re hc
  have hi : (∑ k, (-(U i k).re * (U j k).im + (U i k).im * (U j k).re)) = 0 := by
    simpa [Complex.mul_im, apply_ite] using congrArg Complex.im hc
  fin_cases a <;> fin_cases b <;>
    norm_num [realify, Fintype.sum_prod_type, Fin.sum_univ_two]
  · exact hr
  · have h := congrArg Neg.neg hi
    simpa only [neg_zero, ← Finset.sum_neg_distrib, neg_add_rev, neg_neg, mul_neg,
      neg_mul, add_comm] using h
  · simpa only [mul_neg, neg_mul, add_comm] using hi
  · simpa only [add_comm] using hr

def complexVector (x : κ × Fin 2 → ℝ) : κ → ℂ :=
  fun i => ⟨x (i, 0), x (i, 1)⟩

omit [DecidableEq κ] in
theorem complexVector_mulVec (U : Matrix κ κ ℂ) (x : κ × Fin 2 → ℝ) :
    complexVector (Matrix.mulVec (realify U) x) = Matrix.mulVec U (complexVector x) := by
  funext i
  apply Complex.ext <;>
    simp [complexVector, Matrix.mulVec, dotProduct, realify, Fintype.sum_prod_type,
      Fin.sum_univ_two, Complex.mul_re, Complex.mul_im, sub_eq_add_neg]
  simp only [add_comm]

def gaussianVector (x : κ × Fin 2 → ℝ) : κ → ℂ :=
  fun i => ComplexGaussianVariable.standardComplex (fun k => x (i, k))

omit [Fintype κ] [DecidableEq κ] in
theorem gaussianVector_eq (x : κ × Fin 2 → ℝ) :
    gaussianVector x = (Real.sqrt 2 : ℂ)⁻¹ • complexVector x := by
  funext i
  simp only [gaussianVector, ComplexGaussianVariable.standardComplex, complexVector,
    Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

omit [DecidableEq κ] in
theorem gaussianVector_mulVec (U : Matrix κ κ ℂ) (x : κ × Fin 2 → ℝ) :
    gaussianVector (Matrix.mulVec (realify U) x) = Matrix.mulVec U (gaussianVector x) := by
  rw [gaussianVector_eq, gaussianVector_eq, complexVector_mulVec, Matrix.mulVec_smul]

end
end QuaternionicSymmetry.ComplexMatrixRealification
