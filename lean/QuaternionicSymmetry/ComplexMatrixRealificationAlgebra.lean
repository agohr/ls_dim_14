import QuaternionicSymmetry.ComplexMatrixRealification
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Realification preserves matrix products and doubles the real trace.
These identities also provide a continuous multiplicative coefficient map
for normalized matrix-valued wedge powers. -/
namespace QuaternionicSymmetry.ComplexMatrixRealificationAlgebra
open ComplexMatrixRealification
noncomputable section
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [Fintype κ] [DecidableEq κ] in
theorem realify_add (A B : Matrix κ κ ℂ) : realify (A + B) = realify A + realify B := by
  ext ⟨i,a⟩ ⟨j,b⟩
  fin_cases a <;> fin_cases b <;> simp [realify, Complex.add_re, Complex.add_im, add_comm]

omit [Fintype κ] [DecidableEq κ] in
theorem realify_smul (r : ℝ) (A : Matrix κ κ ℂ) : realify (r • A) = r • realify A := by
  ext ⟨i,a⟩ ⟨j,b⟩
  fin_cases a <;> fin_cases b <;> simp [realify]

omit [DecidableEq κ] in
theorem realify_mul (A B : Matrix κ κ ℂ) : realify (A * B) = realify A * realify B := by
  ext ⟨i,a⟩ ⟨j,b⟩
  fin_cases a <;> fin_cases b <;>
    simp [realify, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Complex.mul_re, Complex.mul_im, Finset.sum_add_distrib,
      sub_eq_add_neg, add_comm]

omit [Fintype κ] in
theorem realify_one : realify (1 : Matrix κ κ ℂ) = 1 := by
  ext ⟨i,a⟩ ⟨j,b⟩
  fin_cases a <;> fin_cases b <;> simp [realify, Matrix.one_apply, apply_ite]

theorem realify_pow (A : Matrix κ κ ℂ) (k : ℕ) : realify (A ^ k) = realify A ^ k := by
  induction k with
  | zero => simpa using realify_one (κ := κ)
  | succ k ih => rw [pow_succ, realify_mul, ih, pow_succ]

omit [DecidableEq κ] in
theorem trace_realify (A : Matrix κ κ ℂ) : (realify A).trace = 2 * A.trace.re := by
  simp [Matrix.trace, realify, Fintype.sum_prod_type, Fin.sum_univ_two,
    ← Finset.sum_add_distrib, two_mul]

def realifyLinear : Matrix κ κ ℂ →ₗ[ℝ] Matrix (κ × Fin 2) (κ × Fin 2) ℝ where
  toFun := realify
  map_add' := realify_add
  map_smul' := realify_smul

local instance : NormedRing (Matrix κ κ ℂ) := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ (Matrix κ κ ℂ) := Matrix.linftyOpNormedAlgebra
local instance : NormedRing (Matrix (κ × Fin 2) (κ × Fin 2) ℝ) := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ (Matrix (κ × Fin 2) (κ × Fin 2) ℝ) :=
  Matrix.linftyOpNormedAlgebra

def realifyCLM : Matrix κ κ ℂ →L[ℝ] Matrix (κ × Fin 2) (κ × Fin 2) ℝ :=
  realifyLinear.toContinuousLinearMap

omit [DecidableEq κ] in
theorem realifyCLM_mul (A B : Matrix κ κ ℂ) :
    realifyCLM (A * B) = realifyCLM A * realifyCLM B := realify_mul A B

end
end QuaternionicSymmetry.ComplexMatrixRealificationAlgebra
