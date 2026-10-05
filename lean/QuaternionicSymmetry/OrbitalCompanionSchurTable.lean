import QuaternionicSymmetry.FiniteTypeCSchurSix
import QuaternionicSymmetry.OrbitalOddRemainderSchur
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Misc
import Mathlib.Tactic

/-! The bounded companion-remainder calculation for Schur weights at most six.
The elementary coefficients are independent rational inputs. Spectral
specialization of this finite table is proved separately. -/

namespace QuaternionicSymmetry.OrbitalCompanionSchurTable

open Matrix

noncomputable section

/-- Coefficient at row `n-d` of the remainder of `X^(n+s)`, expressed in
the elementary coefficients of the monic root polynomial. -/
def remainder (e : ℕ → ℚ) : ℕ → ℕ → ℚ
  | 0, d => (-1) ^ (d + 1) * e d
  | s + 1, d => remainder e s (d + 1) - remainder e s 1 * ((-1) ^ d * e d)

/-- Power sums recovered from independent elementary coefficients by Newton. -/
def newtonPower (e : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => (-1) ^ n * (n + 1) * e (n + 1) +
      ∑ i : Fin n, (-1) ^ i.val * e (i.val + 1) * newtonPower e (n - i.val)
termination_by k => k
decreasing_by omega

/-- The final six coefficient rows/columns for a decreasing partition,
padded by zeros. Unshifted columns retain their actual standard-basis form. -/
def tailMatrix (e : ℕ → ℚ) (lam : List ℕ) : Matrix (Fin 6) (Fin 6) ℚ :=
  fun i j =>
    let q := j.val + (lam[5 - j.val]?).getD 0
    if q < 6 then if i.val = q then 1 else 0
    else remainder e (q - 6) (6 - i.val)

def schurValue (e : ℕ → ℚ) (lam : List ℕ) : ℚ :=
  MvPolynomial.aeval (fun i : Fin 6 => newtonPower e (i.val + 1))
    (FiniteTypeCSchurSix.schur lam)


set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem table_empty (e : ℕ → ℚ) : (tailMatrix e []).det = schurValue e [] := by
  rw [OrbitalOddRemainderSchur.det_eq_tailBlock_of_leftIdentity 6 0 _ (by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [tailMatrix, Matrix.one_apply, Fin.ext_iff])]
  norm_num [tailMatrix, Matrix.det_fin_zero, Matrix.det_fin_one,
    Matrix.det_fin_two, Matrix.det_fin_three, Matrix.submatrix_apply,
    remainder, schurValue, FiniteTypeCSchurSix.schur,
    FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3,
    FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.e5, FiniteTypeCSchurSix.e6,
    FiniteTypeCSchurSix.h0, FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.h2,
    FiniteTypeCSchurSix.h3, FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5,
    FiniteTypeCSchurSix.h6, FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2,
    FiniteTypeCSchurSix.p3, FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5,
    FiniteTypeCSchurSix.p6]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem table_1 (e : ℕ → ℚ) : (tailMatrix e [1]).det = schurValue e [1] := by
  rw [OrbitalOddRemainderSchur.det_eq_tailBlock_of_leftIdentity 5 1 _ (by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [tailMatrix, Matrix.one_apply, Fin.ext_iff])]
  norm_num [tailMatrix, Matrix.det_fin_zero, Matrix.det_fin_one,
    Matrix.det_fin_two, Matrix.det_fin_three, Matrix.submatrix_apply,
    remainder, schurValue, FiniteTypeCSchurSix.schur,
    FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3,
    FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.e5, FiniteTypeCSchurSix.e6,
    FiniteTypeCSchurSix.h0, FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.h2,
    FiniteTypeCSchurSix.h3, FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5,
    FiniteTypeCSchurSix.h6, FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2,
    FiniteTypeCSchurSix.p3, FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5,
    FiniteTypeCSchurSix.p6]
  all_goals norm_num [newtonPower, Fin.sum_univ_succ, Fin.sum_univ_two,
    Fin.sum_univ_three, Fin.sum_univ_four, Fin.sum_univ_five, Fin.sum_univ_six]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem table_2 (e : ℕ → ℚ) : (tailMatrix e [2]).det = schurValue e [2] := by
  rw [OrbitalOddRemainderSchur.det_eq_tailBlock_of_leftIdentity 5 1 _ (by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [tailMatrix, Matrix.one_apply, Fin.ext_iff])]
  norm_num [tailMatrix, Matrix.det_fin_zero, Matrix.det_fin_one,
    Matrix.det_fin_two, Matrix.det_fin_three, Matrix.submatrix_apply,
    remainder, schurValue, FiniteTypeCSchurSix.schur,
    FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3,
    FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.e5, FiniteTypeCSchurSix.e6,
    FiniteTypeCSchurSix.h0, FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.h2,
    FiniteTypeCSchurSix.h3, FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5,
    FiniteTypeCSchurSix.h6, FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2,
    FiniteTypeCSchurSix.p3, FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5,
    FiniteTypeCSchurSix.p6]
  all_goals norm_num [newtonPower, Fin.sum_univ_succ, Fin.sum_univ_two,
    Fin.sum_univ_three, Fin.sum_univ_four, Fin.sum_univ_five, Fin.sum_univ_six]
  all_goals ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem table_1_1 (e : ℕ → ℚ) : (tailMatrix e [1, 1]).det = schurValue e [1, 1] := by
  rw [OrbitalOddRemainderSchur.det_eq_tailBlock_of_leftIdentity 4 2 _ (by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [tailMatrix, Matrix.one_apply, Fin.ext_iff])]
  norm_num [tailMatrix, Matrix.det_fin_zero, Matrix.det_fin_one,
    Matrix.det_fin_two, Matrix.det_fin_three, Matrix.submatrix_apply,
    remainder, schurValue, FiniteTypeCSchurSix.schur,
    FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3,
    FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.e5, FiniteTypeCSchurSix.e6,
    FiniteTypeCSchurSix.h0, FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.h2,
    FiniteTypeCSchurSix.h3, FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5,
    FiniteTypeCSchurSix.h6, FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2,
    FiniteTypeCSchurSix.p3, FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5,
    FiniteTypeCSchurSix.p6]
  all_goals norm_num [newtonPower, Fin.sum_univ_succ, Fin.sum_univ_two,
    Fin.sum_univ_three, Fin.sum_univ_four, Fin.sum_univ_five, Fin.sum_univ_six]
  all_goals ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem table_3 (e : ℕ → ℚ) : (tailMatrix e [3]).det = schurValue e [3] := by
  rw [OrbitalOddRemainderSchur.det_eq_tailBlock_of_leftIdentity 5 1 _ (by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [tailMatrix, Matrix.one_apply, Fin.ext_iff])]
  norm_num [tailMatrix, Matrix.det_fin_zero, Matrix.det_fin_one,
    Matrix.det_fin_two, Matrix.det_fin_three, Matrix.submatrix_apply,
    remainder, schurValue, FiniteTypeCSchurSix.schur,
    FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3,
    FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.e5, FiniteTypeCSchurSix.e6,
    FiniteTypeCSchurSix.h0, FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.h2,
    FiniteTypeCSchurSix.h3, FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5,
    FiniteTypeCSchurSix.h6, FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2,
    FiniteTypeCSchurSix.p3, FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5,
    FiniteTypeCSchurSix.p6]
  all_goals norm_num [newtonPower, Fin.sum_univ_succ, Fin.sum_univ_two,
    Fin.sum_univ_three, Fin.sum_univ_four, Fin.sum_univ_five, Fin.sum_univ_six]
  all_goals ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem table_2_1 (e : ℕ → ℚ) : (tailMatrix e [2, 1]).det = schurValue e [2, 1] := by
  rw [OrbitalOddRemainderSchur.det_eq_tailBlock_of_leftIdentity 4 2 _ (by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [tailMatrix, Matrix.one_apply, Fin.ext_iff])]
  norm_num [tailMatrix, Matrix.det_fin_zero, Matrix.det_fin_one,
    Matrix.det_fin_two, Matrix.det_fin_three, Matrix.submatrix_apply,
    remainder, schurValue, FiniteTypeCSchurSix.schur,
    FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3,
    FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.e5, FiniteTypeCSchurSix.e6,
    FiniteTypeCSchurSix.h0, FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.h2,
    FiniteTypeCSchurSix.h3, FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5,
    FiniteTypeCSchurSix.h6, FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2,
    FiniteTypeCSchurSix.p3, FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5,
    FiniteTypeCSchurSix.p6]
  all_goals norm_num [newtonPower, Fin.sum_univ_succ, Fin.sum_univ_two,
    Fin.sum_univ_three, Fin.sum_univ_four, Fin.sum_univ_five, Fin.sum_univ_six]
  all_goals ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem table_1_1_1 (e : ℕ → ℚ) : (tailMatrix e [1, 1, 1]).det = schurValue e [1, 1, 1] := by
  rw [OrbitalOddRemainderSchur.det_eq_tailBlock_of_leftIdentity 3 3 _ (by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [tailMatrix, Matrix.one_apply, Fin.ext_iff])]
  norm_num [tailMatrix, Matrix.det_fin_zero, Matrix.det_fin_one,
    Matrix.det_fin_two, Matrix.det_fin_three, Matrix.submatrix_apply,
    remainder, schurValue, FiniteTypeCSchurSix.schur,
    FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3,
    FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.e5, FiniteTypeCSchurSix.e6,
    FiniteTypeCSchurSix.h0, FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.h2,
    FiniteTypeCSchurSix.h3, FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5,
    FiniteTypeCSchurSix.h6, FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2,
    FiniteTypeCSchurSix.p3, FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5,
    FiniteTypeCSchurSix.p6]
  all_goals norm_num [newtonPower, Fin.sum_univ_succ, Fin.sum_univ_two,
    Fin.sum_univ_three, Fin.sum_univ_four, Fin.sum_univ_five, Fin.sum_univ_six]
  all_goals ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem table_4 (e : ℕ → ℚ) : (tailMatrix e [4]).det = schurValue e [4] := by
  rw [OrbitalOddRemainderSchur.det_eq_tailBlock_of_leftIdentity 5 1 _ (by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [tailMatrix, Matrix.one_apply, Fin.ext_iff])]
  norm_num [tailMatrix, Matrix.det_fin_zero, Matrix.det_fin_one,
    Matrix.det_fin_two, Matrix.det_fin_three, Matrix.submatrix_apply,
    remainder, schurValue, FiniteTypeCSchurSix.schur,
    FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3,
    FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.e5, FiniteTypeCSchurSix.e6,
    FiniteTypeCSchurSix.h0, FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.h2,
    FiniteTypeCSchurSix.h3, FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5,
    FiniteTypeCSchurSix.h6, FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2,
    FiniteTypeCSchurSix.p3, FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5,
    FiniteTypeCSchurSix.p6]
  all_goals norm_num [newtonPower, Fin.sum_univ_succ, Fin.sum_univ_two,
    Fin.sum_univ_three, Fin.sum_univ_four, Fin.sum_univ_five, Fin.sum_univ_six]
  all_goals ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem table_3_1 (e : ℕ → ℚ) : (tailMatrix e [3, 1]).det = schurValue e [3, 1] := by
  rw [OrbitalOddRemainderSchur.det_eq_tailBlock_of_leftIdentity 4 2 _ (by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [tailMatrix, Matrix.one_apply, Fin.ext_iff])]
  norm_num [tailMatrix, Matrix.det_fin_zero, Matrix.det_fin_one,
    Matrix.det_fin_two, Matrix.det_fin_three, Matrix.submatrix_apply,
    remainder, schurValue, FiniteTypeCSchurSix.schur,
    FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3,
    FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.e5, FiniteTypeCSchurSix.e6,
    FiniteTypeCSchurSix.h0, FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.h2,
    FiniteTypeCSchurSix.h3, FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5,
    FiniteTypeCSchurSix.h6, FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2,
    FiniteTypeCSchurSix.p3, FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5,
    FiniteTypeCSchurSix.p6]
  all_goals norm_num [newtonPower, Fin.sum_univ_succ, Fin.sum_univ_two,
    Fin.sum_univ_three, Fin.sum_univ_four, Fin.sum_univ_five, Fin.sum_univ_six]
  all_goals ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem table_2_2 (e : ℕ → ℚ) : (tailMatrix e [2, 2]).det = schurValue e [2, 2] := by
  rw [OrbitalOddRemainderSchur.det_eq_tailBlock_of_leftIdentity 4 2 _ (by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [tailMatrix, Matrix.one_apply, Fin.ext_iff])]
  norm_num [tailMatrix, Matrix.det_fin_zero, Matrix.det_fin_one,
    Matrix.det_fin_two, Matrix.det_fin_three, Matrix.submatrix_apply,
    remainder, schurValue, FiniteTypeCSchurSix.schur,
    FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3,
    FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.e5, FiniteTypeCSchurSix.e6,
    FiniteTypeCSchurSix.h0, FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.h2,
    FiniteTypeCSchurSix.h3, FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5,
    FiniteTypeCSchurSix.h6, FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2,
    FiniteTypeCSchurSix.p3, FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5,
    FiniteTypeCSchurSix.p6]
  all_goals norm_num [newtonPower, Fin.sum_univ_succ, Fin.sum_univ_two,
    Fin.sum_univ_three, Fin.sum_univ_four, Fin.sum_univ_five, Fin.sum_univ_six]
  all_goals ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem table_2_1_1 (e : ℕ → ℚ) : (tailMatrix e [2, 1, 1]).det = schurValue e [2, 1, 1] := by
  rw [OrbitalOddRemainderSchur.det_eq_tailBlock_of_leftIdentity 3 3 _ (by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [tailMatrix, Matrix.one_apply, Fin.ext_iff])]
  norm_num [tailMatrix, Matrix.det_fin_zero, Matrix.det_fin_one,
    Matrix.det_fin_two, Matrix.det_fin_three, Matrix.submatrix_apply,
    remainder, schurValue, FiniteTypeCSchurSix.schur,
    FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3,
    FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.e5, FiniteTypeCSchurSix.e6,
    FiniteTypeCSchurSix.h0, FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.h2,
    FiniteTypeCSchurSix.h3, FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5,
    FiniteTypeCSchurSix.h6, FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2,
    FiniteTypeCSchurSix.p3, FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5,
    FiniteTypeCSchurSix.p6]
  all_goals norm_num [newtonPower, Fin.sum_univ_succ, Fin.sum_univ_two,
    Fin.sum_univ_three, Fin.sum_univ_four, Fin.sum_univ_five, Fin.sum_univ_six]
  all_goals ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem table_5 (e : ℕ → ℚ) : (tailMatrix e [5]).det = schurValue e [5] := by
  rw [OrbitalOddRemainderSchur.det_eq_tailBlock_of_leftIdentity 5 1 _ (by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [tailMatrix, Matrix.one_apply, Fin.ext_iff])]
  norm_num [tailMatrix, Matrix.det_fin_zero, Matrix.det_fin_one,
    Matrix.det_fin_two, Matrix.det_fin_three, Matrix.submatrix_apply,
    remainder, schurValue, FiniteTypeCSchurSix.schur,
    FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3,
    FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.e5, FiniteTypeCSchurSix.e6,
    FiniteTypeCSchurSix.h0, FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.h2,
    FiniteTypeCSchurSix.h3, FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5,
    FiniteTypeCSchurSix.h6, FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2,
    FiniteTypeCSchurSix.p3, FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5,
    FiniteTypeCSchurSix.p6]
  all_goals norm_num [newtonPower, Fin.sum_univ_succ, Fin.sum_univ_two,
    Fin.sum_univ_three, Fin.sum_univ_four, Fin.sum_univ_five, Fin.sum_univ_six]
  all_goals ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem table_4_1 (e : ℕ → ℚ) : (tailMatrix e [4, 1]).det = schurValue e [4, 1] := by
  rw [OrbitalOddRemainderSchur.det_eq_tailBlock_of_leftIdentity 4 2 _ (by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [tailMatrix, Matrix.one_apply, Fin.ext_iff])]
  norm_num [tailMatrix, Matrix.det_fin_zero, Matrix.det_fin_one,
    Matrix.det_fin_two, Matrix.det_fin_three, Matrix.submatrix_apply,
    remainder, schurValue, FiniteTypeCSchurSix.schur,
    FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3,
    FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.e5, FiniteTypeCSchurSix.e6,
    FiniteTypeCSchurSix.h0, FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.h2,
    FiniteTypeCSchurSix.h3, FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5,
    FiniteTypeCSchurSix.h6, FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2,
    FiniteTypeCSchurSix.p3, FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5,
    FiniteTypeCSchurSix.p6]
  all_goals norm_num [newtonPower, Fin.sum_univ_succ, Fin.sum_univ_two,
    Fin.sum_univ_three, Fin.sum_univ_four, Fin.sum_univ_five, Fin.sum_univ_six]
  all_goals ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem table_3_2 (e : ℕ → ℚ) : (tailMatrix e [3, 2]).det = schurValue e [3, 2] := by
  rw [OrbitalOddRemainderSchur.det_eq_tailBlock_of_leftIdentity 4 2 _ (by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [tailMatrix, Matrix.one_apply, Fin.ext_iff])]
  norm_num [tailMatrix, Matrix.det_fin_zero, Matrix.det_fin_one,
    Matrix.det_fin_two, Matrix.det_fin_three, Matrix.submatrix_apply,
    remainder, schurValue, FiniteTypeCSchurSix.schur,
    FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3,
    FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.e5, FiniteTypeCSchurSix.e6,
    FiniteTypeCSchurSix.h0, FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.h2,
    FiniteTypeCSchurSix.h3, FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5,
    FiniteTypeCSchurSix.h6, FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2,
    FiniteTypeCSchurSix.p3, FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5,
    FiniteTypeCSchurSix.p6]
  all_goals norm_num [newtonPower, Fin.sum_univ_succ, Fin.sum_univ_two,
    Fin.sum_univ_three, Fin.sum_univ_four, Fin.sum_univ_five, Fin.sum_univ_six]
  all_goals ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem table_3_1_1 (e : ℕ → ℚ) : (tailMatrix e [3, 1, 1]).det = schurValue e [3, 1, 1] := by
  rw [OrbitalOddRemainderSchur.det_eq_tailBlock_of_leftIdentity 3 3 _ (by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [tailMatrix, Matrix.one_apply, Fin.ext_iff])]
  norm_num [tailMatrix, Matrix.det_fin_zero, Matrix.det_fin_one,
    Matrix.det_fin_two, Matrix.det_fin_three, Matrix.submatrix_apply,
    remainder, schurValue, FiniteTypeCSchurSix.schur,
    FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3,
    FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.e5, FiniteTypeCSchurSix.e6,
    FiniteTypeCSchurSix.h0, FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.h2,
    FiniteTypeCSchurSix.h3, FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5,
    FiniteTypeCSchurSix.h6, FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2,
    FiniteTypeCSchurSix.p3, FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5,
    FiniteTypeCSchurSix.p6]
  all_goals norm_num [newtonPower, Fin.sum_univ_succ, Fin.sum_univ_two,
    Fin.sum_univ_three, Fin.sum_univ_four, Fin.sum_univ_five, Fin.sum_univ_six]
  all_goals ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem table_2_2_1 (e : ℕ → ℚ) : (tailMatrix e [2, 2, 1]).det = schurValue e [2, 2, 1] := by
  rw [OrbitalOddRemainderSchur.det_eq_tailBlock_of_leftIdentity 3 3 _ (by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [tailMatrix, Matrix.one_apply, Fin.ext_iff])]
  norm_num [tailMatrix, Matrix.det_fin_zero, Matrix.det_fin_one,
    Matrix.det_fin_two, Matrix.det_fin_three, Matrix.submatrix_apply,
    remainder, schurValue, FiniteTypeCSchurSix.schur,
    FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3,
    FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.e5, FiniteTypeCSchurSix.e6,
    FiniteTypeCSchurSix.h0, FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.h2,
    FiniteTypeCSchurSix.h3, FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5,
    FiniteTypeCSchurSix.h6, FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2,
    FiniteTypeCSchurSix.p3, FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5,
    FiniteTypeCSchurSix.p6]
  all_goals norm_num [newtonPower, Fin.sum_univ_succ, Fin.sum_univ_two,
    Fin.sum_univ_three, Fin.sum_univ_four, Fin.sum_univ_five, Fin.sum_univ_six]
  all_goals ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem table_6 (e : ℕ → ℚ) : (tailMatrix e [6]).det = schurValue e [6] := by
  rw [OrbitalOddRemainderSchur.det_eq_tailBlock_of_leftIdentity 5 1 _ (by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [tailMatrix, Matrix.one_apply, Fin.ext_iff])]
  norm_num [tailMatrix, Matrix.det_fin_zero, Matrix.det_fin_one,
    Matrix.det_fin_two, Matrix.det_fin_three, Matrix.submatrix_apply,
    remainder, schurValue, FiniteTypeCSchurSix.schur,
    FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3,
    FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.e5, FiniteTypeCSchurSix.e6,
    FiniteTypeCSchurSix.h0, FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.h2,
    FiniteTypeCSchurSix.h3, FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5,
    FiniteTypeCSchurSix.h6, FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2,
    FiniteTypeCSchurSix.p3, FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5,
    FiniteTypeCSchurSix.p6]
  all_goals norm_num [newtonPower, Fin.sum_univ_succ, Fin.sum_univ_two,
    Fin.sum_univ_three, Fin.sum_univ_four, Fin.sum_univ_five, Fin.sum_univ_six]
  all_goals ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem table_5_1 (e : ℕ → ℚ) : (tailMatrix e [5, 1]).det = schurValue e [5, 1] := by
  rw [OrbitalOddRemainderSchur.det_eq_tailBlock_of_leftIdentity 4 2 _ (by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [tailMatrix, Matrix.one_apply, Fin.ext_iff])]
  norm_num [tailMatrix, Matrix.det_fin_zero, Matrix.det_fin_one,
    Matrix.det_fin_two, Matrix.det_fin_three, Matrix.submatrix_apply,
    remainder, schurValue, FiniteTypeCSchurSix.schur,
    FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3,
    FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.e5, FiniteTypeCSchurSix.e6,
    FiniteTypeCSchurSix.h0, FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.h2,
    FiniteTypeCSchurSix.h3, FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5,
    FiniteTypeCSchurSix.h6, FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2,
    FiniteTypeCSchurSix.p3, FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5,
    FiniteTypeCSchurSix.p6]
  all_goals norm_num [newtonPower, Fin.sum_univ_succ, Fin.sum_univ_two,
    Fin.sum_univ_three, Fin.sum_univ_four, Fin.sum_univ_five, Fin.sum_univ_six]
  all_goals ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem table_4_2 (e : ℕ → ℚ) : (tailMatrix e [4, 2]).det = schurValue e [4, 2] := by
  rw [OrbitalOddRemainderSchur.det_eq_tailBlock_of_leftIdentity 4 2 _ (by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [tailMatrix, Matrix.one_apply, Fin.ext_iff])]
  norm_num [tailMatrix, Matrix.det_fin_zero, Matrix.det_fin_one,
    Matrix.det_fin_two, Matrix.det_fin_three, Matrix.submatrix_apply,
    remainder, schurValue, FiniteTypeCSchurSix.schur,
    FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3,
    FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.e5, FiniteTypeCSchurSix.e6,
    FiniteTypeCSchurSix.h0, FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.h2,
    FiniteTypeCSchurSix.h3, FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5,
    FiniteTypeCSchurSix.h6, FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2,
    FiniteTypeCSchurSix.p3, FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5,
    FiniteTypeCSchurSix.p6]
  all_goals norm_num [newtonPower, Fin.sum_univ_succ, Fin.sum_univ_two,
    Fin.sum_univ_three, Fin.sum_univ_four, Fin.sum_univ_five, Fin.sum_univ_six]
  all_goals ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem table_4_1_1 (e : ℕ → ℚ) : (tailMatrix e [4, 1, 1]).det = schurValue e [4, 1, 1] := by
  rw [OrbitalOddRemainderSchur.det_eq_tailBlock_of_leftIdentity 3 3 _ (by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [tailMatrix, Matrix.one_apply, Fin.ext_iff])]
  norm_num [tailMatrix, Matrix.det_fin_zero, Matrix.det_fin_one,
    Matrix.det_fin_two, Matrix.det_fin_three, Matrix.submatrix_apply,
    remainder, schurValue, FiniteTypeCSchurSix.schur,
    FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3,
    FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.e5, FiniteTypeCSchurSix.e6,
    FiniteTypeCSchurSix.h0, FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.h2,
    FiniteTypeCSchurSix.h3, FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5,
    FiniteTypeCSchurSix.h6, FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2,
    FiniteTypeCSchurSix.p3, FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5,
    FiniteTypeCSchurSix.p6]
  all_goals norm_num [newtonPower, Fin.sum_univ_succ, Fin.sum_univ_two,
    Fin.sum_univ_three, Fin.sum_univ_four, Fin.sum_univ_five, Fin.sum_univ_six]
  all_goals ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem table_3_3 (e : ℕ → ℚ) : (tailMatrix e [3, 3]).det = schurValue e [3, 3] := by
  rw [OrbitalOddRemainderSchur.det_eq_tailBlock_of_leftIdentity 4 2 _ (by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [tailMatrix, Matrix.one_apply, Fin.ext_iff])]
  norm_num [tailMatrix, Matrix.det_fin_zero, Matrix.det_fin_one,
    Matrix.det_fin_two, Matrix.det_fin_three, Matrix.submatrix_apply,
    remainder, schurValue, FiniteTypeCSchurSix.schur,
    FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3,
    FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.e5, FiniteTypeCSchurSix.e6,
    FiniteTypeCSchurSix.h0, FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.h2,
    FiniteTypeCSchurSix.h3, FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5,
    FiniteTypeCSchurSix.h6, FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2,
    FiniteTypeCSchurSix.p3, FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5,
    FiniteTypeCSchurSix.p6]
  all_goals norm_num [newtonPower, Fin.sum_univ_succ, Fin.sum_univ_two,
    Fin.sum_univ_three, Fin.sum_univ_four, Fin.sum_univ_five, Fin.sum_univ_six]
  all_goals ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem table_3_2_1 (e : ℕ → ℚ) : (tailMatrix e [3, 2, 1]).det = schurValue e [3, 2, 1] := by
  rw [OrbitalOddRemainderSchur.det_eq_tailBlock_of_leftIdentity 3 3 _ (by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [tailMatrix, Matrix.one_apply, Fin.ext_iff])]
  norm_num [tailMatrix, Matrix.det_fin_zero, Matrix.det_fin_one,
    Matrix.det_fin_two, Matrix.det_fin_three, Matrix.submatrix_apply,
    remainder, schurValue, FiniteTypeCSchurSix.schur,
    FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3,
    FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.e5, FiniteTypeCSchurSix.e6,
    FiniteTypeCSchurSix.h0, FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.h2,
    FiniteTypeCSchurSix.h3, FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5,
    FiniteTypeCSchurSix.h6, FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2,
    FiniteTypeCSchurSix.p3, FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5,
    FiniteTypeCSchurSix.p6]
  all_goals norm_num [newtonPower, Fin.sum_univ_succ, Fin.sum_univ_two,
    Fin.sum_univ_three, Fin.sum_univ_four, Fin.sum_univ_five, Fin.sum_univ_six]
  all_goals ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem table_2_2_2 (e : ℕ → ℚ) : (tailMatrix e [2, 2, 2]).det = schurValue e [2, 2, 2] := by
  rw [OrbitalOddRemainderSchur.det_eq_tailBlock_of_leftIdentity 3 3 _ (by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [tailMatrix, Matrix.one_apply, Fin.ext_iff])]
  norm_num [tailMatrix, Matrix.det_fin_zero, Matrix.det_fin_one,
    Matrix.det_fin_two, Matrix.det_fin_three, Matrix.submatrix_apply,
    remainder, schurValue, FiniteTypeCSchurSix.schur,
    FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2, FiniteTypeCSchurSix.e3,
    FiniteTypeCSchurSix.e4, FiniteTypeCSchurSix.e5, FiniteTypeCSchurSix.e6,
    FiniteTypeCSchurSix.h0, FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.h2,
    FiniteTypeCSchurSix.h3, FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5,
    FiniteTypeCSchurSix.h6, FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2,
    FiniteTypeCSchurSix.p3, FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5,
    FiniteTypeCSchurSix.p6]
  all_goals norm_num [newtonPower, Fin.sum_univ_succ, Fin.sum_univ_two,
    Fin.sum_univ_three, Fin.sum_univ_four, Fin.sum_univ_five, Fin.sum_univ_six]
  all_goals ring

end
end QuaternionicSymmetry.OrbitalCompanionSchurTable
