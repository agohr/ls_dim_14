import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-! A 4×4 transition fixing the first row has determinant equal to the
determinant of its 3×3 lower-right block. -/
namespace QuaternionicSymmetry.FourDimensionalBlockDeterminant

theorem det_eq_lower_right (A : Matrix (Fin 4) (Fin 4) ℝ)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (h00 : A 0 0 = 1)
    (h0 : ∀ j : Fin 3, A 0 (Fin.succ j) = 0)
    (hR : ∀ i j : Fin 3, A (Fin.succ i) (Fin.succ j) = R i j) :
    A.det = R.det := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ]
  have hsub : A.submatrix Fin.succ Fin.succ = R := by
    ext i j
    exact hR i j
  have h01 : A 0 1 = 0 := by simpa using h0 0
  have h02 : A 0 2 = 0 := by simpa using h0 1
  have h03 : A 0 3 = 0 := by simpa using h0 2
  simp [h00, h01, h02, h03, hsub]

end QuaternionicSymmetry.FourDimensionalBlockDeterminant
