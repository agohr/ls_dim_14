import QuaternionicSymmetry.OrbitalCompanionSchurTable

/-!
The seven Schur remainder identities with partitions of length at least four.
The six hook shapes have a single nonzero entry in the first row after the
leading identity block is removed; the remaining minor is an identity matrix.
-/

namespace QuaternionicSymmetry.OrbitalCompanionSchurLongShapes

open Matrix QuaternionicSymmetry.OrbitalCompanionSchurTable

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

macro "finish_schur" : tactic =>
  `(tactic| (
    norm_num [schurValue, FiniteTypeCSchurSix.schur,
      FiniteTypeCSchurSix.e1, FiniteTypeCSchurSix.e2,
      FiniteTypeCSchurSix.e3, FiniteTypeCSchurSix.e4,
      FiniteTypeCSchurSix.e5, FiniteTypeCSchurSix.e6,
      FiniteTypeCSchurSix.h0, FiniteTypeCSchurSix.h1,
      FiniteTypeCSchurSix.h2, FiniteTypeCSchurSix.h3,
      FiniteTypeCSchurSix.h4, FiniteTypeCSchurSix.h5,
      FiniteTypeCSchurSix.h6, FiniteTypeCSchurSix.p1,
      FiniteTypeCSchurSix.p2, FiniteTypeCSchurSix.p3,
      FiniteTypeCSchurSix.p4, FiniteTypeCSchurSix.p5,
      FiniteTypeCSchurSix.p6]
    all_goals norm_num [newtonPower, Fin.sum_univ_succ,
      Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_four,
      Fin.sum_univ_five, Fin.sum_univ_six]
    all_goals ring))

theorem table_1_1_1_1 (e : ℕ → ℚ) :
    (tailMatrix e [1, 1, 1, 1]).det = schurValue e [1, 1, 1, 1] := by
  rw [OrbitalOddRemainderSchur.det_eq_tailBlock_of_leftIdentity 2 4 _ (by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [tailMatrix, Matrix.one_apply, Fin.ext_iff])]
  let A := (tailMatrix e [1, 1, 1, 1]).submatrix
    (Fin.natAdd 2 : Fin 4 → Fin 6) (Fin.natAdd 2 : Fin 4 → Fin 6)
  have hminor : A.submatrix Fin.succ (3 : Fin 4).succAbove =
      (1 : Matrix (Fin 3) (Fin 3) ℚ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  norm_num [A, tailMatrix, Matrix.submatrix_apply, hminor, remainder]
  finish_schur

theorem table_2_1_1_1 (e : ℕ → ℚ) :
    (tailMatrix e [2, 1, 1, 1]).det = schurValue e [2, 1, 1, 1] := by
  rw [OrbitalOddRemainderSchur.det_eq_tailBlock_of_leftIdentity 2 4 _ (by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [tailMatrix, Matrix.one_apply, Fin.ext_iff])]
  let A := (tailMatrix e [2, 1, 1, 1]).submatrix
    (Fin.natAdd 2 : Fin 4 → Fin 6) (Fin.natAdd 2 : Fin 4 → Fin 6)
  have hminor : A.submatrix Fin.succ (3 : Fin 4).succAbove =
      (1 : Matrix (Fin 3) (Fin 3) ℚ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  norm_num [A, tailMatrix, Matrix.submatrix_apply, hminor, remainder]
  finish_schur

theorem table_1_1_1_1_1 (e : ℕ → ℚ) :
    (tailMatrix e [1, 1, 1, 1, 1]).det =
      schurValue e [1, 1, 1, 1, 1] := by
  rw [OrbitalOddRemainderSchur.det_eq_tailBlock_of_leftIdentity 1 5 _ (by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [tailMatrix, Matrix.one_apply, Fin.ext_iff])]
  let A := (tailMatrix e [1, 1, 1, 1, 1]).submatrix
    (Fin.natAdd 1 : Fin 5 → Fin 6) (Fin.natAdd 1 : Fin 5 → Fin 6)
  have hminor : A.submatrix Fin.succ (4 : Fin 5).succAbove =
      (1 : Matrix (Fin 4) (Fin 4) ℚ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_five]
  norm_num [A, tailMatrix, Matrix.submatrix_apply, hminor, remainder]
  finish_schur

theorem table_3_1_1_1 (e : ℕ → ℚ) :
    (tailMatrix e [3, 1, 1, 1]).det = schurValue e [3, 1, 1, 1] := by
  rw [OrbitalOddRemainderSchur.det_eq_tailBlock_of_leftIdentity 2 4 _ (by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [tailMatrix, Matrix.one_apply, Fin.ext_iff])]
  let A := (tailMatrix e [3, 1, 1, 1]).submatrix
    (Fin.natAdd 2 : Fin 4 → Fin 6) (Fin.natAdd 2 : Fin 4 → Fin 6)
  have hminor : A.submatrix Fin.succ (3 : Fin 4).succAbove =
      (1 : Matrix (Fin 3) (Fin 3) ℚ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  norm_num [A, tailMatrix, Matrix.submatrix_apply, hminor, remainder]
  finish_schur

theorem table_2_2_1_1 (e : ℕ → ℚ) :
    (tailMatrix e [2, 2, 1, 1]).det = schurValue e [2, 2, 1, 1] := by
  rw [OrbitalOddRemainderSchur.det_eq_tailBlock_of_leftIdentity 2 4 _ (by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [tailMatrix, Matrix.one_apply, Fin.ext_iff])]
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  norm_num [tailMatrix, Matrix.det_fin_three, Matrix.submatrix_apply,
    Fin.natAdd, Fin.succAbove, Fin.ext_iff, Fin.lt_def, remainder]
  finish_schur

theorem table_2_1_1_1_1 (e : ℕ → ℚ) :
    (tailMatrix e [2, 1, 1, 1, 1]).det =
      schurValue e [2, 1, 1, 1, 1] := by
  rw [OrbitalOddRemainderSchur.det_eq_tailBlock_of_leftIdentity 1 5 _ (by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [tailMatrix, Matrix.one_apply, Fin.ext_iff])]
  let A := (tailMatrix e [2, 1, 1, 1, 1]).submatrix
    (Fin.natAdd 1 : Fin 5 → Fin 6) (Fin.natAdd 1 : Fin 5 → Fin 6)
  have hminor : A.submatrix Fin.succ (4 : Fin 5).succAbove =
      (1 : Matrix (Fin 4) (Fin 4) ℚ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_five]
  norm_num [A, tailMatrix, Matrix.submatrix_apply, hminor, remainder]
  finish_schur

theorem table_1_1_1_1_1_1 (e : ℕ → ℚ) :
    (tailMatrix e [1, 1, 1, 1, 1, 1]).det =
      schurValue e [1, 1, 1, 1, 1, 1] := by
  let A := tailMatrix e [1, 1, 1, 1, 1, 1]
  have hminor : A.submatrix Fin.succ (5 : Fin 6).succAbove =
      (1 : Matrix (Fin 5) (Fin 5) ℚ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_six]
  norm_num [A, tailMatrix, Matrix.submatrix_apply, hminor, remainder]
  finish_schur


/-- The finite Schur determinant table, including every listed partition through degree six. -/
theorem tailMatrix_det_eq_schurValue (e : ℕ → ℚ) (k : ℕ) (hk : k ≤ 6)
    (lam : List ℕ) (hmem : lam ∈ FiniteTypeCSchurSix.partitions k) :
    (tailMatrix e lam).det = schurValue e lam := by
  interval_cases k
  · simp only [FiniteTypeCSchurSix.partitions, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl
    · exact table_empty e
  · simp only [FiniteTypeCSchurSix.partitions, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl
    · exact table_1 e
  · simp only [FiniteTypeCSchurSix.partitions, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · exact table_2 e
    · exact table_1_1 e
  · simp only [FiniteTypeCSchurSix.partitions, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact table_3 e
    · exact table_2_1 e
    · exact table_1_1_1 e
  · simp only [FiniteTypeCSchurSix.partitions, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl
    · exact table_4 e
    · exact table_3_1 e
    · exact table_2_2 e
    · exact table_2_1_1 e
    · exact table_1_1_1_1 e
  · simp only [FiniteTypeCSchurSix.partitions, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact table_5 e
    · exact table_4_1 e
    · exact table_3_2 e
    · exact table_3_1_1 e
    · exact table_2_2_1 e
    · exact table_2_1_1_1 e
    · exact table_1_1_1_1_1 e
  · simp only [FiniteTypeCSchurSix.partitions, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact table_6 e
    · exact table_5_1 e
    · exact table_4_2 e
    · exact table_4_1_1 e
    · exact table_3_3 e
    · exact table_3_2_1 e
    · exact table_3_1_1_1 e
    · exact table_2_2_2 e
    · exact table_2_2_1_1 e
    · exact table_2_1_1_1_1 e
    · exact table_1_1_1_1_1_1 e

end
end QuaternionicSymmetry.OrbitalCompanionSchurLongShapes
