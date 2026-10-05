import Mathlib.LinearAlgebra.Matrix.Trace

/-! Universal quaternionic-line and rank-three adjoint trace identities over
an arbitrary commutative ring. This is the coefficient algebra needed for
even exterior curvature forms. -/
namespace QuaternionicSymmetry.QuaternionicUniversalEvenTrace
noncomputable section
variable {R : Type*} [CommRing R]

def normSquare (a : Fin 3 → R) : R :=
  a 0 * a 0 + a 1 * a 1 + a 2 * a 2

/-- Right multiplication by the negative imaginary quaternion in the basis
`1,i,j,k`. -/
def lineMatrix (a : Fin 3 → R) : Matrix (Fin 4) (Fin 4) R :=
  !![0, a 0, a 1, a 2;
     -a 0, 0, -a 2, a 1;
     -a 1, a 2, 0, -a 0;
     -a 2, -a 1, a 0, 0]

/-- Twice the cross-product action of the imaginary quaternion. -/
def adjointMatrix (a : Fin 3 → R) : Matrix (Fin 3) (Fin 3) R :=
  !![0, -2 * a 2, 2 * a 1;
     2 * a 2, 0, -2 * a 0;
     -2 * a 1, 2 * a 0, 0]

private theorem lineMatrix_square (a : Fin 3 → R) :
    lineMatrix a ^ 2 = (-normSquare a) • (1 : Matrix (Fin 4) (Fin 4) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lineMatrix, normSquare, pow_two, Matrix.mul_apply,
      Matrix.smul_apply, Fin.sum_univ_four] <;>
    ring

private theorem adjointMatrix_cube (a : Fin 3 → R) :
    adjointMatrix a ^ 3 = (-(4 * normSquare a)) • adjointMatrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adjointMatrix, normSquare, pow_succ, Matrix.mul_apply,
      Matrix.smul_apply, Fin.sum_univ_three] <;>
    ring

private theorem trace_lineMatrix (a : Fin 3 → R) :
    Matrix.trace (lineMatrix a) = 0 := by
  simp [lineMatrix, Matrix.trace, Fin.sum_univ_four]

private theorem trace_adjointMatrix_square (a : Fin 3 → R) :
    Matrix.trace (adjointMatrix a ^ 2) = -(8 * normSquare a) := by
  simp [adjointMatrix, normSquare, pow_two,
    Matrix.trace, Fin.sum_univ_three]
  ring

theorem lineMatrix_even_trace (a : Fin 3 → R) (j : ℕ) :
    Matrix.trace (lineMatrix a ^ (2 * j)) = 4 * (-normSquare a) ^ j := by
  rw [pow_mul, lineMatrix_square, smul_pow]
  simp [Matrix.trace]

theorem adjointMatrix_even_trace (a : Fin 3 → R) (j : ℕ) (hj : 0 < j) :
    Matrix.trace (adjointMatrix a ^ (2 * j)) =
      2 * (-(4 * normSquare a)) ^ j := by
  let C := adjointMatrix a
  have hcubic : C ^ 3 = (-(4 * normSquare a)) • C :=
    adjointMatrix_cube a
  have hbase : Matrix.trace (C ^ 2) =
      2 * (-(4 * normSquare a)) := by
    rw [trace_adjointMatrix_square]
    ring
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  induction m with
  | zero => simpa using hbase
  | succ m ih =>
      have hpow : C ^ (2 * (m + 1 + 1)) =
          (-(4 * normSquare a)) • C ^ (2 * (m + 1)) := by
        calc
          C ^ (2 * (m + 1 + 1)) = C ^ (2 * m + 1) * C ^ 3 := by
            rw [← pow_add]
            congr 1
          _ = C ^ (2 * m + 1) * ((-(4 * normSquare a)) • C) := by
            rw [hcubic]
          _ = (-(4 * normSquare a)) • C ^ (2 * (m + 1)) := by
            rw [mul_smul_comm, ← pow_succ]
            congr 1
      rw [hpow, Matrix.trace_smul, ih (by omega)]
      simp only [smul_eq_mul]
      conv_rhs => rw [pow_succ]
      conv_lhs => rw [pow_succ]
      ring_nf

theorem line_adjoint_even_trace (a : Fin 3 → R)
    (j : ℕ) (hj : 0 < j) :
    (4 : R) ^ j * Matrix.trace (lineMatrix a ^ (2 * j)) =
      2 * Matrix.trace (adjointMatrix a ^ (2 * j)) := by
  rw [lineMatrix_even_trace, adjointMatrix_even_trace a j hj]
  rw [show -(4 * normSquare a) = 4 * (-normSquare a) by ring, mul_pow]
  ring

end
end QuaternionicSymmetry.QuaternionicUniversalEvenTrace
