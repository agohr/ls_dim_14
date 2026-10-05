import QuaternionicSymmetry.GaussianCompactInterchange
import QuaternionicSymmetry.MatrixMoments
import QuaternionicSymmetry.CovariancePolynomial
import Mathlib.LinearAlgebra.Matrix.Trace

/-! A fixed trace-represented Gram decomposition for a numerical positive
semidefinite matrix. The representing Hermitian matrices depend on the PSD
matrix, but not on the variable Hermitian contraction. -/

namespace QuaternionicSymmetry.FixedTraceGram

open Matrix
open scoped ComplexOrder BigOperators MatrixOrder

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- A row matrix whose trace pairing extracts an entry of `C * X`. -/
def entryTraceMatrix (C : Matrix κ κ ℂ) (i j : κ) : Matrix κ κ ℂ :=
  ∑ k, Matrix.single j k (C i k)

theorem trace_entryTraceMatrix (C X : Matrix κ κ ℂ) (i j : κ) :
    Matrix.trace (entryTraceMatrix C i j * X) = (C * X) i j := by
  simp [entryTraceMatrix, Matrix.sum_mul, Matrix.trace_sum,
    Matrix.trace_single_mul, Matrix.mul_apply]

/-- Hermitian part of a complex matrix. -/
def hermitianPart (T : Matrix κ κ ℂ) : Matrix κ κ ℂ :=
  (1 / 2 : ℂ) • (T + Tᴴ)

omit [Fintype κ] [DecidableEq κ] in
theorem hermitianPart_isHermitian (T : Matrix κ κ ℂ) :
    (hermitianPart T).IsHermitian := by
  change (hermitianPart T)ᴴ = hermitianPart T
  simp [hermitianPart, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_add, add_comm]

omit [DecidableEq κ] in
theorem trace_hermitianPart_re (T X : Matrix κ κ ℂ) (hX : X.IsHermitian) :
    (Matrix.trace (hermitianPart T * X)).re =
      (Matrix.trace (T * X)).re := by
  have hconj : Matrix.trace (Tᴴ * X) = star (Matrix.trace (T * X)) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hX.eq,
      Matrix.trace_mul_comm]
  simp only [hermitianPart, Matrix.smul_mul, add_mul, Matrix.trace_smul,
    Matrix.trace_add, smul_eq_mul]
  rw [hconj]
  simp
  ring

/-- Fixed Hermitian matrices representing the real and imaginary components
of each entry of `C * X` under the trace pairing. -/
def entryHermitian (C : Matrix κ κ ℂ) (q : κ × κ × Fin 2) : Matrix κ κ ℂ :=
  hermitianPart
    (if q.2.2 = 0 then entryTraceMatrix C q.1 q.2.1
      else (-Complex.I) • entryTraceMatrix C q.1 q.2.1)

theorem entryHermitian_isHermitian (C : Matrix κ κ ℂ) (q : κ × κ × Fin 2) :
    (entryHermitian C q).IsHermitian := hermitianPart_isHermitian _

theorem trace_entryHermitian_zero (C X : Matrix κ κ ℂ) (hX : X.IsHermitian)
    (i j : κ) :
    (Matrix.trace (entryHermitian C (i,j,0) * X)).re = ((C * X) i j).re := by
  simp only [entryHermitian, ↓reduceIte]
  rw [trace_hermitianPart_re _ X hX, trace_entryTraceMatrix]

theorem trace_entryHermitian_one (C X : Matrix κ κ ℂ) (hX : X.IsHermitian)
    (i j : κ) :
    (Matrix.trace (entryHermitian C (i,j,1) * X)).re = ((C * X) i j).im := by
  simp only [entryHermitian, show (1 : Fin 2) ≠ 0 by decide, if_false]
  rw [trace_hermitianPart_re _ X hX, Matrix.smul_mul, Matrix.trace_smul]
  simp only [smul_eq_mul, trace_entryTraceMatrix]
  simp

theorem trace_weighted_square_eq_entries (C X : Matrix κ κ ℂ)
    (hX : X.IsHermitian) :
    (Matrix.trace (Cᴴ * C * X ^ 2)).re =
      ∑ i, ∑ j, Complex.normSq ((C * X) i j) := by
  have hcyc : Matrix.trace (Cᴴ * C * X ^ 2) =
      Matrix.trace ((C * X)ᴴ * (C * X)) := by
    simp only [Matrix.conjTranspose_mul, hX.eq, pow_two]
    calc
      Matrix.trace (Cᴴ * C * (X * X)) =
          Matrix.trace (Cᴴ * ((C * X) * X)) := by simp only [mul_assoc]
      _ = Matrix.trace (X * (Cᴴ * (C * X))) := Matrix.trace_mul_cycle' _ _ _
      _ = Matrix.trace (X * Cᴴ * (C * X)) := by rw [mul_assoc]
  rw [hcyc]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    Complex.ofReal_re]

/-- A single fixed family of Hermitian trace probes gives the Gram square
decomposition for every Hermitian `X`. -/
theorem trace_weighted_square_fixed (C X : Matrix κ κ ℂ)
    (hX : X.IsHermitian) :
    (Matrix.trace (Cᴴ * C * X ^ 2)).re =
      ∑ q : κ × κ × Fin 2,
        (Matrix.trace (entryHermitian C q * X)).re ^ 2 := by
  rw [trace_weighted_square_eq_entries C X hX]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp_rw [trace_entryHermitian_zero C X hX,
    trace_entryHermitian_one C X hX, Complex.normSq_apply]
  simp only [pow_two]

/-- A positive semidefinite numerical matrix has a fixed finite Hermitian
trace-probe family. The family is independent of the Hermitian matrix `X` and
works simultaneously for every `X`. -/
theorem psd_fixed_trace_gram (A : Matrix κ κ ℂ) (hA : A.PosSemidef) :
    ∃ B : κ × κ × Fin 2 → Matrix κ κ ℂ,
      (∀ q, (B q).IsHermitian) ∧
      ∀ X : Matrix κ κ ℂ, X.IsHermitian →
        (Matrix.trace (A * X ^ 2)).re =
          ∑ q, (Matrix.trace (B q * X)).re ^ 2 := by
  obtain ⟨C, hC⟩ : ∃ C : Matrix κ κ ℂ, A = star C * C :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  simp only [Matrix.star_eq_conjTranspose] at hC
  refine ⟨entryHermitian C, entryHermitian_isHermitian C, ?_⟩
  intro X hX
  rw [hC]
  exact trace_weighted_square_fixed C X hX

theorem covarianceEntry_fixed_gram (C X Y : Matrix κ κ ℂ)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    MatrixMoments.covarianceEntry (Cᴴ * C) (fun b : Fin 2 =>
      if b = 0 then X else Y) 0 1 =
        ∑ q : κ × κ × Fin 2,
          (Matrix.trace (entryHermitian C q * X)).re *
            (Matrix.trace (entryHermitian C q * Y)).re := by
  have hXY : (X + Y).IsHermitian := hX.add hY
  have hsum := trace_weighted_square_fixed C (X + Y) hXY
  have hx := trace_weighted_square_fixed C X hX
  have hy := trace_weighted_square_fixed C Y hY
  simp only [Matrix.mul_add, Matrix.trace_add, Complex.add_re] at hsum
  unfold MatrixMoments.covarianceEntry
  simp only [if_true, show (1 : Fin 2) ≠ 0 by decide, if_false]
  have hsquare : (X + Y) ^ 2 = X ^ 2 + Y ^ 2 + (X * Y + Y * X) := by
    simp only [pow_two, add_mul, mul_add]
    abel
  rw [hsquare, Matrix.mul_add, Matrix.mul_add, Matrix.trace_add,
    Matrix.trace_add, Complex.add_re, Complex.add_re] at hsum
  have hsqsum :
      (∑ q : κ × κ × Fin 2,
        ((entryHermitian C q * X).trace.re +
          (entryHermitian C q * Y).trace.re) ^ 2) =
      (∑ q, (entryHermitian C q * X).trace.re ^ 2) +
        (∑ q, (entryHermitian C q * Y).trace.re ^ 2) +
          2 * ∑ q, (entryHermitian C q * X).trace.re *
            (entryHermitian C q * Y).trace.re := by
    simp_rw [add_sq]
    simp only [Finset.sum_add_distrib]
    simp only [Finset.mul_sum, mul_assoc]
    abel
  rw [hsqsum, hx, hy] at hsum
  linarith

variable {β S : Type*} [Fintype β] [CommRing S] [Algebra ℝ S]

/-- The fixed trace probes form a real Gram matrix for every Hermitian
matrix family, with no dependence on its coefficients. -/
def traceProbeMatrix (C : Matrix κ κ ℂ) (B : β → Matrix κ κ ℂ) :
    Matrix (κ × κ × Fin 2) β ℝ :=
  fun q b => (Matrix.trace (entryHermitian C q * B b)).re

omit [Fintype β] in
theorem covarianceMatrix_fixed_gram (C : Matrix κ κ ℂ)
    (B : β → Matrix κ κ ℂ) (hB : ∀ b, (B b).IsHermitian) :
    MatrixMoments.covarianceMatrix (Cᴴ * C) B =
      (traceProbeMatrix C B)ᵀ * traceProbeMatrix C B := by
  ext b c
  have h := covarianceEntry_fixed_gram C (B b) (B c) (hB b) (hB c)
  simpa [MatrixMoments.covarianceMatrix, traceProbeMatrix,
    Matrix.mul_apply, Matrix.transpose_apply] using h

/-- A PSD matrix supplies a fixed Hermitian probe family for the universal
covariance polynomial in any commutative real algebra, including algebras
with nilpotents. -/
theorem psd_fixed_covariance_squares (A : Matrix κ κ ℂ)
    (B : β → Matrix κ κ ℂ) (hA : A.PosSemidef)
    (hB : ∀ b, (B b).IsHermitian) :
    ∃ P : κ × κ × Fin 2 → Matrix κ κ ℂ,
      (∀ q, (P q).IsHermitian) ∧
      ∀ η : β → S,
        CovariancePolynomial.quadratic (MatrixMoments.covarianceMatrix A B) η =
          ∑ q, (∑ b, algebraMap ℝ S
            (Matrix.trace (P q * B b)).re * η b) ^ 2 := by
  obtain ⟨C, hC⟩ : ∃ C : Matrix κ κ ℂ, A = star C * C :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  simp only [Matrix.star_eq_conjTranspose] at hC
  refine ⟨entryHermitian C, entryHermitian_isHermitian C, ?_⟩
  intro η
  rw [hC, covarianceMatrix_fixed_gram C B hB]
  exact CovariancePolynomial.gram_quadratic (traceProbeMatrix C B) η

/-- The trace probes are chosen from `A` once and work simultaneously for
every Hermitian matrix family and every coefficient assignment. -/
theorem psd_fixed_covariance_squares_all_families (A : Matrix κ κ ℂ)
    (hA : A.PosSemidef) :
    ∃ P : κ × κ × Fin 2 → Matrix κ κ ℂ,
      (∀ q, (P q).IsHermitian) ∧
      ∀ (B : β → Matrix κ κ ℂ), (∀ b, (B b).IsHermitian) →
        ∀ η : β → S,
          CovariancePolynomial.quadratic (MatrixMoments.covarianceMatrix A B) η =
            ∑ q, (∑ b, algebraMap ℝ S
              (Matrix.trace (P q * B b)).re * η b) ^ 2 := by
  obtain ⟨C, hC⟩ : ∃ C : Matrix κ κ ℂ, A = star C * C :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  simp only [Matrix.star_eq_conjTranspose] at hC
  refine ⟨entryHermitian C, entryHermitian_isHermitian C, ?_⟩
  intro B hB η
  rw [hC, covarianceMatrix_fixed_gram C B hB]
  exact CovariancePolynomial.gram_quadratic (traceProbeMatrix C B) η

end
end QuaternionicSymmetry.FixedTraceGram
