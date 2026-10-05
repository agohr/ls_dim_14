import QuaternionicSymmetry.MatrixMoments
import QuaternionicSymmetry.CovariancePolynomial
import Mathlib.Tactic

/-!
Trace expansion for matrix-valued coefficients in a commutative complex
algebra.  Matrix products remain noncommutative; commutativity is used only
for the coefficient algebra and finite scalar sums.
-/

namespace QuaternionicSymmetry.MatrixValuedForms

open Matrix

variable {ι β S : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]
  [CommRing S] [Algebra ℂ S]

/-- Entrywise extension of the complex-to-coefficient-algebra map. -/
def mapMatrix (M : Matrix ι ι ℂ) : Matrix ι ι S :=
  M.map (algebraMap ℂ S)

/-- A finite coefficient-algebra linear combination of matrix forms. -/
def weightedMatrix (B : β → Matrix ι ι ℂ) (η : β → S) : Matrix ι ι S :=
  ∑ b, η b • mapMatrix (S := S) (B b)

omit [DecidableEq ι] in
private theorem trace_mapMatrix (M : Matrix ι ι ℂ) :
    trace (mapMatrix (S := S) M) = algebraMap ℂ S (trace M) := by
  simp [mapMatrix, Matrix.trace]

omit [DecidableEq ι] in
private theorem mapMatrix_mul (M N : Matrix ι ι ℂ) :
    mapMatrix (S := S) (M * N) = mapMatrix (S := S) M * mapMatrix (S := S) N := by
  ext i j
  simp [mapMatrix, Matrix.mul_apply]

omit [DecidableEq ι] in
private theorem trace_term (A : Matrix ι ι ℂ) (B₁ B₂ : Matrix ι ι ℂ)
    (r s : S) :
    trace (mapMatrix (S := S) A * (r • mapMatrix (S := S) B₁) * (s • mapMatrix (S := S) B₂)) =
      algebraMap ℂ S (trace (A * B₁ * B₂)) * r * s := by
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_smul]
  rw [← mapMatrix_mul (M := A) (N := B₁)]
  rw [← mapMatrix_mul (M := A * B₁) (N := B₂), trace_mapMatrix]
  simp only [smul_eq_mul]
  ring

/-- Unsymmetrized trace expansion of the square of a weighted matrix sum. -/
theorem trace_weightedMatrix_sq (A : Matrix ι ι ℂ)
    (B : β → Matrix ι ι ℂ) (η : β → S) :
    trace (mapMatrix (S := S) A * weightedMatrix B η ^ 2) =
      ∑ a, ∑ b, algebraMap ℂ S (trace (A * B a * B b)) * η a * η b := by
  classical
  simp only [weightedMatrix, pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Matrix.trace_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro b hb
  simpa [Matrix.mul_assoc] using trace_term A (B b) (B a) (η b) (η a)

/-- Symmetrized trace expansion, matching the real covariance coefficient. -/
theorem trace_weightedMatrix_sq_symm (A : Matrix ι ι ℂ)
    (B : β → Matrix ι ι ℂ) (η : β → S)
    (_hA : A.IsHermitian) (_hB : ∀ b, (B b).IsHermitian) :
    trace (mapMatrix (S := S) A * weightedMatrix B η ^ 2) =
      ∑ a, ∑ b,
        algebraMap ℂ S
          (trace (A * (B a * B b + B b * B a)) / (2 : ℂ)) * η a * η b := by
  classical
  rw [trace_weightedMatrix_sq]
  let X : β → β → S := fun a b =>
    algebraMap ℂ S (trace (A * B a * B b)) * η a * η b
  have hswap : (∑ a, ∑ b, X b a) = ∑ a, ∑ b, X a b := by
    rw [Finset.sum_comm]
  calc
    (∑ a, ∑ b, X a b) =
        ((∑ a, ∑ b, X a b) + (∑ a, ∑ b, X b a)) *
          algebraMap ℂ S ((1 / 2 : ℂ)) := by
      rw [hswap]
      have hhalf : algebraMap ℂ S ((1 / 2 : ℂ)) * (2 : S) = 1 := by
        rw [show (2 : S) = algebraMap ℂ S (2 : ℂ) by exact (map_ofNat (algebraMap ℂ S) 2).symm]
        rw [← map_mul]
        norm_num
      calc
        (∑ a, ∑ b, X a b) = (∑ a, ∑ b, X a b) *
            (algebraMap ℂ S ((1 / 2 : ℂ)) * (2 : S)) := by rw [hhalf, mul_one]
        _ = ((∑ a, ∑ b, X a b) + (∑ a, ∑ b, X a b)) *
            algebraMap ℂ S ((1 / 2 : ℂ)) := by ring
    _ = (∑ a, ∑ b, (X a b + X b a)) *
          algebraMap ℂ S ((1 / 2 : ℂ)) := by
      congr 1
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a ha
      rw [← Finset.sum_add_distrib]
    _ = ∑ a, ∑ b, (X a b + X b a) *
          algebraMap ℂ S ((1 / 2 : ℂ)) := by
      simp only [Finset.sum_mul]
    _ = ∑ a, ∑ b,
        algebraMap ℂ S
          (trace (A * (B a * B b + B b * B a)) / (2 : ℂ)) * η a * η b := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      dsimp [X]
      have hcoeff :
          algebraMap ℂ S (trace (A * (B a * B b + B b * B a)) / (2 : ℂ)) =
            (algebraMap ℂ S (trace (A * B a * B b)) +
              algebraMap ℂ S (trace (A * B b * B a))) *
                algebraMap ℂ S ((1 / 2 : ℂ)) := by
        have hcomplex :
            trace (A * (B a * B b + B b * B a)) / (2 : ℂ) =
              (trace (A * B a * B b) + trace (A * B b * B a)) * (1 / 2 : ℂ) := by
          simp only [Matrix.mul_add, Matrix.trace_add, Matrix.mul_assoc]
          ring
        rw [hcomplex, map_mul, map_add]
      rw [hcoeff]
      ring

/-- Over the induced real algebra structure, the trace expansion is the covariance polynomial. -/
theorem trace_weightedMatrix_sq_covariance (A : Matrix ι ι ℂ)
    (B : β → Matrix ι ι ℂ) (η : β → S)
    (hA : A.IsHermitian) (hB : ∀ b, (B b).IsHermitian) :
    trace (mapMatrix (S := S) A * weightedMatrix B η ^ 2) =
      QuaternionicSymmetry.CovariancePolynomial.quadratic
        (QuaternionicSymmetry.MatrixMoments.covarianceMatrix A B) η := by
  rw [trace_weightedMatrix_sq_symm A B η hA hB]
  unfold QuaternionicSymmetry.CovariancePolynomial.quadratic
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have hc :
      algebraMap ℂ S (trace (A * (B a * B b + B b * B a)) / (2 : ℂ)) =
        algebraMap ℝ S (QuaternionicSymmetry.MatrixMoments.covarianceEntry A B a b) := by
    rw [← QuaternionicSymmetry.MatrixMoments.covarianceEntry_complex A B hA hB a b]
    exact (IsScalarTower.algebraMap_apply ℝ ℂ S _).symm
  rw [hc]
  rfl

end QuaternionicSymmetry.MatrixValuedForms
