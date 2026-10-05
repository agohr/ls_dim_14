import QuaternionicSymmetry.AlgebraPolynomialExt
import QuaternionicSymmetry.CovariancePolynomial

/-! Polynomial numerical matrices give polynomial covariance expressions
with coefficients in any commutative real algebra. -/

namespace QuaternionicSymmetry.PolynomialCovariance

open scoped BigOperators
open MvPolynomial

noncomputable section

variable {δ κ β S : Type*} [Fintype δ] [Fintype κ] [DecidableEq κ]
  [Fintype β] [CommRing S] [Algebra ℝ S]

def evalMatrix (A : Matrix κ κ (MvPolynomial δ ℂ)) (x : δ → ℝ) : Matrix κ κ ℂ :=
  A.map (MvPolynomial.eval (fun i => algebraMap ℝ ℂ (x i)))

def entry (A : Matrix κ κ (MvPolynomial δ ℂ)) (B : β → Matrix κ κ ℂ)
    (a b : β) : MvPolynomial δ ℝ :=
  C (1 / 2 : ℝ) * AlgebraPolynomialExt.mapCoefficients Complex.reLm
    (Matrix.trace (A * (B a * B b + B b * B a).map C))

omit [Fintype β] [DecidableEq κ] in
theorem eval_entry (A : Matrix κ κ (MvPolynomial δ ℂ)) (B : β → Matrix κ κ ℂ)
    (a b : β) (x : δ → ℝ) :
    (entry A B a b).eval x = MatrixMoments.covarianceEntry (evalMatrix A x) B a b := by
  have ht (D : Matrix κ κ ℂ) :
      MvPolynomial.eval (fun i => algebraMap ℝ ℂ (x i)) (Matrix.trace (A * D.map C)) =
        Matrix.trace (evalMatrix A x * D) := by
    simp [Matrix.trace, Matrix.mul_apply, evalMatrix, Matrix.map_apply]
  rw [entry, map_mul, eval_C, AlgebraPolynomialExt.eval_mapCoefficients, ht]
  change (1 / 2 : ℝ) * (Matrix.trace (evalMatrix A x *
    (B a * B b + B b * B a))).re = _ / 2
  ring

def expression (A : Matrix κ κ (MvPolynomial δ ℂ)) (B : β → Matrix κ κ ℂ)
    (η : β → S) : MvPolynomial δ S :=
  -(∑ a, ∑ b, MvPolynomial.map (algebraMap ℝ S) (entry A B a b) * C (η a) * C (η b))

omit [DecidableEq κ] in
theorem eval_expression (A : Matrix κ κ (MvPolynomial δ ℂ)) (B : β → Matrix κ κ ℂ)
    (η : β → S) (x : δ → ℝ) :
    (expression A B η).eval (fun i => algebraMap ℝ S (x i)) =
      -CovariancePolynomial.quadratic (MatrixMoments.covarianceMatrix (evalMatrix A x) B) η := by
  unfold expression CovariancePolynomial.quadratic MatrixMoments.covarianceMatrix
  simp only [map_neg, map_sum, map_mul, eval_C]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have h := MvPolynomial.map_eval (algebraMap ℝ S) x (entry A B a b)
  simp only [Function.comp_def] at h
  rw [← h, eval_entry]

end
end QuaternionicSymmetry.PolynomialCovariance
