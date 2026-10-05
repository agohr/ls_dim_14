import QuaternionicSymmetry.MatrixMoments
import QuaternionicSymmetry.EvenForms
import Mathlib.Tactic

/-! The algebraic sum-of-squares step for the numerical covariance matrix.

The target is any commutative real algebra, including the algebra of even
exterior expressions. This identity does not assert an order on that algebra.
-/

namespace QuaternionicSymmetry.CovariancePolynomial

open scoped BigOperators ComplexOrder

variable {α β S : Type*} [Fintype α] [Fintype β] [CommRing S] [Algebra ℝ S]

noncomputable def quadratic (G : Matrix β β ℝ) (η : β → S) : S :=
  ∑ a, ∑ b, algebraMap ℝ S (G a b) * η a * η b

/-- A numerical Gram factorization gives a polynomial sum of squares. -/
theorem gram_quadratic (C : Matrix α β ℝ) (η : β → S) :
    quadratic (C.transpose * C) η =
      ∑ s, (∑ a, algebraMap ℝ S (C s a) * η a) ^ 2 := by
  classical
  simp only [quadratic, Matrix.mul_apply, Matrix.transpose_apply, map_sum, map_mul,
    pow_two, Finset.sum_mul, Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The Hermitian covariance yields a sum of squares in every commutative real algebra. -/
theorem covariance_sum_squares {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (B : β → Matrix ι ι ℂ)
    (hA : A.PosSemidef) (hB : ∀ b, (B b).IsHermitian) (η : β → S) :
    ∃ θ : β → S, quadratic (MatrixMoments.covarianceMatrix A B) η = ∑ s, θ s ^ 2 := by
  obtain ⟨C, hC⟩ := MatrixMoments.covarianceMatrix_factorization A B hA hB
  refine ⟨fun s => ∑ a, algebraMap ℝ S (C s a) * η a, ?_⟩
  rw [hC, gram_quadratic]

end QuaternionicSymmetry.CovariancePolynomial
