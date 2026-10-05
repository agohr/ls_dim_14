import QuaternionicSymmetry.GaussianMatrixTracePolynomial
import QuaternionicSymmetry.QuaternionicTracePositivity
import QuaternionicSymmetry.GaussianPositiveRay
import QuaternionicSymmetry.GaussianAffineMoments

/-! Positivity of the actual Gaussian matrix trace moments in the
complexification of the quaternionic even exterior algebra. -/

namespace QuaternionicSymmetry.QuaternionicGaussianTraceMoments

open Module QuaternionicFundamental QuaternionicTracePositivity

noncomputable section

variable {α ι κ β V : Type*} [Fintype α] [Fintype ι] [Fintype κ] [DecidableEq κ]
  [Fintype β] [DecidableEq β] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

def curvatureSquare (B : β → Matrix κ κ ℂ) (η : β → E V) : Matrix κ κ (CE V) :=
  -(MatrixValuedForms.weightedMatrix B (fun b => embed (V := V) (η b))) ^ 2

theorem moment_mixed_in_positive_ray (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (q : α → ℝ) (hq : ∀ m, 0 ≤ q m)
    (B : β → Matrix κ κ ℂ) (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (k : ℕ) (hk : k ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (embed (V := V) (topForm Q c))
      (GaussianMatrixTracePolynomial.moment q (curvatureSquare B η) k *
        embed (V := V) (form Q c) ^ (Q.quaternionicDimension - k)) := by
  apply GaussianMatrixTracePolynomial.moment_mul_contains
    (QuaternionicTracePositivity.embed_topForm_ne_zero Q c)
  intro x
  exact QuaternionicTracePositivity.traceY_mixed_mem_positiveRay Q c
    (PolynomialCovariance.evalMatrix (ComplexGaussianMatrix.matrixPolynomial q) x)
    B (ComplexGaussianMatrix.evalMatrix_matrixPolynomial_posSemidef_flat q hq x)
    hB η hη k hk

theorem normalized_moment_mixed_in_positive_ray (Q : QuaternionicStructure V)
    (c : Basis ι ℝ V) (q : α → ℝ) (hq : ∀ m, 0 ≤ q m)
    (B : β → Matrix κ κ ℂ) (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (k : ℕ) (hk : k ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (embed (V := V) (topForm Q c))
      (((k.factorial : ℝ)⁻¹) •
        GaussianMatrixTracePolynomial.moment q (curvatureSquare B η) k *
          embed (V := V) (form Q c) ^ (Q.quaternionicDimension - k)) := by
  apply GaussianMatrixTracePolynomial.normalized_moment_mul_contains
    (QuaternionicTracePositivity.embed_topForm_ne_zero Q c)
  intro x
  exact QuaternionicTracePositivity.traceY_mixed_mem_positiveRay Q c
    (PolynomialCovariance.evalMatrix (ComplexGaussianMatrix.matrixPolynomial q) x)
    B (ComplexGaussianMatrix.evalMatrix_matrixPolynomial_posSemidef_flat q hq x)
    hB η hη k hk

end
end QuaternionicSymmetry.QuaternionicGaussianTraceMoments
