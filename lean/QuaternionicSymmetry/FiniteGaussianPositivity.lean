import QuaternionicSymmetry.ComplexGaussianMatrix
import QuaternionicSymmetry.QuaternionicGaussianMoments
import QuaternionicSymmetry.AhatGaussianWeights

/-! The actual finite sums of Gaussian rank-one matrices used in the A-hat
representation satisfy the quaternionic moment sign. -/

namespace QuaternionicSymmetry.FiniteGaussianPositivity

open Module QuaternionicFundamental

noncomputable section

variable {α ι κ β V : Type*} [Fintype α] [Fintype ι] [Fintype κ] [DecidableEq κ]
  [Fintype β] [DecidableEq β] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

def moment (q : α → ℝ) (B : β → Matrix κ κ ℂ) (η : β → E V) (k : ℕ) : E V :=
  QuaternionicGaussianMoments.moment (ComplexGaussianMatrix.matrixPolynomial q) B η k

def normalizedMoment (q : α → ℝ) (B : β → Matrix κ κ ℂ)
    (η : β → E V) (k : ℕ) : E V := ((k.factorial : ℝ)⁻¹) • moment q B η k

theorem moment_mixed_in_positive_ray (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (q : α → ℝ) (hq : ∀ m, 0 ≤ q m)
    (B : β → Matrix κ κ ℂ) (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (k : ℕ) (hk : k ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (topForm Q c)
      (moment q B η k * form Q c ^ (Q.quaternionicDimension - k)) := by
  apply QuaternionicGaussianMoments.moment_mixed_in_positive_ray Q c
    (ComplexGaussianMatrix.matrixPolynomial q) B _ hB η hη k hk
  intro x
  exact ComplexGaussianMatrix.evalMatrix_matrixPolynomial_posSemidef q hq
    (fun p r => x (p, r))

theorem normalizedMoment_mixed_in_positive_ray (Q : QuaternionicStructure V)
    (c : Basis ι ℝ V) (q : α → ℝ) (hq : ∀ m, 0 ≤ q m)
    (B : β → Matrix κ κ ℂ) (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (k : ℕ) (hk : k ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (topForm Q c)
      (normalizedMoment q B η k * form Q c ^ (Q.quaternionicDimension - k)) := by
  rw [normalizedMoment, smul_mul_assoc]
  exact PositiveRay.smul (moment_mixed_in_positive_ray Q c q hq B hB η hη k hk)
    (by positivity)

def ahatPartialMoment (N : ℕ) (B : β → Matrix κ κ ℂ) (η : β → E V) (k : ℕ) : E V :=
  moment (fun m : Fin N => AhatGaussianWeights.weight (m.val + 1)) B η k

theorem ahatPartialMoment_mixed_in_positive_ray (Q : QuaternionicStructure V)
    (c : Basis ι ℝ V) (N : ℕ) (B : β → Matrix κ κ ℂ)
    (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (k : ℕ) (hk : k ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (topForm Q c)
      (ahatPartialMoment N B η k * form Q c ^ (Q.quaternionicDimension - k)) :=
  moment_mixed_in_positive_ray Q c _ (fun _ => AhatGaussianWeights.weight_nonneg _)
    B hB η hη k hk

end
end QuaternionicSymmetry.FiniteGaussianPositivity
