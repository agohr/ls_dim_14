import QuaternionicSymmetry.QuaternionicGaussianTraceMoments
import QuaternionicSymmetry.GaussianWeightedBlockMoments
import QuaternionicSymmetry.AhatPositiveLimits

/-! The A-hat coefficient polynomials through order four have the required
pointwise quaternionic sign. Finite Gaussian positivity and the proved
coefficient limits discharge the entire finite-approximation premise. -/

namespace QuaternionicSymmetry.QuaternionicAhatPositivity

open Module QuaternionicFundamental QuaternionicTracePositivity
open QuaternionicGaussianTraceMoments

noncomputable section

variable {ι κ β V : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
  [Fintype β] [DecidableEq β] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

def tracePower (B : β → Matrix κ κ ℂ) (η : β → E V) (j : ℕ) : CE V :=
  Matrix.trace (curvatureSquare B η ^ j)

theorem F₂_mixed_in_positive_ray (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (B : β → Matrix κ κ ℂ) (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (hk : 2 ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (embed (V := V) (topForm Q c))
      ((algebraMap ℝ (CE V) (1 / 1152) * tracePower B η 1 ^ 2 +
        algebraMap ℝ (CE V) (1 / 2880) * tracePower B η 2) *
          embed (V := V) (form Q c) ^ (Q.quaternionicDimension - 2)) := by
  apply AhatPositiveLimits.contains_e₂_limit (embed_topForm_ne_zero Q c)
  intro N
  let q : Fin N → ℝ := fun m => AhatGaussianWeights.weight m.val
  have he := GaussianWeightedBlockMoments.normalized_moment_two_eq_eval q
    (curvatureSquare B η)
  simp only [q, ComplexGaussianExponentialCoefficients.fin_weight_logWeightParameters] at he
  have hp := normalized_moment_mixed_in_positive_ray Q c q
    (fun m => AhatGaussianWeights.weight_nonneg m.val) B hB η hη 2 hk
  norm_num only [Nat.factorial, Nat.cast_ofNat, inv_eq_one_div] at hp
  rw [he] at hp
  simpa only [MvPolynomial.eval_mul, MvPolynomial.eval_C, tracePower, pow_one] using hp

theorem F₃_mixed_in_positive_ray (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (B : β → Matrix κ κ ℂ) (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (hk : 3 ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (embed (V := V) (topForm Q c))
      ((algebraMap ℝ (CE V) (1 / 82944) * tracePower B η 1 ^ 3 +
        algebraMap ℝ (CE V) (1 / 69120) * tracePower B η 1 * tracePower B η 2 +
        algebraMap ℝ (CE V) (1 / 181440) * tracePower B η 3) *
          embed (V := V) (form Q c) ^ (Q.quaternionicDimension - 3)) := by
  apply AhatPositiveLimits.contains_e₃_limit (embed_topForm_ne_zero Q c)
  intro N
  let q : Fin N → ℝ := fun m => AhatGaussianWeights.weight m.val
  have he := GaussianWeightedBlockMoments.normalized_moment_three_eq_eval q
    (curvatureSquare B η)
  simp only [q, ComplexGaussianExponentialCoefficients.fin_weight_logWeightParameters] at he
  have hp := normalized_moment_mixed_in_positive_ray Q c q
    (fun m => AhatGaussianWeights.weight_nonneg m.val) B hB η hη 3 hk
  norm_num only [Nat.factorial, Nat.cast_ofNat, inv_eq_one_div] at hp
  rw [he] at hp
  simpa only [MvPolynomial.eval_mul, MvPolynomial.eval_C, tracePower, pow_one] using hp

theorem F₄_mixed_in_positive_ray (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (B : β → Matrix κ κ ℂ) (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (hk : 4 ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (embed (V := V) (topForm Q c))
      ((algebraMap ℝ (CE V) (1 / 7962624) * tracePower B η 1 ^ 4 +
        algebraMap ℝ (CE V) (1 / 3317760) * tracePower B η 1 ^ 2 * tracePower B η 2 +
        algebraMap ℝ (CE V) (1 / 16588800) * tracePower B η 2 ^ 2 +
        algebraMap ℝ (CE V) (1 / 4354560) * tracePower B η 1 * tracePower B η 3 +
        algebraMap ℝ (CE V) (1 / 9676800) * tracePower B η 4) *
          embed (V := V) (form Q c) ^ (Q.quaternionicDimension - 4)) := by
  apply AhatPositiveLimits.contains_e₄_limit (embed_topForm_ne_zero Q c)
  intro N
  let q : Fin N → ℝ := fun m => AhatGaussianWeights.weight m.val
  have he := GaussianWeightedBlockMoments.normalized_moment_four_eq_eval q
    (curvatureSquare B η)
  simp only [q, ComplexGaussianExponentialCoefficients.fin_weight_logWeightParameters] at he
  have hp := normalized_moment_mixed_in_positive_ray Q c q
    (fun m => AhatGaussianWeights.weight_nonneg m.val) B hB η hη 4 hk
  norm_num only [Nat.factorial, Nat.cast_ofNat, inv_eq_one_div] at hp
  rw [he] at hp
  simpa only [MvPolynomial.eval_mul, MvPolynomial.eval_C, tracePower, pow_one] using hp

end
end QuaternionicSymmetry.QuaternionicAhatPositivity
