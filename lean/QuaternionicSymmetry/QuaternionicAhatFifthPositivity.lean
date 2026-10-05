import QuaternionicSymmetry.QuaternionicAhatPositivity
import QuaternionicSymmetry.GaussianWeightedBlockFifth

/-! The fifth positive A-hat/Gaussian coefficient as a pointwise top-form
inequality. The input is an actual quaternionic curvature expansion at one
point; no global characteristic-class or index assertion is made here. -/

namespace QuaternionicSymmetry.QuaternionicAhatFifthPositivity

open Module QuaternionicFundamental QuaternionicTracePositivity
open QuaternionicGaussianTraceMoments QuaternionicAhatPositivity

noncomputable section


variable {ι κ β V : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
  [Fintype β] [DecidableEq β] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The fifth limiting Gaussian trace polynomial at a point. -/
def fifthTraceCoefficient (B : β → Matrix κ κ ℂ) (η : β → E V) : CE V :=
  AhatFifthCoefficientLimits.coefficient
    (tracePower B η 1) (tracePower B η 2) (tracePower B η 3)
    (tracePower B η 4) (tracePower B η 5)

/-- The actual finite Gaussian moment has a pointwise sign, and its fifth
coefficient converges to the seven-term trace expression. -/
theorem F₅_mixed_in_positive_ray (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (B : β → Matrix κ κ ℂ) (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (hk : 5 ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (embed (V := V) (topForm Q c))
      (fifthTraceCoefficient B η *
          embed (V := V) (form Q c) ^ (Q.quaternionicDimension - 5)) := by
  change PositiveRay.Contains (embed (V := V) (topForm Q c))
    (AhatFifthCoefficientLimits.coefficient
      (tracePower B η 1) (tracePower B η 2) (tracePower B η 3)
      (tracePower B η 4) (tracePower B η 5) *
      embed (V := V) (form Q c) ^ (Q.quaternionicDimension - 5))
  apply AhatFifthCoefficientLimits.contains_coefficient_limit
    (embed_topForm_ne_zero Q c)
  intro N
  let q : Fin N → ℝ := fun m => AhatGaussianWeights.weight m.val
  have he := GaussianWeightedBlockFifth.normalized_moment_five_eq_eval q
    (curvatureSquare B η)
  simp only [q, GaussianWeightedBlockFifth.fin_weight_logWeightParameters] at he
  have hp := normalized_moment_mixed_in_positive_ray Q c q
    (fun m => AhatGaussianWeights.weight_nonneg m.val) B hB η hη 5 hk
  norm_num only [Nat.factorial, Nat.cast_ofNat, inv_eq_one_div] at hp
  rw [he] at hp
  simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C]
  simp only [tracePower, pow_one]
  exact hp

end
end QuaternionicSymmetry.QuaternionicAhatFifthPositivity
