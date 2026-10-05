import QuaternionicSymmetry.QuaternionicAhatPositivity

/-! The explicit second and third rank-one coefficient polynomials have
the required quaternionic sign. Gaussian moments give a direct proof of
these signs, including the positive dimension normalizations. -/

namespace QuaternionicSymmetry.QuaternionicLowMomentPositivity

open Module QuaternionicFundamental QuaternionicTracePositivity
open QuaternionicGaussianTraceMoments QuaternionicAhatPositivity
open scoped ComplexOrder

noncomputable section

variable {ι κ β V : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
  [Fintype β] [DecidableEq β] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem tracePower_one_pow_mixed_in_positive_ray
    (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (B : β → Matrix κ κ ℂ) (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (k : ℕ) (hk : k ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (embed (V := V) (topForm Q c))
      (tracePower B η 1 ^ k *
        embed (V := V) (form Q c) ^ (Q.quaternionicDimension - k)) := by
  have hp := QuaternionicTracePositivity.traceY_mixed_mem_positiveRay Q c
    (1 : Matrix κ κ ℂ) B Matrix.PosSemidef.one hB η hη k hk
  have hm : (1 : Matrix κ κ ℂ).map (algebraMap ℂ (CE V)) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  unfold traceY MatrixValuedForms.mapMatrix at hp
  rw [hm, Matrix.one_mul (α := CE V)] at hp
  simpa only [tracePower, curvatureSquare, pow_one] using hp

theorem scaled_quadratic_moment_mixed_in_positive_ray
    (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (B : β → Matrix κ κ ℂ) (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (k : ℕ) (hk : k ≤ Q.quaternionicDimension) (r : ℝ) (hr : 0 ≤ r) :
    PositiveRay.Contains (embed (V := V) (topForm Q c))
      (r • GaussianQuadraticPolynomial.moment (curvatureSquare B η) k *
        embed (V := V) (form Q c) ^ (Q.quaternionicDimension - k)) := by
  apply GaussianQuadraticTrace.scaled_moment_mul_contains
    (embed_topForm_ne_zero Q c) _ _ r hr
  intro z
  exact QuaternionicTracePositivity.traceY_mixed_mem_positiveRay Q c
    (ComplexGaussianRankOne.rankOne z) B
    (ComplexGaussianRankOne.rankOne_posSemidef z) hB η hη k hk

theorem M₂₁_mixed_in_positive_ray (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (B : β → Matrix κ κ ℂ) (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (hk : 2 ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (embed (V := V) (topForm Q c))
      (((Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) + 1))⁻¹ •
        (tracePower B η 1 ^ 2 + tracePower B η 2) *
          embed (V := V) (form Q c) ^ (Q.quaternionicDimension - 2)) := by
  have hp := scaled_quadratic_moment_mixed_in_positive_ray Q c B hB η hη 2 hk
    (((Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) + 1))⁻¹) (by positivity)
  rw [UniversalGaussianMatrixMoments.moment_two (S := CE V)] at hp
  simpa only [tracePower, pow_one] using hp

theorem M₃₁_mixed_in_positive_ray (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (B : β → Matrix κ κ ℂ) (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (hk : 3 ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (embed (V := V) (topForm Q c))
      (((Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) + 1) *
          ((Fintype.card κ : ℝ) + 2))⁻¹ •
        (tracePower B η 1 ^ 3 + 3 * tracePower B η 1 * tracePower B η 2 +
          2 * tracePower B η 3) *
            embed (V := V) (form Q c) ^ (Q.quaternionicDimension - 3)) := by
  have hp := scaled_quadratic_moment_mixed_in_positive_ray Q c B hB η hη 3 hk
    (((Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) + 1) *
      ((Fintype.card κ : ℝ) + 2))⁻¹) (by positivity)
  rw [UniversalGaussianMatrixMoments.moment_three (S := CE V)] at hp
  simpa only [tracePower, pow_one] using hp

end
end QuaternionicSymmetry.QuaternionicLowMomentPositivity
