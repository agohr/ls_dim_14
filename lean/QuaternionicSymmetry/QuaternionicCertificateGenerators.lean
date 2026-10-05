import QuaternionicSymmetry.RealCertificateEvaluation
import QuaternionicSymmetry.QuaternionicLowMomentPositivity
import QuaternionicSymmetry.QuaternionicRankTwoPositivity

/-! Actual quaternionic exterior-form evaluation of the rational certificate
generators, with every needed mixed sign discharged. -/

namespace QuaternionicSymmetry.QuaternionicCertificateGenerators

open Module QuaternionicFundamental QuaternionicTracePositivity
open QuaternionicAhatPositivity AlgebraCertificates

noncomputable section

variable {ι κ β V : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
  [Fintype β] [DecidableEq β] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

omit [DecidableEq β] [FiniteDimensional ℝ V] in
def evaluateForms (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (B : β → Matrix κ κ ℂ) (η : β → E V) : P →ₐ[ℚ] CE V :=
  evaluate (embed (V := V) (form Q c)) (tracePower B η 1) (tracePower B η 2)
    (tracePower B η 3) (tracePower B η 4)

omit [DecidableEq β] [FiniteDimensional ℝ V] in
@[simp] theorem evaluateForms_U (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (B : β → Matrix κ κ ℂ) (η : β → E V) :
    evaluateForms Q c B η U = embed (V := V) (form Q c) := evaluate_U _ _ _ _ _

theorem Z₁_power_mixed_positive (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (B : β → Matrix κ κ ℂ) (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (k : ℕ) (hk : k ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (embed (V := V) (topForm Q c))
      (evaluateForms Q c B η (Z₁ ^ k * U ^ (Q.quaternionicDimension - k))) := by
  simpa only [evaluateForms, map_mul, map_pow, evaluate_Z₁, evaluate_U] using
    QuaternionicLowMomentPositivity.tracePower_one_pow_mixed_in_positive_ray Q c B hB η hη k hk

theorem F₂_mixed_positive (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (B : β → Matrix κ κ ℂ) (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (hk : 2 ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (embed (V := V) (topForm Q c))
      (evaluateForms Q c B η (F₂ * U ^ (Q.quaternionicDimension - 2))) := by
  simpa only [evaluateForms, map_mul, map_pow, evaluate_U, RealCertificateEvaluation.evaluate_F₂] using
    QuaternionicAhatPositivity.F₂_mixed_in_positive_ray Q c B hB η hη hk

theorem F₃_mixed_positive (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (B : β → Matrix κ κ ℂ) (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (hk : 3 ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (embed (V := V) (topForm Q c))
      (evaluateForms Q c B η (F₃ * U ^ (Q.quaternionicDimension - 3))) := by
  simpa only [evaluateForms, map_mul, map_pow, evaluate_U, RealCertificateEvaluation.evaluate_F₃] using
    QuaternionicAhatPositivity.F₃_mixed_in_positive_ray Q c B hB η hη hk

theorem F₄_mixed_positive (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (B : β → Matrix κ κ ℂ) (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (hk : 4 ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (embed (V := V) (topForm Q c))
      (evaluateForms Q c B η (F₄ * U ^ (Q.quaternionicDimension - 4))) := by
  simpa only [evaluateForms, map_mul, map_pow, evaluate_U, RealCertificateEvaluation.evaluate_F₄] using
    QuaternionicAhatPositivity.F₄_mixed_in_positive_ray Q c B hB η hη hk

theorem M₂₁_mixed_positive (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (B : β → Matrix κ κ ℂ) (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (hk : 2 ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (embed (V := V) (topForm Q c))
      (evaluateForms Q c B η (M₂₁ (Fintype.card κ) * U ^ (Q.quaternionicDimension - 2))) := by
  simpa only [evaluateForms, map_mul, map_pow, evaluate_U, RealCertificateEvaluation.evaluate_M₂₁,
    Rat.cast_natCast] using
    QuaternionicLowMomentPositivity.M₂₁_mixed_in_positive_ray Q c B hB η hη hk

theorem M₃₁_mixed_positive (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (B : β → Matrix κ κ ℂ) (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (hk : 3 ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (embed (V := V) (topForm Q c))
      (evaluateForms Q c B η (M₃₁ (Fintype.card κ) * U ^ (Q.quaternionicDimension - 3))) := by
  simpa only [evaluateForms, map_mul, map_pow, evaluate_U, RealCertificateEvaluation.evaluate_M₃₁,
    Rat.cast_natCast] using
    QuaternionicLowMomentPositivity.M₃₁_mixed_in_positive_ray Q c B hB η hη hk

theorem M₃₂_mixed_positive (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (hr : 3 ≤ Fintype.card κ)
    (B : β → Matrix κ κ ℂ) (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (hk : 3 ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (embed (V := V) (topForm Q c))
      (evaluateForms Q c B η (M₃₂ (Fintype.card κ) * U ^ (Q.quaternionicDimension - 3))) := by
  simpa only [evaluateForms, map_mul, map_pow, evaluate_U, RealCertificateEvaluation.evaluate_M₃₂,
    Rat.cast_natCast] using
    QuaternionicRankTwoPositivity.M₃₂_mixed_in_positive_ray Q c hr B hB η hη hk

end
end QuaternionicSymmetry.QuaternionicCertificateGenerators
