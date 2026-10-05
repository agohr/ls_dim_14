import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveHopfMFDerivEquivariance

/-! The actual projective normalizer derivative is complex-linear and
surjective on every true CP¹ tangent model. No global spin lift is used. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveNormalizerTangent

open scoped Manifold ContDiff
open QuaternionicIsometryNormalizer
  FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinNormalizerAction
  FourDimensionalHalfSpinNormalizerHolomorphic
  ManifoldComplexHolomorphicFactorization

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  (S : QuaternionicStructure E)

theorem projectiveAction_mfderiv_complex
    (g : normalizer S) (p : ProjectiveSpinor)
    (v : Fin 1 → ℂ) :
    mfderiv 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, Fin 1 → ℂ)
      (projectiveNormalizerAction S g) p (Complex.I • v) =
    Complex.I • (show Fin 1 → ℂ from
      mfderiv 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, Fin 1 → ℂ)
        (projectiveNormalizerAction S g) p v) :=
  real_derivative_commutes_i_of_holomorphic
    (projectiveNormalizerAction_holomorphic S g) p v

theorem projectiveAction_mfderiv_surjective
    (g : normalizer S) (p : ProjectiveSpinor) :
    Function.Surjective
      (mfderiv 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, Fin 1 → ℂ)
        (projectiveNormalizerAction S g) p) := by
  let A : ProjectiveSpinor → ProjectiveSpinor :=
    projectiveNormalizerAction S g
  let B : ProjectiveSpinor → ProjectiveSpinor :=
    projectiveNormalizerAction S g⁻¹
  have hBA : B (A p) = p := by
    change (g⁻¹ : normalizer S) • (g • p) = p
    simp
  have hAB : A ∘ B = id := by
    funext q
    change g • (g⁻¹ • q) = q
    simp
  have hA : MDifferentiableAt 𝓘(ℝ, Fin 1 → ℂ)
      𝓘(ℝ, Fin 1 → ℂ) A (B (A p)) :=
    (projectiveNormalizerAction_realSmooth S g).mdifferentiableAt (by simp)
  have hB : MDifferentiableAt 𝓘(ℝ, Fin 1 → ℂ)
      𝓘(ℝ, Fin 1 → ℂ) B (A p) :=
    (projectiveNormalizerAction_realSmooth S g⁻¹).mdifferentiableAt (by simp)
  have h := mfderiv_comp (I := 𝓘(ℝ, Fin 1 → ℂ))
    (I' := 𝓘(ℝ, Fin 1 → ℂ)) (I'' := 𝓘(ℝ, Fin 1 → ℂ))
    (A p) hA hB
  rw [hAB, mfderiv_id, hBA] at h
  intro v
  refine ⟨(mfderiv 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, Fin 1 → ℂ) B (A p)) v, ?_⟩
  have hv := congrArg (fun T : (Fin 1 → ℂ) →L[ℝ] (Fin 1 → ℂ) => T v) h
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    A, B] using hv.symm

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveNormalizerTangent
