import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveNorthVerticalSign
import QuaternionicSymmetry.FourDimensionalHalfSpinNormalizerHolomorphic

/-! Differentiate the literal normalizer-equivariance of the independent
projective Hopf map. This is an equality of actual manifold derivatives,
not just of homogeneous-fiber point actions. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveHopfMFDerivEquivariance

open scoped Manifold ContDiff
open QuaternionicIsometryNormalizer
  FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinNormalizerAction
  FourDimensionalHalfSpinNormalizerHolomorphic
  FourDimensionalHalfSpinHopfProjectiveDescent
  FourDimensionalHalfSpinHopfProjectiveSmooth
  FourDimensionalTwistorNormalizerQuotient
  QuaternionicNormalizerSphereSmooth
  ManifoldTwistorCoefficientSphere

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  (S : QuaternionicStructure E)

local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

theorem projectiveHopfGeometric_normalizerAction
    (g : normalizer S) (p : ProjectiveSpinor) :
    projectiveHopfGeometric (projectiveNormalizerAction S g p) =
      geometricAction S g (projectiveHopfGeometric p) := by
  unfold projectiveHopfGeometric geometricAction
  rw [projectiveHopf_normalizerAction]
  simp

theorem projectiveHopf_mfderiv_equivariant
    (g : normalizer S) (p : ProjectiveSpinor)
    (v : TangentSpace 𝓘(ℝ, Fin 1 → ℂ) p) :
    mfderiv 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) projectiveHopfGeometric
      (projectiveNormalizerAction S g p)
      (mfderiv 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, Fin 1 → ℂ)
        (projectiveNormalizerAction S g) p v) =
    mfderiv (𝓡 2) (𝓡 2) (geometricAction S g)
      (projectiveHopfGeometric p)
      (mfderiv 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2)
        projectiveHopfGeometric p v) := by
  have hfun : projectiveHopfGeometric ∘ projectiveNormalizerAction S g =
      geometricAction S g ∘ projectiveHopfGeometric := by
    funext q
    exact projectiveHopfGeometric_normalizerAction S g q
  have hderiv := congrArg
    (fun f : ProjectiveSpinor → geometricSphere =>
      mfderiv 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) f p v) hfun
  have hA : MDifferentiableAt 𝓘(ℝ, Fin 1 → ℂ)
      𝓘(ℝ, Fin 1 → ℂ) (projectiveNormalizerAction S g) p :=
    (projectiveNormalizerAction_realSmooth S g).mdifferentiableAt (by simp)
  have hH : MDifferentiableAt 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2)
      projectiveHopfGeometric p :=
    projectiveHopfGeometric_contMDiff.mdifferentiableAt (by simp)
  have hH' : MDifferentiableAt 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2)
      projectiveHopfGeometric (projectiveNormalizerAction S g p) :=
    projectiveHopfGeometric_contMDiff.mdifferentiableAt (by simp)
  have hG : MDifferentiableAt (𝓡 2) (𝓡 2)
      (geometricAction S g) (projectiveHopfGeometric p) :=
    (geometricAction_smooth S g).mdifferentiableAt (by simp)
  change mfderiv 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2)
      (projectiveHopfGeometric ∘ projectiveNormalizerAction S g) p v =
    mfderiv 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2)
      (geometricAction S g ∘ projectiveHopfGeometric) p v at hderiv
  rw [mfderiv_comp p hH' hA, mfderiv_comp p hG hH] at hderiv
  exact hderiv

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveHopfMFDerivEquivariance
