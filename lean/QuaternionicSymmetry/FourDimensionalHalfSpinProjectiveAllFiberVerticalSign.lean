import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveNormalizerTangent
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveNormalizerTransitive

/-! The literal projective Hopf map is anti-complex at every point of the
true CP¹ fiber, relative to the independently smooth geometric sphere's
quaternionic vertical tensor. This uses actual transitivity, holomorphic
projective tangent action, and normalizer sphere mfderiv covariance. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveAllFiberVerticalSign

open scoped Manifold
open QuaternionicIsometryNormalizer
  FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinProjectiveMobiusAction
  FourDimensionalHalfSpinProjectiveNormalizerTransitive
  FourDimensionalHalfSpinProjectiveNorthVerticalSign
  FourDimensionalHalfSpinProjectiveHopfMFDerivEquivariance
  FourDimensionalHalfSpinProjectiveNormalizerTangent
  FourDimensionalHalfSpinNormalizerAction
  FourDimensionalHalfSpinHopfProjectiveSmooth
  FourDimensionalHalfSpinHopfProjectiveDescent
  FourDimensionalTwistorNormalizerQuotient
  FourDimensionalTwistorHomogeneousFiber
  ManifoldTwistorVerticalComplex
  ManifoldTwistorCoefficientSphere
  QuaternionicNormalizerSphereSmooth
  QuaternionicNormalizerSphereTangentCovariance

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  (S : QuaternionicStructure E)

local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

theorem projectiveHopf_mfderiv_anti_complex
    (S : QuaternionicStructure E)
    (p : ProjectiveSpinor) (w : Fin 1 → ℂ) :
    mfderiv 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) projectiveHopfGeometric
      p (Complex.I • w) =
    -sphereVerticalComplex (projectiveHopf p)
      (mfderiv 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2)
        projectiveHopfGeometric p w) := by
  let p₀ : ProjectiveSpinor := affineSpinorPoint 0
  obtain ⟨g, hg⟩ := normalizer_transitive S p
  let A := projectiveNormalizerAction S g
  let G := geometricAction S g
  let H := projectiveHopfGeometric
  have hA : A p₀ = p := hg
  have hH0 : H p₀ = coefficientSphereHomeomorph north := by
    simp [H, p₀, projectiveHopfGeometric, projectiveHopf_affineZero]
  have hGp : G (coefficientSphereHomeomorph north) =
      coefficientSphereHomeomorph (projectiveHopf p) := by
    rw [← hH0]
    rw [← hA]
    exact (projectiveHopfGeometric_normalizerAction S g p₀).symm
  have hact : act S g north = projectiveHopf p := by
    apply coefficientSphereHomeomorph.injective
    exact hGp
  have hsurj := projectiveAction_mfderiv_surjective S g p₀
  obtain ⟨v, hv⟩ := hsurj w
  change Fin 1 → ℂ at v
  have hcomplex := projectiveAction_mfderiv_complex S g p₀ v
  have heq (u : Fin 1 → ℂ) :=
    projectiveHopf_mfderiv_equivariant S g p₀ u
  have htarget (u : Fin 1 → ℂ) :
      mfderiv 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) H p
        (mfderiv 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, Fin 1 → ℂ) A p₀ u) =
      mfderiv (𝓡 2) (𝓡 2) G (coefficientSphereHomeomorph north)
        (mfderiv 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) H p₀ u) := by
    have hu := heq u
    change projectiveNormalizerAction S g p₀ = p at hA
    change projectiveHopfGeometric p₀ = coefficientSphereHomeomorph north at hH0
    rw [hA, hH0] at hu
    exact hu
  have hnat := sphereVerticalComplex_geometricAction S g north
    (mfderiv 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) H p₀ v)
  rw [hact] at hnat
  calc
    mfderiv 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) H p (Complex.I • w) =
        mfderiv 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) H p
          (mfderiv 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, Fin 1 → ℂ)
            A p₀ (Complex.I • v)) := by rw [hcomplex, hv]
    _ = mfderiv (𝓡 2) (𝓡 2) G (coefficientSphereHomeomorph north)
          (mfderiv 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) H p₀
            (Complex.I • v)) := htarget _
    _ = mfderiv (𝓡 2) (𝓡 2) G (coefficientSphereHomeomorph north)
          (-sphereVerticalComplex north
            (mfderiv 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) H p₀ v)) := by
            have hn : mfderiv 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) H p₀
                (Complex.I • v) =
              -sphereVerticalComplex north
                (mfderiv 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) H p₀ v) := by
              exact north_projectiveHopf_mfderiv_anti_complex v
            rw [hn]
    _ = -sphereVerticalComplex (projectiveHopf p)
          (mfderiv (𝓡 2) (𝓡 2) G
            (coefficientSphereHomeomorph north)
            (mfderiv 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) H p₀ v)) := by
            rw [map_neg, hnat]
    _ = -sphereVerticalComplex (projectiveHopf p)
          (mfderiv 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) H p w) := by
            rw [← htarget v, hv]

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveAllFiberVerticalSign
