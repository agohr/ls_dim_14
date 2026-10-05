import QuaternionicSymmetry.FourDimensionalHalfSpinNormalizerAction
import QuaternionicSymmetry.ComplexProjectiveLinearEquivHolomorphic
import QuaternionicSymmetry.ManifoldComplexHolomorphicFactorization

/-! Every fixed element of the actual quaternionic orthogonal normalizer
acts holomorphically on the genuine local projective half-spin line. The
map is the literal complex projectivization of its unit-quaternion matrix
factor, independent of which checked product lift is selected. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinNormalizerHolomorphic

open scoped Manifold ContDiff
open QuaternionicIsometryNormalizer
  FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinNormalizerAction
  ComplexProjectiveLinearEquivHolomorphic
  ManifoldComplexHolomorphicFactorization

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  (S : QuaternionicStructure E)

theorem projectiveNormalizerAction_holomorphic (g : normalizer S) :
    ContMDiff 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ, Fin 1 → ℂ) ∞
      (projectiveNormalizerAction S g) := by
  change ContMDiff 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ, Fin 1 → ℂ) ∞
      (projectiveMap (halfSpinLinearEquiv
        (FourDimensionalHalfSpinNormalizerAction.productLift S g).2))
  exact contMDiff_projectiveMap _

theorem projectiveNormalizerAction_realSmooth (g : normalizer S) :
    ContMDiff 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, Fin 1 → ℂ) ∞
      (projectiveNormalizerAction S g) :=
  holomorphic_is_real_smooth
    (projectiveNormalizerAction_holomorphic S g)

end
end QuaternionicSymmetry.FourDimensionalHalfSpinNormalizerHolomorphic
