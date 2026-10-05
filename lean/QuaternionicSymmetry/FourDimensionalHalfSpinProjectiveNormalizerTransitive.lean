import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFiberChartOverlap
import QuaternionicSymmetry.FourDimensionalHalfSpinNormalizerHolomorphic
import QuaternionicSymmetry.FourDimensionalHalfSpinHopfChartFormula
import QuaternionicSymmetry.FourDimensionalTwistorHomogeneousFiber

/-! The checked normalizer action is transitive on the actual CP¹
half-spin fiber.  This uses the independently proved Hopf bijection and
normalizer action, not a global spin lift. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveNormalizerTransitive

open scoped Quaternion Matrix
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinProjectiveMobiusAction
  FourDimensionalHalfSpinHopfProjectiveDescent
  FourDimensionalHalfSpinHopfChartFormula
  FourDimensionalHalfSpinHopfSphere
  FourDimensionalHalfSpinHopfInjective
  FourDimensionalHalfSpinNormalizerAction
  FourDimensionalTwistorNormalizerQuotient
  FourDimensionalTwistorHomogeneousFiber
  QuaternionicIsometryNormalizer
  ManifoldTwistorSphereBundle

noncomputable section

theorem projectiveHopf_affineZero :
    projectiveHopf (affineSpinorPoint 0) = north := by
  unfold affineSpinorPoint
  rw [projectiveHopf_mk]
  apply Subtype.ext
  change (hopfSphere (affineZeroSpinor 0) (affineZero_nonzero 0)).1 = north.1
  rw [affineZero_hopfCoefficients]
  ext i
  fin_cases i <;>
    simp [north, Pi.basisFun_apply]

theorem normalizer_transitive {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Nontrivial E] [FiniteDimensional ℝ E]
    (S : QuaternionicStructure E) (p : ProjectiveSpinor) :
    ∃ g : normalizer S,
      projectiveNormalizerAction S g (affineSpinorPoint 0) = p := by
  obtain ⟨g, hg⟩ := exists_normalizer_maps_north S (projectiveHopf p)
  refine ⟨g, projectiveHopf_injective ?_⟩
  rw [projectiveHopf_normalizerAction,
    projectiveHopf_affineZero]
  apply Subtype.ext
  exact hg

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveNormalizerTransitive
