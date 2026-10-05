import QuaternionicSymmetry.FourDimensionalHalfSpinHopfChartFormula
import QuaternionicSymmetry.QuaternionicNormalizerProductSurjective

/-! The actual quaternionic orthogonal normalizer acts on true projective
spinor lines by the explicit half-spin matrix of its unit-quaternion factor.
The factor exists by the checked product decomposition; projective
independence and the action law follow from literal Hopf equivariance and
injectivity, not from a transported definition. This is still a normalizer
representation, pending the separate `SO(4)` identification. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinNormalizerAction

open scoped Quaternion
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open QuaternionicIsometryNormalizer
  QuaternionicUnitScalarIsometries
  QuaternionicNormalizerProductSurjective
  FourDimensionalTwistorNormalizerQuotient
  FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinHopfProjectiveDescent
  FourDimensionalHalfSpinHopfInjective
  FourDimensionalHalfSpinHopfAction
open ManifoldTwistorSphereBundle

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  (S : QuaternionicStructure E)

def productLift (g : normalizer S) :
    symplecticKernel S × unitary ℍ :=
  Classical.choose (symplecticProductAction_surjective S g)

theorem productLift_spec (g : normalizer S) :
    symplecticProductAction S (productLift S g) = g :=
  Classical.choose_spec (symplecticProductAction_surjective S g)

private theorem kernel_act_id (h : symplecticKernel S)
    (a : coefficientSphere) : act S h.1 a = a := by
  have hh : rotationEquiv S h.1 = LinearEquiv.refl ℝ (Fin 3 → ℝ) :=
    (rotation_kernel_iff_commutes S h.1).2
      ((mem_symplecticKernel_iff S h.1).1 h.2)
  apply Subtype.ext
  change rotationEquiv S h.1 a.1 = a.1
  rw [hh]
  rfl

private theorem product_act (h : symplecticKernel S) (q : unitary ℍ)
    (a : coefficientSphere) :
    act S (symplecticProductAction S (h,q)) a =
      act S (unitQuaternionNormalizerAction S q) a := by
  apply Subtype.ext
  change rotationLinear S
      (h.1 * unitQuaternionNormalizerAction S q) a.1 =
    rotationLinear S (unitQuaternionNormalizerAction S q) a.1
  rw [rotationLinear_mul]
  have hh := congrArg Subtype.val
    (kernel_act_id S h (act S (unitQuaternionNormalizerAction S q) a))
  exact hh

/-- The normalizer action uses an actual checked unit-quaternion factor
and its literal complex 2×2 projective matrix. -/
def projectiveNormalizerAction (g : normalizer S)
    (p : ProjectiveSpinor) : ProjectiveSpinor :=
  projectiveHalfSpin (productLift S g).2 p

theorem projectiveHopf_normalizerAction (g : normalizer S)
    (p : ProjectiveSpinor) :
    projectiveHopf (projectiveNormalizerAction S g p) =
      act S g (projectiveHopf p) := by
  unfold projectiveNormalizerAction
  rw [projectiveHopf_action S]
  let h := productLift S g
  change act S (unitQuaternionNormalizerAction S h.2) (projectiveHopf p) =
    act S g (projectiveHopf p)
  rw [← productLift_spec S g]
  exact (product_act S h.1 h.2 (projectiveHopf p)).symm

/-- Two checked product lifts of the same normalizer element induce the
same true projective half-spin map. -/
theorem projective_factor_independent
    (h k : symplecticKernel S × unitary ℍ)
    (hg : symplecticProductAction S h =
      symplecticProductAction S k) (p : ProjectiveSpinor) :
    projectiveHalfSpin h.2 p = projectiveHalfSpin k.2 p := by
  apply projectiveHopf_injective
  rw [projectiveHopf_action S, projectiveHopf_action S]
  rw [← product_act S h.1 h.2 (projectiveHopf p),
    ← product_act S k.1 k.2 (projectiveHopf p), hg]

instance : MulAction (normalizer S) ProjectiveSpinor where
  smul := projectiveNormalizerAction S
  one_smul p := by
    apply projectiveHopf_injective
    change projectiveHopf (projectiveNormalizerAction S 1 p) = projectiveHopf p
    rw [projectiveHopf_normalizerAction]
    exact one_smul (M := normalizer S) (projectiveHopf p)
  mul_smul g h p := by
    apply projectiveHopf_injective
    change projectiveHopf (projectiveNormalizerAction S (g*h) p) =
      projectiveHopf (projectiveNormalizerAction S g
        (projectiveNormalizerAction S h p))
    rw [projectiveHopf_normalizerAction,
      projectiveHopf_normalizerAction,
      projectiveHopf_normalizerAction]
    exact mul_smul g h (projectiveHopf p)

end
end QuaternionicSymmetry.FourDimensionalHalfSpinNormalizerAction
