import QuaternionicSymmetry.FourDimensionalHalfSpinTwoSidedOrientation
import QuaternionicSymmetry.QuaternionicLeftLineAction
import QuaternionicSymmetry.QuaternionicNormalizerProductSurjective

/-! In a genuine quaternionic line, the quaternion-linear orthogonal kernel
is exactly right multiplication by a unit quaternion. Consequently the
checked normalizer product decomposition is literally two-sided on `ℍ`.
This does not yet identify the normalizer with all of `SO(4)`. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinNormalizerTwoSided

open scoped Quaternion
open QuaternionicIsometryNormalizer
  QuaternionicUnitScalarIsometries
  QuaternionicNormalizerProductSurjective
  QuaternionicLeftLineAction
  QuaternionicProjectiveStandardHilbertStructure
  FourDimensionalHalfSpinTwoSidedOrthogonal
  QuaternionicUnitQuaternionTransport

noncomputable section

private theorem normSq_one_of_norm_one (w : ℍ) (hw : ‖w‖ = 1) :
    Quaternion.normSq w = 1 := by
  rw [Quaternion.normSq_eq_norm_mul_self, hw]
  ring

/-- The `Sp(1)` kernel on the left quaternionic line is actual right
unit-quaternion multiplication. -/
theorem kernel_eq_right (h : symplecticKernel leftLineStructure) :
    ∃ r : unitary ℍ, h.1.1 = rightUnitIsometry r := by
  let w : ℍ := h.1.1 1
  have hw : ‖w‖ = 1 := by
    simp [w, h.1.1.norm_map]
  have hstar : Quaternion.normSq (star w) = 1 := by
    rw [Quaternion.normSq_star]
    exact normSq_one_of_norm_one w hw
  let r : unitary ℍ := ofNormSqOne (star w) hstar
  refine ⟨r, ?_⟩
  apply LinearIsometryEquiv.ext
  intro v
  obtain ⟨hI, hJ⟩ :=
    (mem_symplecticKernel_iff leftLineStructure h.1).mp h.2
  have hv := apply_eq_mul_one h.1.1.toLinearEquiv.toLinearMap hI hJ v
  change h.1.1 v = v * w at hv
  change h.1.1 v = v * star (star w)
  rw [star_star]
  exact hv

/-- Every genuine left-quaternionic normalizer element in real dimension
four has a literal two-sided unit-quaternion presentation. -/
theorem normalizer_eq_twoSided (g : normalizer leftLineStructure) :
    ∃ q r : unitary ℍ, g.1 = twoSidedIsometry q r := by
  obtain ⟨p, hp⟩ := symplecticProductAction_surjective leftLineStructure g
  obtain ⟨r, hr⟩ := kernel_eq_right p.1
  refine ⟨p.2, r, ?_⟩
  have hprod := congrArg Subtype.val hp
  change p.1.1.1 * (unitQuaternionNormalizerAction leftLineStructure p.2).1 =
    g.1 at hprod
  -- The product factors commute, so the scalar-left and kernel-right
  -- actions agree with the literal two-sided action.
  rw [← hprod]
  rw [hr]
  apply LinearIsometryEquiv.ext
  intro v
  simp [twoSidedIsometry_apply, rightUnitIsometry_apply,
    unitQuaternionNormalizerAction, unitQuaternionAction,
    unitScalarIsometry_apply, action_eq_mul, mul_assoc]

end
end QuaternionicSymmetry.FourDimensionalHalfSpinNormalizerTwoSided
