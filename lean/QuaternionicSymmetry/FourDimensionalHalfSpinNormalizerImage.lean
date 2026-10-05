import QuaternionicSymmetry.FourDimensionalHalfSpinNormalizerTwoSided
import QuaternionicSymmetry.FourDimensionalHalfSpinOrthogonalImageAction

/-! Exact identification of the concrete two-sided quaternionic image with
the fixed left-quaternionic normalizer in real dimension four. This is a
structure-group identification, not yet a proof that it is all `SO(4)`. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinNormalizerImage

open scoped Quaternion
open QuaternionicIsometryNormalizer
  QuaternionicUnitScalarIsometries
  QuaternionicProjectiveStandardHilbertStructure
  QuaternionicLeftLineAction
  QuaternionicUnitQuaternionTransport
  FourDimensionalHalfSpinTwoSidedOrthogonal
  FourDimensionalHalfSpinNormalizerTwoSided
  FourDimensionalHalfSpinOrthogonalImageAction
  VectorBundleFrameTransitions
  VectorBundleFrameTransitions.QuaternionicFrameReduction

noncomputable section

private theorem right_commutes_action (r : unitary ℍ) (q v : ℍ) :
    rightUnitIsometry r (leftLineStructure.action q v) =
      leftLineStructure.action q (rightUnitIsometry r v) := by
  simp [action_eq_mul, rightUnitIsometry_apply, mul_assoc]

private theorem right_conjugation_synth (r : unitary ℍ) (a : Fin 3 → ℝ) :
    conjugation (rightUnitIsometry r) (synth leftLineStructure a) =
      synth leftLineStructure a := by
  apply ContinuousLinearMap.ext
  intro v
  rw [conjugation_apply]
  rw [← action_pureScalar leftLineStructure a,
    ← action_pureScalar leftLineStructure a]
  rw [right_commutes_action]
  simp

theorem rightUnitIsometry_mem_normalizer (r : unitary ℍ) :
    rightUnitIsometry r ∈ normalizer leftLineStructure := by
  let T := conjugation (rightUnitIsometry r)
  have hfix (A : ℍ →L[ℝ] ℍ) (hA : A ∈ quaternionicSpan leftLineStructure) :
      T A = A := by
    calc
      T A = T (synth leftLineStructure (coeff leftLineStructure A)) := by
        rw [synth_coeff_of_mem leftLineStructure A hA]
      _ = synth leftLineStructure (coeff leftLineStructure A) :=
        right_conjugation_synth r _
      _ = A := synth_coeff_of_mem leftLineStructure A hA
  intro A
  constructor
  · intro hA
    rw [hfix A hA]
    exact hA
  · intro hA
    have heq : T A = A := by
      apply T.injective
      exact hfix (T A) hA
    rw [heq] at hA
    exact hA

theorem twoSidedIsometry_mem_normalizer (q r : unitary ℍ) :
    twoSidedIsometry q r ∈ normalizer leftLineStructure := by
  change leftUnitIsometry q * rightUnitIsometry r ∈
    normalizer leftLineStructure
  exact Subgroup.mul_mem _
    (show leftUnitIsometry q ∈ normalizer leftLineStructure from by
      have heq : leftUnitIsometry q =
          unitScalarIsometry leftLineStructure (q : ℍ)
            (normSq_one_of_unitary q) := by
        apply LinearIsometryEquiv.ext
        intro v
        rw [leftUnitIsometry_apply, unitScalarIsometry_apply, action_eq_mul]
      rw [heq]
      exact unitScalar_mem_normalizer leftLineStructure (q : ℍ)
        (normSq_one_of_unitary q))
    (rightUnitIsometry_mem_normalizer r)

theorem orthogonalImage_eq_normalizer :
    orthogonalImage = normalizer leftLineStructure := by
  ext g
  constructor
  · rintro ⟨⟨q,r⟩, rfl⟩
    exact twoSidedIsometry_mem_normalizer q r
  · intro hg
    obtain ⟨q,r,hqr⟩ := normalizer_eq_twoSided ⟨g,hg⟩
    exact ⟨(q,r), hqr.symm⟩

end
end QuaternionicSymmetry.FourDimensionalHalfSpinNormalizerImage
