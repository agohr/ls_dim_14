import QuaternionicSymmetry.FourDimensionalHalfSpinActualTransition
import QuaternionicSymmetry.FourDimensionalHalfSpinCliffordCovariance

/-! The genuine adapted tangent transition and genuine projective-spinor
transition use one and the same left unit-quaternion factor. The
complementary right factor is the target chirality in the checked
Clifford equivariance law. This is pointwise; smooth local factors are
handled separately. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinActualCliffordTransition

open scoped ContDiff Manifold Quaternion
open QuaternionicIsometryNormalizer
  QuaternionicUnitScalarIsometries
  QuaternionicProjectiveStandardHilbertStructure
  QuaternionicLeftLineAction
  FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinNormalizerAction
  FourDimensionalHalfSpinNormalizerTwoSided
  FourDimensionalHalfSpinTwoSidedOrthogonal
  FourDimensionalHalfSpinActualTransition
  FourDimensionalHalfSpinCliffordActual
  FourDimensionalHalfSpinCliffordCovariance
  QuaternionicManifoldPointwiseLifts

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

theorem actualTransition_clifford_factors (i j : atlas ℍ M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j) :
    ∃ q r : unitary ℍ,
      (fixedTransitionNormalizer leftLineStructure Q i j x hi hj).1 =
        twoSidedIsometry q r ∧
      (∀ p : ProjectiveSpinor,
        spinorTransition Q i j x hi hj p = projectiveHalfSpin q p) ∧
      (∀ u : ℍ, ∀ v : Spinor,
        cliffordMultiply
          ((fixedTransitionNormalizer leftLineStructure Q i j x hi hj).1 u)
          (halfSpinLinearEquiv q v) =
        halfSpinLinearEquiv r (cliffordMultiply u v)) := by
  let g := fixedTransitionNormalizer leftLineStructure Q i j x hi hj
  let h := productLift leftLineStructure g
  obtain ⟨r,hr⟩ := kernel_eq_right h.1
  let q := h.2
  have hg : h.1.1 * unitQuaternionNormalizerAction leftLineStructure q = g :=
    productLift_spec leftLineStructure g
  have hreal : g.1 = twoSidedIsometry q r := by
    have hprod := congrArg Subtype.val hg
    change h.1.1 * (unitQuaternionNormalizerAction leftLineStructure q).1 = g.1 at hprod
    rw [← hprod, hr]
    apply LinearIsometryEquiv.ext
    intro u
    simp [twoSidedIsometry_apply, rightUnitIsometry_apply,
      unitQuaternionNormalizerAction, unitQuaternionAction,
      unitScalarIsometry_apply, action_eq_mul, mul_assoc]
  refine ⟨q, r, hreal, ?_, ?_⟩
  · intro p
    rfl
  · intro u v
    rw [hreal, twoSidedIsometry_apply]
    exact cliffordMultiply_twoSided q r u v

end
end QuaternionicSymmetry.FourDimensionalHalfSpinActualCliffordTransition
