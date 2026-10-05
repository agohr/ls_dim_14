import QuaternionicSymmetry.FourDimensionalHalfSpinNormalizerImage
import QuaternionicSymmetry.QuaternionicManifoldPointwiseLifts

/-! Literal projective half-spin transitions for the actual adapted tangent
atlas in quaternionic-line dimension. Their cocycle and Hopf comparison are
checked against the existing fixed-model normalizer transitions. The
pointwise transition formula is not yet a smooth projective bundle atlas. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinActualTransition

open scoped ContDiff Manifold Quaternion
open VectorBundleFrameTransitions
  QuaternionicManifoldPointwiseLifts
  QuaternionicProjectiveStandardHilbertStructure
  FourDimensionalHalfSpinNormalizerAction
  FourDimensionalHalfSpinNormalizerTwoSided
  FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinHopfProjectiveDescent
  FourDimensionalTwistorNormalizerQuotient

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

def spinorTransition (i j : atlas ℍ M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j)
    (p : ProjectiveSpinor) : ProjectiveSpinor :=
  projectiveNormalizerAction leftLineStructure
    (fixedTransitionNormalizer leftLineStructure Q i j x hi hj) p

/-- Every actual fixed-model transition has two literal quaternionic
factors; no arbitrary `SO(4)` identification is invoked. -/
theorem actualTransition_twoSided (i j : atlas ℍ M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j) :
    ∃ q r : unitary ℍ,
      (fixedTransitionNormalizer leftLineStructure Q i j x hi hj).1 =
        FourDimensionalHalfSpinTwoSidedOrthogonal.twoSidedIsometry q r :=
  normalizer_eq_twoSided _

theorem spinorTransition_hopf (i j : atlas ℍ M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j)
    (p : ProjectiveSpinor) :
    projectiveHopf (spinorTransition Q i j x hi hj p) =
      FourDimensionalTwistorNormalizerQuotient.act leftLineStructure
        (fixedTransitionNormalizer leftLineStructure Q i j x hi hj)
        (projectiveHopf p) :=
  projectiveHopf_normalizerAction leftLineStructure _ p

/-- The true projective-matrix transitions satisfy the exact triple-overlap
cocycle, including the central sign cancellation. -/
theorem spinorTransition_cocycle (i j k : atlas ℍ M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j)
    (hk : x ∈ Q.frames.adaptedCore.baseSet k)
    (p : ProjectiveSpinor) :
    spinorTransition Q j k x hj hk (spinorTransition Q i j x hi hj p) =
      spinorTransition Q i k x hi hk p := by
  change (fixedTransitionNormalizer leftLineStructure Q j k x hj hk) •
      ((fixedTransitionNormalizer leftLineStructure Q i j x hi hj) • p) =
    (fixedTransitionNormalizer leftLineStructure Q i k x hi hk) • p
  rw [← mul_smul, fixedTransition_cocycle]

end
end QuaternionicSymmetry.FourDimensionalHalfSpinActualTransition
