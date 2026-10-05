import QuaternionicSymmetry.QuaternionicManifoldFixedNormalizer

/-! Pointwise `Sp(n) × Sp(1)` factors of actual adapted tangent transitions,
with the central sign of their triple-overlap defect. -/

namespace QuaternionicSymmetry.QuaternionicManifoldPointwiseLifts

open VectorBundleFrameTransitions ManifoldQuaternionicUnitaryNormalizer
  QuaternionicIsometryNormalizer QuaternionicUnitScalarIsometries
  QuaternionicNormalizerProductSurjective QuaternionicManifoldFixedNormalizer
open scoped ContDiff Manifold Quaternion

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

def fixedTransitionNormalizer (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j) : normalizer S :=
  ⟨fixedTransition S Q i j x hi hj,
    fixedTransition_mem_normalizer S Q i j x hi hj⟩

theorem fixedTransition_cocycle (i j k : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j)
    (hk : x ∈ Q.frames.adaptedCore.baseSet k) :
    fixedTransitionNormalizer S Q j k x hj hk *
      fixedTransitionNormalizer S Q i j x hi hj =
        fixedTransitionNormalizer S Q i k x hi hk := by
  apply Subtype.ext
  change fixedTransition S Q j k x hj hk *
    fixedTransition S Q i j x hi hj =
      fixedTransition S Q i k x hi hk
  have hg : frameTransitionIsometry Q j k x hj hk *
      frameTransitionIsometry Q i j x hi hj =
        frameTransitionIsometry Q i k x hi hk := by
    change (frameTransitionIsometry Q i j x hi hj).trans
      (frameTransitionIsometry Q j k x hj hk) =
        frameTransitionIsometry Q i k x hi hk
    exact frameTransitionIsometry_comp Q i j k x hi hj hk
  unfold fixedTransition
  calc
    _ = (modelGauge S (Q.reduction.Q k)).symm *
        (frameTransitionIsometry Q j k x hj hk *
          frameTransitionIsometry Q i j x hi hj) *
          modelGauge S (Q.reduction.Q i) := by
          change (modelGauge S (Q.reduction.Q k))⁻¹ *
            frameTransitionIsometry Q j k x hj hk *
              modelGauge S (Q.reduction.Q j) *
                (modelGauge S (Q.reduction.Q j))⁻¹ *
                  frameTransitionIsometry Q i j x hi hj *
                    modelGauge S (Q.reduction.Q i) =
            (modelGauge S (Q.reduction.Q k))⁻¹ *
              (frameTransitionIsometry Q j k x hj hk *
                frameTransitionIsometry Q i j x hi hj) *
                modelGauge S (Q.reduction.Q i)
          group
    _ = _ := by rw [hg]

/-- A pointwise product lift selected from the proved surjectivity theorem.
No continuity is asserted for this choice. -/
def chosenLift (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j) :
    symplecticKernel S × unitary ℍ :=
  Classical.choose (symplecticProductAction_surjective S
    (fixedTransitionNormalizer S Q i j x hi hj))

theorem chosenLift_image (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j) :
    symplecticProductAction S (chosenLift S Q i j x hi hj) =
      fixedTransitionNormalizer S Q i j x hi hj :=
  Classical.choose_spec (symplecticProductAction_surjective S
    (fixedTransitionNormalizer S Q i j x hi hj))

/-- The product-lift defect on a triple overlap has central quaternionic
scalar `+1` or `-1`. This is the pointwise signed cocycle precursor. -/
theorem chosenLift_defect_sign (i j k : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j)
    (hk : x ∈ Q.frames.adaptedCore.baseSet k) :
    (((chosenLift S Q j k x hj hk) *
      (chosenLift S Q i j x hi hj) *
      (chosenLift S Q i k x hi hk)⁻¹).2 : ℍ) = 1 ∨
    (((chosenLift S Q j k x hj hk) *
      (chosenLift S Q i j x hi hj) *
      (chosenLift S Q i k x hi hk)⁻¹).2 : ℍ) = -1 := by
  let d := chosenLift S Q j k x hj hk *
    chosenLift S Q i j x hi hj *
      (chosenLift S Q i k x hi hk)⁻¹
  have hd : symplecticProductAction S d = 1 := by
    dsimp [d]
    rw [map_mul, map_mul, map_inv,
      chosenLift_image, chosenLift_image, chosenLift_image,
      fixedTransition_cocycle]
    group
  exact symplecticProduct_kernel_sign S d hd

end
end QuaternionicSymmetry.QuaternionicManifoldPointwiseLifts
