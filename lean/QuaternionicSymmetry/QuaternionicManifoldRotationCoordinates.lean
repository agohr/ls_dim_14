import QuaternionicSymmetry.QuaternionicManifoldPointwiseLifts
import QuaternionicSymmetry.QuaternionicNormalizerRotationAxes

/-! The fixed-model normalizer rotation is exactly the smooth rank-three
transition already derived from actual adapted tangent frames. -/

namespace QuaternionicSymmetry.QuaternionicManifoldRotationCoordinates

open VectorBundleFrameTransitions
  VectorBundleFrameTransitions.QuaternionicFrameReduction
  QuaternionicIsometryNormalizer QuaternionicUnitScalarIsometries
  QuaternionicManifoldFixedNormalizer QuaternionicManifoldPointwiseLifts
  QuaternionicNormalizerRotationAxes
open scoped ContDiff Manifold Quaternion

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

private theorem modelGauge_symm_conjugation_synth
    (T : QuaternionicStructure E) (a : Fin 3 → ℝ) :
    conjugation (modelGauge S T).symm (synth T a) = synth S a := by
  apply (conjugation (modelGauge S T)).injective
  rw [← conjugation_mul]
  have hmul : modelGauge S T * (modelGauge S T).symm = 1 := by
    change modelGauge S T * (modelGauge S T)⁻¹ = 1
    group
  rw [hmul, conjugation_one]
  exact (modelGauge_conjugation_synth S T a).symm

/-- Pointwise equality between the rotation extracted from the fixed-model
isometry and the rank-three coordinate transition of the actual reduction. -/
theorem rotationLinear_fixedTransition (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j)
    (a : Fin 3 → ℝ) :
    rotationLinear S (fixedTransitionNormalizer S Q i j x hi hj) a =
      Q.reduction.rankThreeCoordChange i j x a := by
  apply (show Function.Injective (synth S) from
    Function.LeftInverse.injective (coeff_synth S))
  rw [synth_rotationLinear]
  change conjugation (fixedTransition S Q i j x hi hj) (synth S a) =
    synth S (Q.reduction.rankThreeCoordChange i j x a)
  unfold fixedTransition
  rw [conjugation_mul, conjugation_mul,
    modelGauge_conjugation_synth]
  have hmid :
      conjugation (ManifoldQuaternionicUnitaryNormalizer.frameTransitionIsometry
        Q i j x hi hj) (synth (Q.reduction.Q i) a) =
      synth (Q.reduction.Q j)
        (Q.reduction.rankThreeCoordChange i j x a) := by
    ext v
    rw [conjugation_apply]
    have h := ManifoldQuaternionicUnitaryNormalizer.frameTransitionIsometry_adjoint
      Q i j x hi hj a
    rw [h]
    rfl
  rw [hmid, modelGauge_symm_conjugation_synth]

theorem firstAxis_fixedTransition (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j) :
    firstAxis S (fixedTransitionNormalizer S Q i j x hi hj) =
      pureScalar (Q.reduction.rankThreeCoordChange i j x
        (Pi.basisFun ℝ (Fin 3) 0)) := by
  exact congrArg pureScalar
    (rotationLinear_fixedTransition S Q i j x hi hj _)

theorem secondAxis_fixedTransition (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j) :
    secondAxis S (fixedTransitionNormalizer S Q i j x hi hj) =
      pureScalar (Q.reduction.rankThreeCoordChange i j x
        (Pi.basisFun ℝ (Fin 3) 1)) := by
  exact congrArg pureScalar
    (rotationLinear_fixedTransition S Q i j x hi hj _)

private def pureScalarLinear : (Fin 3 → ℝ) →ₗ[ℝ] ℍ where
  toFun := pureScalar
  map_add' a b := by
    ext <;> simp [pureScalar]
  map_smul' r a := by
    ext <;> simp [pureScalar]

def axisPair (i j : atlas E M) (x : M) : ℍ × ℍ :=
  (pureScalar (Q.reduction.rankThreeCoordChange i j x
      (Pi.basisFun ℝ (Fin 3) 0)),
   pureScalar (Q.reduction.rankThreeCoordChange i j x
      (Pi.basisFun ℝ (Fin 3) 1)))

theorem smooth_axisPair (i j : atlas E M) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℍ × ℍ) ∞ (axisPair Q i j)
      (Q.frames.adaptedCore.baseSet i ∩ Q.frames.adaptedCore.baseSet j) := by
  have h₀ := Q.smooth_rankThreeCoordChange_apply i j
    (Pi.basisFun ℝ (Fin 3) 0)
  have h₁ := Q.smooth_rankThreeCoordChange_apply i j
    (Pi.basisFun ℝ (Fin 3) 1)
  have hp₀ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℍ) ∞
      (fun x => pureScalar (Q.reduction.rankThreeCoordChange i j x
        (Pi.basisFun ℝ (Fin 3) 0)))
      (Q.frames.adaptedCore.baseSet i ∩ Q.frames.adaptedCore.baseSet j) := by
    exact pureScalarLinear.toContinuousLinearMap.contMDiff.comp_contMDiffOn h₀
  have hp₁ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℍ) ∞
      (fun x => pureScalar (Q.reduction.rankThreeCoordChange i j x
        (Pi.basisFun ℝ (Fin 3) 1)))
      (Q.frames.adaptedCore.baseSet i ∩ Q.frames.adaptedCore.baseSet j) := by
    exact pureScalarLinear.toContinuousLinearMap.contMDiff.comp_contMDiffOn h₁
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact hp₀.prodMk hp₁

end
end QuaternionicSymmetry.QuaternionicManifoldRotationCoordinates
