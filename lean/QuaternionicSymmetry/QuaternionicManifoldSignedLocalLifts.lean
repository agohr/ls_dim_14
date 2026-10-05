import QuaternionicSymmetry.QuaternionicManifoldSmoothProductLifts

/-! On refined triple overlaps, the explicitly smooth local product lifts
have central `±1` defect. This is the signed germ cocycle needed before a
projective gauge construction; no global lift on the old cover is assumed. -/

namespace QuaternionicSymmetry.QuaternionicManifoldSignedLocalLifts

open VectorBundleFrameTransitions
  QuaternionicManifoldPointwiseLifts
  QuaternionicManifoldLocalScalarLifts
  QuaternionicManifoldSmoothProductLifts
  QuaternionicUnitScalarIsometries
open scoped ContDiff Manifold Quaternion

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

def localProductLift (i j : atlas E M) (q : unitary ℍ)
    (y : M) (hy : y ∈ liftNeighborhood Q i j q) :
    QuaternionicIsometryNormalizer.symplecticKernel S × unitary ℍ :=
  (Classical.choose (exists_smooth_operator_factor S Q i j q y hy),
    scalarLiftUnit Q S i j q y hy)

theorem localProductLift_image (i j : atlas E M) (q : unitary ℍ)
    (y : M) (hy : y ∈ liftNeighborhood Q i j q) :
    symplecticProductAction S (localProductLift S Q i j q y hy) =
      fixedTransitionNormalizer S Q i j y hy.1.1 hy.1.2 :=
  (Classical.choose_spec (exists_smooth_operator_factor S Q i j q y hy)).2

theorem localProductLift_operator (i j : atlas E M) (q : unitary ℍ)
    (y : M) (hy : y ∈ liftNeighborhood Q i j q) :
    (localProductLift S Q i j q y hy).1.1.1.toContinuousLinearMap =
      symplecticFactorOperator S Q i j q y :=
  (Classical.choose_spec (exists_smooth_operator_factor S Q i j q y hy)).1

def tripleNeighborhood (i j k : atlas E M)
    (qij qjk qik : unitary ℍ) : Set M :=
  liftNeighborhood Q i j qij ∩
    liftNeighborhood Q j k qjk ∩
      liftNeighborhood Q i k qik

theorem isOpen_tripleNeighborhood (i j k : atlas E M)
    (qij qjk qik : unitary ℍ) :
    IsOpen (tripleNeighborhood Q i j k qij qjk qik) :=
  ((isOpen_liftNeighborhood Q i j qij).inter
    (isOpen_liftNeighborhood Q j k qjk)).inter
    (isOpen_liftNeighborhood Q i k qik)

/-- The triple-overlap defect of the locally smooth product lifts is the
central quaternionic sign, with its inverse convention fixed by the actual
adapted-frame cocycle. -/
theorem localProductLift_defect_sign (i j k : atlas E M)
    (qij qjk qik : unitary ℍ) (y : M)
    (hy : y ∈ tripleNeighborhood Q i j k qij qjk qik) :
    (((localProductLift S Q j k qjk y hy.1.2) *
      (localProductLift S Q i j qij y hy.1.1) *
      (localProductLift S Q i k qik y hy.2)⁻¹).2 : ℍ) = 1 ∨
    (((localProductLift S Q j k qjk y hy.1.2) *
      (localProductLift S Q i j qij y hy.1.1) *
      (localProductLift S Q i k qik y hy.2)⁻¹).2 : ℍ) = -1 := by
  let d := localProductLift S Q j k qjk y hy.1.2 *
    localProductLift S Q i j qij y hy.1.1 *
      (localProductLift S Q i k qik y hy.2)⁻¹
  have hd : symplecticProductAction S d = 1 := by
    dsimp [d]
    rw [map_mul, map_mul, map_inv,
      localProductLift_image, localProductLift_image,
      localProductLift_image,
      fixedTransition_cocycle]
    group
  exact symplecticProduct_kernel_sign S d hd

end
end QuaternionicSymmetry.QuaternionicManifoldSignedLocalLifts
