import QuaternionicSymmetry.QuaternionicManifoldRotationCoordinates
import QuaternionicSymmetry.QuaternionicUnitQuaternionLocalRotationLift
import QuaternionicSymmetry.QuaternionicNormalizerExplicitFactor

/-! Actual adapted tangent frame overlaps admit smooth local `Sp(1)` scalar
lifts after refining each overlap around a point. -/

namespace QuaternionicSymmetry.QuaternionicManifoldLocalScalarLifts

open VectorBundleFrameTransitions
  QuaternionicManifoldPointwiseLifts QuaternionicManifoldRotationCoordinates
  QuaternionicNormalizerRotationAxes
  QuaternionicUnitQuaternionLocalRotationLift
  QuaternionicNormalizerExplicitFactor
open scoped ContDiff Manifold Quaternion

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

def overlap (i j : atlas E M) : Set M :=
  Q.frames.adaptedCore.baseSet i ∩ Q.frames.adaptedCore.baseSet j

def liftNeighborhood (i j : atlas E M) (q : unitary ℍ) : Set M :=
  overlap Q i j ∩ (axisPair Q i j) ⁻¹' localDomain q

def scalarLiftRaw (i j : atlas E M) (q : unitary ℍ) (x : M) : ℍ :=
  localLiftRaw q (axisPair Q i j x)

omit [Nontrivial E] [FiniteDimensional ℝ E] in
theorem isOpen_overlap (i j : atlas E M) : IsOpen (overlap Q i j) :=
  (Q.frames.adaptedCore.isOpen_baseSet i).inter
    (Q.frames.adaptedCore.isOpen_baseSet j)

theorem isOpen_liftNeighborhood (i j : atlas E M) (q : unitary ℍ) :
    IsOpen (liftNeighborhood Q i j q) :=
  (smooth_axisPair Q i j).continuousOn.isOpen_inter_preimage
    (isOpen_overlap Q i j) (isOpen_localDomain q)

theorem smooth_scalarLiftRaw (i j : atlas E M) (q : unitary ℍ) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℍ) ∞ (scalarLiftRaw Q i j q)
      (liftNeighborhood Q i j q) := by
  have haxis := (smooth_axisPair Q i j).mono
    (show liftNeighborhood Q i j q ⊆ overlap Q i j from Set.inter_subset_left)
  have hraw : ContMDiffOn 𝓘(ℝ, ℍ × ℍ) 𝓘(ℝ, ℍ) ∞
      (localLiftRaw q) (localDomain q) :=
    (contDiffOn_localLiftRaw q).contMDiffOn
  exact hraw.comp haxis (by intro x hx; exact hx.2)

theorem axisPair_valid (S : QuaternionicStructure E) (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j) :
    (axisPair Q i j x).1.re = 0 ∧
    (axisPair Q i j x).2.re = 0 ∧
    Quaternion.normSq (axisPair Q i j x).1 = 1 ∧
    Quaternion.normSq (axisPair Q i j x).2 = 1 ∧
    (axisPair Q i j x).1 * (axisPair Q i j x).2 =
      -(axisPair Q i j x).2 * (axisPair Q i j x).1 := by
  have h₁ := firstAxis_fixedTransition S Q i j x hi hj
  have h₂ := secondAxis_fixedTransition S Q i j x hi hj
  rw [show (axisPair Q i j x).1 =
    firstAxis S (fixedTransitionNormalizer S Q i j x hi hj) from h₁.symm,
    show (axisPair Q i j x).2 =
    secondAxis S (fixedTransitionNormalizer S Q i j x hi hj) from h₂.symm]
  exact ⟨firstAxis_re S _, secondAxis_re S _,
    firstAxis_normSq S _, secondAxis_normSq S _,
    axes_anticommute S _⟩

/-- Around every point of an actual adapted tangent overlap, a fixed
quaternion chart gives a smooth scalar factor of its normalizer transition.
The chart is local; no global choice on the original overlap is asserted. -/
theorem exists_local_scalar_lift (S : QuaternionicStructure E)
    (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j) :
    ∃ q : unitary ℍ,
      x ∈ liftNeighborhood Q i j q ∧
      IsOpen (liftNeighborhood Q i j q) ∧
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℍ) ∞
        (scalarLiftRaw Q i j q) (liftNeighborhood Q i j q) ∧
      ∀ y ∈ liftNeighborhood Q i j q,
        Quaternion.normSq (scalarLiftRaw Q i j q y) = 1 ∧
        scalarLiftRaw Q i j q y * QuaternionicUnitQuaternionTransport.basisI =
          (axisPair Q i j y).1 * scalarLiftRaw Q i j q y ∧
        scalarLiftRaw Q i j q y * QuaternionicUnitQuaternionTransport.basisJ =
          (axisPair Q i j y).2 * scalarLiftRaw Q i j q y := by
  obtain ⟨hu, hv, hnu, hnv, huv⟩ := axisPair_valid Q S i j x hi hj
  obtain ⟨q, hqx, _, _, _⟩ := exists_smooth_local_lift
    (axisPair Q i j x).1 (axisPair Q i j x).2 hu hv hnu hnv huv
  refine ⟨q, ⟨⟨hi, hj⟩, hqx⟩,
    isOpen_liftNeighborhood Q i j q,
    smooth_scalarLiftRaw Q i j q, ?_⟩
  intro y hy
  obtain ⟨hu', hv', hnu', hnv', huv'⟩ :=
    axisPair_valid Q S i j y hy.1.1 hy.1.2
  exact localLiftRaw_unit_and_intertwines q
    (axisPair Q i j y).1 (axisPair Q i j y).2
    hu' hv' hnu' hnv' huv' hy.2

theorem scalarLiftRaw_valid (S : QuaternionicStructure E)
    (i j : atlas E M) (q : unitary ℍ) (y : M)
    (hy : y ∈ liftNeighborhood Q i j q) :
    Quaternion.normSq (scalarLiftRaw Q i j q y) = 1 ∧
    scalarLiftRaw Q i j q y * QuaternionicUnitQuaternionTransport.basisI =
      (axisPair Q i j y).1 * scalarLiftRaw Q i j q y ∧
    scalarLiftRaw Q i j q y * QuaternionicUnitQuaternionTransport.basisJ =
      (axisPair Q i j y).2 * scalarLiftRaw Q i j q y := by
  obtain ⟨hu, hv, hnu, hnv, huv⟩ :=
    axisPair_valid Q S i j y hy.1.1 hy.1.2
  exact localLiftRaw_unit_and_intertwines q
    (axisPair Q i j y).1 (axisPair Q i j y).2
    hu hv hnu hnv huv hy.2

def scalarLiftUnit (S : QuaternionicStructure E)
    (i j : atlas E M) (q : unitary ℍ) (y : M)
    (hy : y ∈ liftNeighborhood Q i j q) : unitary ℍ :=
  QuaternionicUnitQuaternionTransport.ofNormSqOne
    (scalarLiftRaw Q i j q y) (scalarLiftRaw_valid Q S i j q y hy).1

/-- The local smooth scalar formula supplies an actual `Sp(n) × Sp(1)`
factor of every fixed-model transition on its refined overlap. -/
theorem local_product_factor (S : QuaternionicStructure E)
    (i j : atlas E M) (q : unitary ℍ) (y : M)
    (hy : y ∈ liftNeighborhood Q i j q) :
    ∃ h : QuaternionicIsometryNormalizer.symplecticKernel S,
      QuaternionicUnitScalarIsometries.symplecticProductAction S
        (h, scalarLiftUnit Q S i j q y hy) =
        fixedTransitionNormalizer S Q i j y hy.1.1 hy.1.2 := by
  let r : unitary ℍ := scalarLiftUnit Q S i j q y hy
  obtain ⟨_, hqi, hqj⟩ := scalarLiftRaw_valid Q S i j q y hy
  have hrI : (r : ℍ) * QuaternionicUnitQuaternionTransport.basisI =
      firstAxis S (fixedTransitionNormalizer S Q i j y hy.1.1 hy.1.2) * r := by
    change scalarLiftRaw Q i j q y * _ = _ * scalarLiftRaw Q i j q y
    rw [firstAxis_fixedTransition S Q i j y hy.1.1 hy.1.2]
    exact hqi
  have hrJ : (r : ℍ) * QuaternionicUnitQuaternionTransport.basisJ =
      secondAxis S (fixedTransitionNormalizer S Q i j y hy.1.1 hy.1.2) * r := by
    change scalarLiftRaw Q i j q y * _ = _ * scalarLiftRaw Q i j q y
    rw [secondAxis_fixedTransition S Q i j y hy.1.1 hy.1.2]
    exact hqj
  obtain ⟨h, hh⟩ := factor_of_axis_lift S
    (fixedTransitionNormalizer S Q i j y hy.1.1 hy.1.2) r hrI hrJ
  exact ⟨h, hh⟩

end
end QuaternionicSymmetry.QuaternionicManifoldLocalScalarLifts
