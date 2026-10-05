import QuaternionicSymmetry.ManifoldQuaternionicTorusHigherComponentAlternative
import QuaternionicSymmetry.ManifoldQuaternionicTorusFixedComplexComponent
import QuaternionicSymmetry.ManifoldQuaternionicZeroFixedComponent
import QuaternionicSymmetry.GeneralSmoothMapSource
import QuaternionicSymmetry.ManifoldTwistorVerticalLine
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! A literal torus-fixed twistor component over a kernel-fixed base component
has real dimension at most the base dimension plus the two-dimensional twistor
fiber. The proof differentiates the actual base projection and embedded
inclusions; it does not infer dimensions from finite fibers. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFixedComplexDimensionBound

open ManifoldQuaternionicTorusAction ManifoldQuaternionicTorusFixedComplexComponent
open ManifoldQuaternionicZeroFixedComponent ManifoldQuaternionicTwistorLiftedFixedSet
open ManifoldRiemannianFixedComponentInput ManifoldRiemannianFixedComponentGenericInput
open ManifoldQuaternionicTwistorComplexFixedAtlas
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorSphereCore ManifoldTwistorGlobalAlmostComplex
open QuaternionicSymmetry.GeneralSmoothMapSource
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
  {r : ℕ} (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (A : ContinuousTorusAction Q r) (z : SphereBundleTotal Q)
  (hz : ∀ t, A.representation t • z = z) (μ : Fin r → ℤ)

private abbrev Y := component Q A z
private abbrev N := FixedComponent Q (A.connectedKernelImage Q μ) z.1
private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)

/-- The actual base projection of the full-torus component factors through
the connected kernel fixed component. -/
def baseToKernel : ↥(Y Q A z) → N Q A z μ := by
  intro y
  have hzset : z ∈ fixedSpherePoints Q A.imageSubgroup :=
    (mem_fixedSpherePoints_iff_torus Q A z).mpr hz
  have hfixed : ∀ w ∈ Y Q A z, ∀ t, A.representation t • w = w := by
    intro w hw
    exact (mem_fixedSpherePoints_iff_torus Q A w).mp
      (connectedComponentIn_subset _ _ hw)
  exact ⟨y.1.1, fixed_set_base_in_connectedKernelComponent Q A z μ
    (Y Q A z) isPreconnected_connectedComponentIn
    (mem_connectedComponentIn hzset) hfixed y.1 y.2⟩

include hz in
/-- The real dimension bound is certified by an injective differential into
the base tangent plus the vertical two-plane. -/
theorem real_dimension_le_base_plus_two
    {k m : ℕ}
    (H : FixedComponentAtlas (J (E := E))
      (liftedSet Q A.imageSubgroup) z k)
    (C : FixedComponentAtlas Q (A.connectedKernelImage Q μ) z.1 (4*m))
    (hLee : LeeEmbeddedCodomainRestrictionTheorem) :
    k ≤ 4*m + 2 := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin k)) (↥(Y Q A z)) := H.charts
  letI : IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) ∞ (↥(Y Q A z)) := H.manifold
  letI : ChartedSpace (EuclideanSpace ℝ (Fin (4*m))) (N Q A z μ) := C.charts
  letI : IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (4*m))) ∞ (N Q A z μ) := C.manifold
  let f := baseToKernel Q A z hz μ
  have hcomp : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) 𝓘(ℝ,E) ∞
      ((Subtype.val : N Q A z μ → M) ∘ f) := by
    convert (ManifoldTwistorSphereManifold.sphereProjection_smooth Q).comp
      H.inclusion_smooth using 1
  have hf : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin k))
      𝓘(ℝ,EuclideanSpace ℝ (Fin (4*m))) ∞ f :=
    hLee Subtype.val f Topology.IsEmbedding.subtypeVal
      C.inclusion_smooth C.inclusion_injective_derivative hcomp
  have hiY : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) (J (E := E)) ∞
      (Subtype.val : ↥(Y Q A z) → SphereBundleTotal Q) := H.inclusion_smooth
  let y : ↥(Y Q A z) := ⟨z, mem_connectedComponentIn
    ((mem_fixedSpherePoints_iff_torus Q A z).mpr hz)⟩
  let D : EuclideanSpace ℝ (Fin k) →L[ℝ]
      (EuclideanSpace ℝ (Fin (4*m))) × EuclideanSpace ℝ (Fin 2) :=
    (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k))
      𝓘(ℝ,EuclideanSpace ℝ (Fin (4*m))) f y).prod
      ((ContinuousLinearMap.snd ℝ E (EuclideanSpace ℝ (Fin 2))).comp
        (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) (J (E := E))
          (Subtype.val : ↥(Y Q A z) → SphereBundleTotal Q) y))
  have hdiff : (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin (4*m))) 𝓘(ℝ,E)
      (Subtype.val : N Q A z μ → M) (f y)).comp
      (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k))
        𝓘(ℝ,EuclideanSpace ℝ (Fin (4*m))) f y) =
      (ContinuousLinearMap.fst ℝ E (EuclideanSpace ℝ (Fin 2))).comp
      (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) (J (E := E))
        (Subtype.val : ↥(Y Q A z) → SphereBundleTotal Q) y) := by
    have h₁ := mfderiv_comp y
      (C.inclusion_smooth.mdifferentiableAt (by simp))
      (hf.mdifferentiableAt (by simp))
    have h₂ := mfderiv_comp y
      ((ManifoldTwistorSphereManifold.sphereProjection_smooth Q).contMDiffAt.mdifferentiableAt (by simp))
      (hiY.mdifferentiableAt (by simp))
    rw [sphereProjection_mfderiv Q y.1] at h₂
    convert h₁.symm.trans h₂ using 1
  have hD : Function.Injective D := by
    intro u v huv
    have hbase : (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k))
      𝓘(ℝ,EuclideanSpace ℝ (Fin (4*m))) f y) u =
      (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k))
      𝓘(ℝ,EuclideanSpace ℝ (Fin (4*m))) f y) v := by
      simpa only [D, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply]
        using congrArg Prod.fst huv
    have hvert : (ContinuousLinearMap.snd ℝ E (EuclideanSpace ℝ (Fin 2)))
        ((mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) (J (E := E))
          (Subtype.val : ↥(Y Q A z) → SphereBundleTotal Q) y) u) =
        (ContinuousLinearMap.snd ℝ E (EuclideanSpace ℝ (Fin 2)))
        ((mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) (J (E := E))
          (Subtype.val : ↥(Y Q A z) → SphereBundleTotal Q) y) v) := by
      simpa only [D, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply]
        using congrArg Prod.snd huv
    apply H.inclusion_injective_derivative y
    apply Prod.ext
    · have h := congrArg (fun t =>
        (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin (4*m)))
          𝓘(ℝ,E) (Subtype.val : N Q A z μ → M) (f y)) t) hbase
      change ((mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin (4*m))) 𝓘(ℝ,E)
        (Subtype.val : N Q A z μ → M) (f y)).comp
        (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k))
          𝓘(ℝ,EuclideanSpace ℝ (Fin (4*m))) f y)) u =
        ((mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin (4*m))) 𝓘(ℝ,E)
          (Subtype.val : N Q A z μ → M) (f y)).comp
          (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k))
            𝓘(ℝ,EuclideanSpace ℝ (Fin (4*m))) f y)) v at h
      rw [hdiff] at h
      exact h
    · exact hvert
  have hdim := LinearMap.finrank_le_finrank_of_injective hD
  simpa using hdim

include hz in
/-- The actual compatible complex fixed atlas has dimension at most
`2m+1` when the kernel-fixed base component has real dimension `4m`. -/
theorem complex_dimension_le_two_mul_add_one
    {k m b n : ℕ}
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    (A₀ : CompatibleComplexAtlas Q D n)
    (H : FixedComponentAtlas (J (E := E))
      (liftedSet Q A.imageSubgroup) z k)
    (B : letI := A₀.charts
      ComplexSubmanifoldInput.CompatibleComplexAtlas
        (realEmbeddedAtlas Q D A₀ A.imageSubgroup H) b)
    (C : FixedComponentAtlas Q (A.connectedKernelImage Q μ) z.1 (4*m))
    (hLee : LeeEmbeddedCodomainRestrictionTheorem) :
    b ≤ 2*m + 1 := by
  letI := A₀.charts
  have hzset : z ∈ fixedSpherePoints Q A.imageSubgroup :=
    (mem_fixedSpherePoints_iff_torus Q A z).mpr hz
  have hdim : k = 2*b := B.real_dimension_eq_twice
    (realEmbeddedAtlas Q D A₀ A.imageSubgroup H)
    ⟨z, mem_connectedComponentIn hzset⟩
  have hreal := real_dimension_le_base_plus_two Q A z hz μ H C hLee
  omega

include hz in
/-- In the four-real-dimensional kernel branch the literal full-torus
fixed component has complex dimension at most three. No positive
four-dimensional geometry or twistor classification is assumed. -/
theorem complex_dimension_le_three_of_four_base
    {k b n : ℕ}
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    (A₀ : CompatibleComplexAtlas Q D n)
    (H : FixedComponentAtlas (J (E := E))
      (liftedSet Q A.imageSubgroup) z k)
    (B : letI := A₀.charts
      ComplexSubmanifoldInput.CompatibleComplexAtlas
        (realEmbeddedAtlas Q D A₀ A.imageSubgroup H) b)
    (C : FixedComponentAtlas Q (A.connectedKernelImage Q μ) z.1 4)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem) :
    b ≤ 3 := by
  have h := complex_dimension_le_two_mul_add_one Q A z hz μ D A₀ H B
    (m := 1) (by simpa using C) hLee
  simpa using h

end
end QuaternionicSymmetry.ManifoldQuaternionicFixedComplexDimensionBound
