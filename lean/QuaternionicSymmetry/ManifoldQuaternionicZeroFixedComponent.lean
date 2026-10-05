import QuaternionicSymmetry.ManifoldQuaternionicFixedFiberFinite
import QuaternionicSymmetry.ManifoldQuaternionicFixedComponentTopology

/-! The zero-dimensional kernel fixed-component branch forces a connected
twistor torus fixed set with nonzero weight to be a point. Its base lies
in the actual component by connectedness, not by a supplied inclusion. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicZeroFixedComponent

open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicTorusAction
open ManifoldQuaternionicTwistorIsotropyWeight
open ManifoldQuaternionicVerticalWeightKernel ManifoldQuaternionicFixedFiberFinite
open ManifoldRiemannianFixedComponentInput ManifoldQuaternionicFixedComponentTopology
open ManifoldTwistorSphereCore ManifoldTwistorCoefficientSphere
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem fixedComponent_subsingleton_of_dimension_zero
    (S : Subgroup (QuaternionicIsometries Q)) (x : M)
    (C : FixedComponentAtlas Q S x 0) : Subsingleton (FixedComponent Q S x) := by
  letI := C.charts
  letI := preconnectedComponent Q S x
  letI : DiscreteTopology (FixedComponent Q S x) :=
    ChartedSpace.discreteTopology (EuclideanSpace ℝ (Fin 0)) (FixedComponent Q S x)
  exact PreconnectedSpace.trivial_of_discrete

variable {r : ℕ} (A : ContinuousTorusAction Q r)
  (z : SphereBundleTotal Q) (hz : ∀ t, A.representation t • z = z)

theorem fixed_set_base_in_connectedKernelComponent
    (μ : Fin r → ℤ) (Y : Set (SphereBundleTotal Q)) (hY : IsPreconnected Y)
    (hzY : z ∈ Y) (hfixed : ∀ w ∈ Y, ∀ t, A.representation t • w = w) :
    ∀ w ∈ Y, w.1 ∈ ContinuousTorusAction.connectedKernelFixedComponent Q A μ z.1 := by
  let π : SphereBundleTotal Q → M := fun w => w.1
  have hπ : Continuous π := (sphereCore Q).continuous_proj
  have himage : π '' Y ⊆ ContinuousTorusAction.connectedKernelFixedSet Q A μ := by
    rintro x ⟨w, hw, rfl⟩ f hf
    obtain ⟨t, _ht, rfl⟩ := hf
    exact isotropy_fixes_base Q w ⟨A.representation t, hfixed w hw t⟩
  have hsub := (hY.image π hπ.continuousOn).subset_connectedComponentIn
    (show z.1 ∈ π '' Y from ⟨z, hzY, rfl⟩) himage
  exact fun w hw => hsub ⟨w, hw, rfl⟩

theorem fixed_set_subsingleton_of_zero_component
    (μ : Fin r → ℤ) (hμ : μ ≠ 0)
    (hweight : HasVerticalWeight Q A z hz μ)
    (Y : Set (SphereBundleTotal Q)) (hY : IsPreconnected Y) (hzY : z ∈ Y)
    (hfixed : ∀ w ∈ Y, ∀ t, A.representation t • w = w)
    (C : FixedComponentAtlas Q
      (ContinuousTorusAction.connectedKernelImage Q A μ) z.1 0) :
    Y.Subsingleton := by
  let S := ContinuousTorusAction.connectedKernelImage Q A μ
  letI : Subsingleton (FixedComponent Q S z.1) :=
    fixedComponent_subsingleton_of_dimension_zero Q S z.1 C
  letI : T1Space (SphereBundleTotal Q) :=
    ((𝓘(ℝ,E)).prod (𝓡 2)).t1Space (SphereBundleTotal Q)
  apply connected_fixed_set_in_fiber_subsingleton Q A z hz μ hμ hweight Y hY ?_ hfixed
  intro w hw
  have hwN := fixed_set_base_in_connectedKernelComponent Q A z μ Y hY hzY hfixed w hw
  have hzN := mem_connectedComponentIn (base_mem_connectedKernelFixedSet Q A z hz μ)
  exact congrArg Subtype.val (Subsingleton.elim
    (⟨w.1,hwN⟩ : FixedComponent Q S z.1) ⟨z.1,hzN⟩)

/-- A nontrivial connected twistor fixed set with nonzero vertical weight
forces the actual quaternionic kernel fixed component to have positive,
strictly smaller dimension. Both inequalities are proved internally. -/
theorem exists_positive_smaller_fixedComponent
    [T2Space M] [SecondCountableTopology M] [PreconnectedSpace M]
    (hjet : ManifoldRiemannianOneJetInput.RiemannianOneJetRigidityOnModel
      (E := E) (M := M))
    (hfixedSource : RiemannianFixedComponentOnModel (E := E) (M := M))
    (hA : A.Faithful) (hr : 2 ≤ r)
    (μ : Fin r → ℤ) (hμ : μ ≠ 0)
    (hweight : HasVerticalWeight Q A z hz μ)
    (Y : Set (SphereBundleTotal Q)) (hY : IsPreconnected Y) (hzY : z ∈ Y)
    (hYnontrivial : Y.Nontrivial)
    (hfixed : ∀ w ∈ Y, ∀ t, A.representation t • w = w)
    (R : QuaternionicStructure E) :
    ∃ m : ℕ, 0 < m ∧ m < R.quaternionicDimension ∧
      Nonempty (FixedComponentAtlas Q
        (ContinuousTorusAction.connectedKernelImage Q A μ) z.1 (4*m)) := by
  obtain ⟨m, hm, ⟨C⟩⟩ := exists_smaller_fixedComponent_of_vertical_weight
    Q A z hz hjet hfixedSource hA hr μ hμ hweight R
  refine ⟨m, ?_, hm, ⟨C⟩⟩
  by_contra h
  have hmzero : m = 0 := by omega
  subst m
  have hsub := fixed_set_subsingleton_of_zero_component Q A z hz μ hμ hweight
    Y hY hzY hfixed C
  exact (Set.not_subsingleton_iff.mpr hYnontrivial) hsub

end
end QuaternionicSymmetry.ManifoldQuaternionicZeroFixedComponent
