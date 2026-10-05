import QuaternionicSymmetry.ManifoldRiemannianFixedComponentInput
import QuaternionicSymmetry.ManifoldQuaternionicKernelCompactness

/-! Strict dimension drop for the actual fixed-component submanifold,
relative only to the precisely registered general Riemannian one-jet and
fixed-submanifold sources. Quaternionic divisibility and positive induced
curvature are not assumed or concluded by this packet. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFixedComponentDimension

open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicFixedTangentDimension
open ManifoldRiemannianOneJetInput ManifoldRiemannianFixedComponentInput
open ManifoldQuaternionicTorusAction QuaternionicTorusWeightKernel
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem atlas_dimension_eq_fixedTangent_finrank
    (S : Subgroup (QuaternionicIsometries Q)) (x : M) {k : ℕ}
    (C : FixedComponentAtlas Q S x k) (y : FixedComponent Q S x) :
    k = Module.finrank ℝ
      (fixedTangentSpace Q S y.1 (connectedComponentIn_subset _ _ y.2)) := by
  letI := C.charts
  have h := LinearMap.finrank_range_of_inj
    (f := (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) 𝓘(ℝ,E)
      (Subtype.val : FixedComponent Q S x → M) y).toLinearMap)
    (C.inclusion_injective_derivative y)
  rw [C.tangent_eq y] at h
  simpa only [TangentSpace, finrank_euclideanSpace_fin] using h.symm

theorem atlas_dimension_lt [T2Space M] [SecondCountableTopology M]
    [PreconnectedSpace M]
    (hjet : RiemannianOneJetRigidityOnModel (E := E) (M := M))
    (S : Subgroup (QuaternionicIsometries Q)) (hS : ∃ f ∈ S, f ≠ 1)
    (x : M) (hx : x ∈ fixedPoints Q S) {k : ℕ}
    (C : FixedComponentAtlas Q S x k) : k < Module.finrank ℝ E := by
  let y : FixedComponent Q S x := ⟨x, mem_connectedComponentIn hx⟩
  rw [atlas_dimension_eq_fixedTangent_finrank Q S x C y]
  exact fixedTangentSpace_finrank_lt Q hjet S hS y.1
    (connectedComponentIn_subset _ _ y.2)

/-- The actual connected fixed subset admits a strictly lower-dimensional
smooth embedded atlas. The bound is proved from effectiveness and one-jet
rigidity, not included in the fixed-submanifold literature input. -/
theorem exists_fixedComponentAtlas_dimension_lt [T2Space M]
    [SecondCountableTopology M] [PreconnectedSpace M]
    (hjet : RiemannianOneJetRigidityOnModel (E := E) (M := M))
    (hfixed : RiemannianFixedComponentOnModel (E := E) (M := M))
    (S : Subgroup (QuaternionicIsometries Q)) (hS : ∃ f ∈ S, f ≠ 1)
    (x : M) (hx : x ∈ fixedPoints Q S) :
    ∃ k : ℕ, k < Module.finrank ℝ E ∧ Nonempty (FixedComponentAtlas Q S x k) := by
  obtain ⟨k, ⟨C⟩⟩ := hfixed Q S x hx
  exact ⟨k, atlas_dimension_lt Q hjet S hS x hx C, ⟨C⟩⟩

theorem exists_connectedKernelFixedComponentAtlas_dimension_lt [T2Space M]
    [SecondCountableTopology M] [PreconnectedSpace M]
    (hjet : RiemannianOneJetRigidityOnModel (E := E) (M := M))
    (hfixed : RiemannianFixedComponentOnModel (E := E) (M := M))
    {r : ℕ} (A : ContinuousTorusAction Q r) (hA : A.Faithful)
    (hr : 2 ≤ r) (μ : Fin r → ℤ) (hμ : μ ≠ 0)
    (x : M) (hx : x ∈ ContinuousTorusAction.connectedKernelFixedSet Q A μ) :
    ∃ k : ℕ, k < Module.finrank ℝ E ∧ Nonempty (FixedComponentAtlas Q
      (ContinuousTorusAction.connectedKernelImage Q A μ) x k) := by
  obtain ⟨t, ht, hne⟩ := connectedKernel_has_nonidentity μ hr hμ
  apply exists_fixedComponentAtlas_dimension_lt Q hjet hfixed
    (ContinuousTorusAction.connectedKernelImage Q A μ) ?_ x hx
  refine ⟨A.representation t, ⟨t, ht, rfl⟩, ?_⟩
  intro h
  apply hne
  apply hA
  simpa using h

end
end QuaternionicSymmetry.ManifoldQuaternionicFixedComponentDimension
