import QuaternionicSymmetry.QuaternionicTorusWeightKernel

/-! A nonzero weight kernel in a faithful rank-at-least-two torus action
has a proper fixed locus on the actual quaternionic manifold. This does
not yet identify the locus as a submanifold or prove its dimension drop. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicProperKernelFixedSet

open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicTorusAction
open QuaternionicTorusWeightKernel
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem exists_moved_point (f : QuaternionicIsometries Q) (hf : f ≠ 1) :
    ∃ x : M, f • x ≠ x := by
  classical
  by_contra h
  apply hf
  apply Subtype.ext
  apply Diffeomorph.ext
  intro x
  simpa using not_exists.mp h x

theorem fixedPoints_ne_univ (S : Subgroup (QuaternionicIsometries Q))
    (hS : ∃ f ∈ S, f ≠ 1) : fixedPoints Q S ≠ Set.univ := by
  obtain ⟨f, hfS, hf⟩ := hS
  obtain ⟨x, hx⟩ := exists_moved_point Q f hf
  intro h
  have hxS : x ∈ fixedPoints Q S := by rw [h]; trivial
  exact hx (hxS f hfS)

theorem connectedKernelFixedSet_ne_univ {r : ℕ}
    (A : ContinuousTorusAction Q r) (hA : A.Faithful)
    (hr : 2 ≤ r) (μ : Fin r → ℤ) (hμ : μ ≠ 0) :
    ContinuousTorusAction.connectedKernelFixedSet Q A μ ≠ Set.univ := by
  obtain ⟨t, ht, hne⟩ := connectedKernel_has_nonidentity μ hr hμ
  apply fixedPoints_ne_univ
  refine ⟨A.representation t, ⟨t, ht, rfl⟩, ?_⟩
  intro h
  apply hne
  apply hA
  simpa using h

theorem connectedKernelFixedComponent_ne_univ {r : ℕ}
    (A : ContinuousTorusAction Q r) (hA : A.Faithful)
    (hr : 2 ≤ r) (μ : Fin r → ℤ) (hμ : μ ≠ 0) (x : M) :
    ContinuousTorusAction.connectedKernelFixedComponent Q A μ x ≠ Set.univ := by
  intro h
  apply connectedKernelFixedSet_ne_univ Q A hA hr μ hμ
  apply Set.eq_univ_of_univ_subset
  rw [← h]
  exact ContinuousTorusAction.fixedComponent_subset_fixedSet Q A μ x

end
end QuaternionicSymmetry.ManifoldQuaternionicProperKernelFixedSet
