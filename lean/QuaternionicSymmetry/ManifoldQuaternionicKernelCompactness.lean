import QuaternionicSymmetry.ManifoldQuaternionicProperKernelFixedSet
import QuaternionicSymmetry.ManifoldQuaternionicIsometryTopology

/-! The connected character kernel has compact, closed image in the
actual quaternionic-isometry group. Its fixed components in a compact
manifold are compact connected subsets. No submanifold or dimension
claim is included here. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicKernelCompactness

open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicTorusAction
open ManifoldQuaternionicIsometryTopology QuaternionicTorusWeightKernel
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable {r : ℕ} (A : ContinuousTorusAction Q r) (μ : Fin r → ℤ)

theorem isCompact_connectedKernelImage :
    IsCompact (ContinuousTorusAction.connectedKernelImage Q A μ :
      Set (QuaternionicIsometries Q)) := by
  exact (isCompact_connectedWeightKernel μ).image
    (continuous_representation_of_action Q A.representation A.continuous_action)

theorem isConnected_connectedKernelImage :
    IsConnected (ContinuousTorusAction.connectedKernelImage Q A μ :
      Set (QuaternionicIsometries Q)) := by
  exact (isConnected_connectedWeightKernel μ).image _
    (continuous_representation_of_action Q A.representation
      A.continuous_action).continuousOn

theorem isClosed_connectedKernelImage [T2Space M] :
    IsClosed (ContinuousTorusAction.connectedKernelImage Q A μ :
      Set (QuaternionicIsometries Q)) :=
  (isCompact_connectedKernelImage Q A μ).isClosed

theorem isCompact_connectedKernelFixedSet [T2Space M] [CompactSpace M] :
    IsCompact (ContinuousTorusAction.connectedKernelFixedSet Q A μ) :=
  (ContinuousTorusAction.isClosed_connectedKernelFixedSet Q A μ).isCompact

theorem isCompact_connectedKernelFixedComponent [T2Space M] [CompactSpace M]
    (x : M) :
    IsCompact (ContinuousTorusAction.connectedKernelFixedComponent Q A μ x) := by
  let F := ContinuousTorusAction.connectedKernelFixedSet Q A μ
  letI : CompactSpace F :=
    isCompact_iff_compactSpace.mp (isCompact_connectedKernelFixedSet Q A μ)
  change IsCompact (connectedComponentIn F x)
  by_cases hx : x ∈ F
  · rw [connectedComponentIn_eq_image hx]
    exact isClosed_connectedComponent.isCompact.image continuous_subtype_val
  · rw [connectedComponentIn_eq_empty hx]
    exact isCompact_empty

theorem isConnected_connectedKernelFixedComponent (x : M)
    (hx : x ∈ ContinuousTorusAction.connectedKernelFixedSet Q A μ) :
    IsConnected (ContinuousTorusAction.connectedKernelFixedComponent Q A μ x) :=
  isConnected_connectedComponentIn_iff.mpr hx

end
end QuaternionicSymmetry.ManifoldQuaternionicKernelCompactness
