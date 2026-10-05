import QuaternionicSymmetry.ManifoldRiemannianFixedComponentInput

/-! The actual fixed-component subtype is preconnected, and is compact
when the ambient manifold is compact Hausdorff. No atlas or curvature input
is needed for these topological facts. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFixedComponentTopology

open ManifoldQuaternionicSpanSymmetry ManifoldRiemannianFixedComponentInput
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (S : Subgroup (QuaternionicIsometries Q)) (x : M)

def preconnectedComponent : PreconnectedSpace (FixedComponent Q S x) :=
  isPreconnected_iff_preconnectedSpace.mp isPreconnected_connectedComponentIn

def connectedComponent (hx : x ∈ fixedPoints Q S) :
    ConnectedSpace (FixedComponent Q S x) :=
  isConnected_iff_connectedSpace.mp (isConnected_connectedComponentIn_iff.mpr hx)

theorem isCompact_component [T2Space M] [CompactSpace M] :
    IsCompact (connectedComponentIn (fixedPoints Q S) x) := by
  let F := fixedPoints Q S
  letI : CompactSpace F :=
    isCompact_iff_compactSpace.mp (isClosed_fixedPoints Q S).isCompact
  by_cases hx : x ∈ F
  · rw [connectedComponentIn_eq_image hx]
    exact isClosed_connectedComponent.isCompact.image continuous_subtype_val
  · rw [connectedComponentIn_eq_empty hx]
    exact isCompact_empty

def compactComponent [T2Space M] [CompactSpace M] :
    CompactSpace (FixedComponent Q S x) :=
  isCompact_iff_compactSpace.mp (isCompact_component Q S x)

end
end QuaternionicSymmetry.ManifoldQuaternionicFixedComponentTopology
