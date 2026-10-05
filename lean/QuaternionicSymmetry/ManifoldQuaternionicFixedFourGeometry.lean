import QuaternionicSymmetry.ManifoldQuaternionicFixedPositiveGeometry
import QuaternionicSymmetry.ManifoldQuaternionicFourSubmanifoldInput
import QuaternionicSymmetry.ManifoldQuaternionicFixedSpanInvariant
import QuaternionicSymmetry.ManifoldQuaternionicFixedComponentTopology

/-! Apply the orientation-compatible four-dimensional T4 source to the
actual fixed-component atlas. The fixed tangent invariance, compactness and
connectedness are internal. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicFixedFourGeometry
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldPositiveTwistorCompatibleFourGeometry
open ManifoldQuaternionicFourSubmanifoldInput
open ManifoldQuaternionicSubmanifoldInput
open ManifoldRiemannianFixedComponentInput
open ManifoldQuaternionicFixedSpanInvariant
open ManifoldQuaternionicFixedComponentTopology
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryCoefficients
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T3Space M] [SecondCountableTopology M] [CompactSpace M]

/-- The four-dimensional fixed component carries the actual induced
positive Einstein geometry with the Weyl half compatible with its restricted
quaternionic span and orientation. This applies only when the kernel acts
trivially on that span throughout the component. -/
theorem exists_induced_compact_four_geometry
    (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (S : Subgroup (QuaternionicIsometries P.tangent)) (x : M)
    (C : FixedComponentAtlas P.tangent S x 4)
    (hQ : ∀ y : FixedComponent P.tangent S x, ∀ f ∈ S,
      ∀ a : Fin 3 → ℝ, coefficientAction P.tangent f y.1 a = a)
    (hT4four : PositiveFourQuaternionicSubmanifoldSource) :
    ∃ C' : FixedComponentAtlas P.tangent S x 4,
    letI := C'.charts
    letI := C'.manifold
    ∃ R : CompactConnectedPositiveTwistorCompatibleFourGeometry
        (E := EuclideanSpace ℝ (Fin 4)) (M := FixedComponent P.tangent S x),
      IsInducedQuaternionicGeometry P
        R.toPositiveTwistorCompatibleFourGeometry.toPositiveQuaternionicKahlerGeometry
        Subtype.val := by
  letI := C.charts
  letI := C.manifold
  letI : SecondCountableTopology (FixedComponent P.tangent S x) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  have hRange : QuaternionicTangentRange (F := EuclideanSpace ℝ (Fin 4))
      P (Subtype.val : FixedComponent P.tangent S x → M) := by
    intro y B hB v hv
    rw [C.tangent_eq] at hv ⊢
    exact fixedTangentSpace_span_mem P.tangent S y.1
      (connectedComponentIn_subset _ _ y.2) (hQ y) B hB v hv
  obtain ⟨B,R,hR⟩ := hT4four P n hn hDim (by simp)
    Subtype.val C.inclusion_smooth Topology.IsEmbedding.subtypeVal
      C.inclusion_injective_derivative hRange
  letI := B.charts
  letI := B.manifold
  letI := compactComponent P.tangent S x
  letI := preconnectedComponent P.tangent S x
  exact ⟨ManifoldQuaternionicFixedPositiveGeometry.refinedFixedComponentAtlas
    P S x 4 C B, ⟨R,isCompact_univ,isPreconnected_univ⟩,hR⟩

end
end QuaternionicSymmetry.ManifoldQuaternionicFixedFourGeometry
