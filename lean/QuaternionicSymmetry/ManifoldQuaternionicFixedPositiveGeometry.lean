import QuaternionicSymmetry.ManifoldQuaternionicFixedSpanInvariant
import QuaternionicSymmetry.ManifoldQuaternionicFixedComponentTopology

/-! Apply T4 with a compatible choice of fixed-component charts. The tangent invariance, topology and compactness are checked here;
the induced metric is tied to the genuine inclusion. The chosen atlas may
be refined to admit local quaternionic frames. The four-dimensional
case is intentionally excluded. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicFixedPositiveGeometry

open ManifoldPositiveQuaternionicKahlerGeometry ManifoldQuaternionicSpanSymmetry
open ManifoldRiemannianFixedComponentInput
open ManifoldQuaternionicSubmanifoldInput ManifoldQuaternionicFixedSpanInvariant
open ManifoldQuaternionicIsometryCoefficients
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T3Space M] [SecondCountableTopology M]

/-- Rechoose fixed-component charts while retaining its actual inclusion and
fixed tangent spaces. Compatibility is recorded by the supplied atlas. -/
def refinedFixedComponentAtlas
    (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (S : Subgroup (QuaternionicIsometries P.tangent)) (x : M) (k : ℕ)
    (C : FixedComponentAtlas P.tangent S x k)
    (B : letI := C.charts; letI := C.manifold
      CompatibleSubmanifoldAtlas (E := E) (F := EuclideanSpace ℝ (Fin k)) C.charts
        (Subtype.val : FixedComponent P.tangent S x → M)) :
    FixedComponentAtlas P.tangent S x k := by
  letI := C.charts
  letI := C.manifold
  exact {
    charts := B.charts
    manifold := B.manifold
    inclusion_smooth := B.inclusion_smooth
    inclusion_injective_derivative := B.inclusion_injective_derivative
    tangent_eq := fun y => (B.tangent_range y).trans (C.tangent_eq y) }

theorem exists_induced_positive_geometry
    (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hDim : Module.finrank ℝ E = 4*n)
    (S : Subgroup (QuaternionicIsometries P.tangent)) (x : M)
    (C : FixedComponentAtlas P.tangent S x (4*m))
    (hQ : ∀ y : FixedComponent P.tangent S x, ∀ f ∈ S,
      ∀ a : Fin 3 → ℝ, coefficientAction P.tangent f y.1 a = a)
    (hT4 : PositiveQuaternionicSubmanifoldSource) :
    ∃ C' : FixedComponentAtlas P.tangent S x (4*m),
    letI : NeZero (4*m) := ⟨by omega⟩
    letI := C'.charts
    letI := C'.manifold
    ∃ R : PositiveQuaternionicKahlerGeometry
        (E := EuclideanSpace ℝ (Fin (4*m))) (M := FixedComponent P.tangent S x),
      IsInducedQuaternionicGeometry P R Subtype.val := by
  letI : NeZero (4*m) := ⟨by omega⟩
  letI := C.charts
  letI := C.manifold
  letI : SecondCountableTopology (FixedComponent P.tangent S x) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  have hRange : QuaternionicTangentRange (F := EuclideanSpace ℝ (Fin (4*m)))
      P (Subtype.val : FixedComponent P.tangent S x → M) := by
    intro y B hB v hv
    rw [C.tangent_eq] at hv ⊢
    exact fixedTangentSpace_span_mem P.tangent S y.1
      (connectedComponentIn_subset _ _ y.2) (hQ y) B hB v hv
  obtain ⟨B,R,hR⟩ := hT4 P n m hn hm hDim (by simp) Subtype.val
    C.inclusion_smooth Topology.IsEmbedding.subtypeVal C.inclusion_injective_derivative hRange
  exact ⟨refinedFixedComponentAtlas P S x (4*m) C B, R, hR⟩

/-- Compactness and connectedness come from the actual fixed subset,
not from the T4 literature premise. -/
theorem exists_induced_compact_positive_geometry [CompactSpace M]
    (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hDim : Module.finrank ℝ E = 4*n)
    (S : Subgroup (QuaternionicIsometries P.tangent)) (x : M)
    (C : FixedComponentAtlas P.tangent S x (4*m))
    (hQ : ∀ y : FixedComponent P.tangent S x, ∀ f ∈ S,
      ∀ a : Fin 3 → ℝ, coefficientAction P.tangent f y.1 a = a)
    (hT4 : PositiveQuaternionicSubmanifoldSource) :
    ∃ C' : FixedComponentAtlas P.tangent S x (4*m),
    letI : NeZero (4*m) := ⟨by omega⟩
    letI := C'.charts
    letI := C'.manifold
    ∃ R : CompactConnectedPositiveQuaternionicKahlerGeometry
        (E := EuclideanSpace ℝ (Fin (4*m))) (M := FixedComponent P.tangent S x),
      IsInducedQuaternionicGeometry P R.toPositiveQuaternionicKahlerGeometry
        Subtype.val := by
  letI : NeZero (4*m) := ⟨by omega⟩
  letI := C.charts
  letI := C.manifold
  obtain ⟨C', R, hR⟩ := exists_induced_positive_geometry P n m hn hm hDim S x C hQ hT4
  letI := C'.charts
  letI := C'.manifold
  letI := ManifoldQuaternionicFixedComponentTopology.compactComponent P.tangent S x
  letI := ManifoldQuaternionicFixedComponentTopology.preconnectedComponent P.tangent S x
  exact ⟨C', ⟨R, isCompact_univ, isPreconnected_univ⟩, hR⟩

end
end QuaternionicSymmetry.ManifoldQuaternionicFixedPositiveGeometry
