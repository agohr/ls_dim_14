import QuaternionicSymmetry.CompactActionFixedComponentManifold

/-! A reusable fixed-component atlas with its exact derivative-fixed tangent
range, constructed from compactness and smooth action alone. -/
namespace QuaternionicSymmetry.CompactActionFixedComponent
open Set MeasureTheory CompactActionFixedTangent
open scoped Manifold ContDiff
noncomputable section

variable {A E H K M : Type}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]
  [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [ChartedSpace A K] [IsManifold 𝓘(ℝ,A) ∞ K] [LieGroup 𝓘(ℝ,A) ∞ K]

abbrev fixedSet (a : K × M → M) : Set M := {x | ∀ g, a (g,x) = x}
abbrev Component (a : K × M → M) (x : M) := ↥(connectedComponentIn (fixedSet a) x)

structure Atlas (a : K × M → M) (x : M) (k : ℕ) where
  charts : ChartedSpace (EuclideanSpace ℝ (Fin k)) (Component a x)
  manifold : letI := charts; IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) ∞ (Component a x)
  inclusion_smooth : letI := charts
    ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) I ∞ (Subtype.val : Component a x → M)
  inclusion_injective_derivative : letI := charts
    ∀ y, Function.Injective (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) I
      (Subtype.val : Component a x → M) y)
  tangent_eq : letI := charts
    ∀ y, LinearMap.range (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) I
      (Subtype.val : Component a x → M) y).toLinearMap = fixedDerivatives (I := I) a y.1

lemma exists_atlas [T2Space K]
    (a : K × M → M) (ha : ContMDiff (𝓘(ℝ,A).prod I) I ∞ a)
    (h1 : ∀ x, a (1,x) = x)
    (hmul : ∀ g h x, a (g,a (h,x)) = a (g*h,x))
    (x : M) (hx : x ∈ fixedSet a) : ∃ k, Nonempty (Atlas (I := I) a x k) := by
  letI : MeasurableSpace K := borel K
  letI : BorelSpace K := ⟨rfl⟩
  let ν : Measure K := (Measure.haar : Measure K).inv
  let μ : Measure K := (ν univ)⁻¹ • ν
  obtain ⟨k,c,hm,hi,hdi,ht⟩ :=
    CompactActionFixedComponentManifold.exists_fixed_component_manifold μ a ha h1 hmul x hx
  exact ⟨k,⟨⟨c,hm,hi,hdi,ht⟩⟩⟩

end
end QuaternionicSymmetry.CompactActionFixedComponent
