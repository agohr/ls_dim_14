import QuaternionicSymmetry.CompactActionFixedComponent
import QuaternionicSymmetry.SmoothActionFixedClosure
import QuaternionicSymmetry.GeneralClosedSubgroupLieSource
import QuaternionicSymmetry.ManifoldImmersionSmooth

/-! Every subgroup of a compact smooth Lie action has smooth fixed components.
The retained closed-subgroup theorem supplies a Lie atlas on its closure. -/
namespace QuaternionicSymmetry.CompactSubgroupFixedComponent
open Set CompactActionFixedTangent SmoothActionFixedClosure
open scoped Manifold ContDiff
noncomputable section
set_option maxHeartbeats 800000

variable {A E H G M : Type}
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [SecondCountableTopology G]
  [ChartedSpace A G] [IsManifold 𝓘(ℝ,A) ∞ G] [LieGroup 𝓘(ℝ,A) ∞ G]

abbrev fixedSet (a : G × M → M) (S : Subgroup G) : Set M :=
  {x | ∀ g ∈ S, a (g,x) = x}
abbrev Component (a : G × M → M) (S : Subgroup G) (x : M) :=
  ↥(connectedComponentIn (fixedSet a S) x)

structure Atlas (a : G × M → M) (S : Subgroup G) (x : M) (k : ℕ) where
  charts : ChartedSpace (EuclideanSpace ℝ (Fin k)) (Component a S x)
  manifold : letI := charts; IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) ∞ (Component a S x)
  inclusion_smooth : letI := charts
    ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) I ∞ (Subtype.val : Component a S x → M)
  inclusion_injective_derivative : letI := charts
    ∀ y, Function.Injective (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) I
      (Subtype.val : Component a S x → M) y)
  tangent_eq : letI := charts
    ∀ y v, v ∈ LinearMap.range (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) I
      (Subtype.val : Component a S x → M) y).toLinearMap ↔
      ∀ g ∈ S, mfderiv I I (fun z => a (g,z)) y.1 v = v

lemma exists_atlas
    (hLee : GeneralClosedSubgroupLieSource.LeeClosedEmbeddingTheorem)
    (a : G × M → M) (ha : ContMDiff (𝓘(ℝ,A).prod I) I ∞ a)
    (h1 : ∀ x, a (1,x) = x)
    (hmul : ∀ g h x, a (g,a (h,x)) = a (g*h,x))
    (S : Subgroup G) (x : M) (hx : x ∈ fixedSet a S) :
    ∃ k, Nonempty (Atlas (I := I) a S x k) := by
  let K := S.topologicalClosure
  letI : CompactSpace K := isCompact_iff_compactSpace.mp S.isClosed_topologicalClosure.isCompact
  have hcl : Topology.IsClosedEmbedding K.subtype := S.isClosed_topologicalClosure.isClosedEmbedding_subtypeVal
  obtain ⟨d,⟨B⟩⟩ := hLee (E := A) K.subtype hcl
  letI := B.charts
  letI := B.manifold
  letI := B.lieGroup
  have hi := ManifoldImmersionSmooth.smoothEmbedding_contMDiff B.smoothEmbedding
  let b : K × M → M := fun p => a (p.1.1,p.2)
  have hb : ContMDiff ((𝓘(ℝ,Fin d → ℝ)).prod I) I ∞ b :=
    ha.comp ((hi.comp contMDiff_fst).prodMk contMDiff_snd)
  have hsets : CompactActionFixedComponent.fixedSet b = fixedSet a S := by
    ext y
    exact (Subtype.forall.trans (fixed_points_closure_iff a ha S y))
  have hxb : x ∈ CompactActionFixedComponent.fixedSet b := by rwa [hsets]
  obtain ⟨k,⟨C⟩⟩ := CompactActionFixedComponent.exists_atlas b hb h1
    (fun g h y => hmul g.1 h.1 y) x hxb
  have hc : CompactActionFixedComponent.Component b x = Component a S x := by
    simp only [CompactActionFixedComponent.Component,Component,hsets]
  -- Transport the charted subset along the literal equality of fixed sets.
  have htransport : ∀ (T : Set M), T = CompactActionFixedComponent.fixedSet b →
      ∃ (c : ChartedSpace (EuclideanSpace ℝ (Fin k)) (↥(connectedComponentIn T x))),
        letI := c
        IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) ∞ (↥(connectedComponentIn T x)) ∧
        ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) I ∞
          (Subtype.val : (↥(connectedComponentIn T x)) → M) ∧
        (∀ y, Function.Injective (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) I
          (Subtype.val : (↥(connectedComponentIn T x)) → M) y)) ∧
        ∀ y v, v ∈ LinearMap.range (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) I
          (Subtype.val : (↥(connectedComponentIn T x)) → M) y).toLinearMap ↔
          ∀ g : K, mfderiv I I (fun z => b (g,z)) y.1 v = v := by
    intro T hT
    subst T
    refine ⟨C.charts,C.manifold,C.inclusion_smooth,C.inclusion_injective_derivative,?_⟩
    intro y v
    rw [C.tangent_eq]
    rfl
  obtain ⟨c,hm,hi,hdi,ht⟩ := htransport (fixedSet a S) hsets.symm
  refine ⟨k,⟨⟨c,hm,hi,hdi,?_⟩⟩⟩
  intro y v
  rw [ht y v]
  exact Subtype.forall.trans (fixed_derivatives_closure_iff a ha S y.1
    (connectedComponentIn_subset _ _ y.2) v)

end
end QuaternionicSymmetry.CompactSubgroupFixedComponent
