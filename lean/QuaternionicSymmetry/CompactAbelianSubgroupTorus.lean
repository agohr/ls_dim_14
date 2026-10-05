import QuaternionicSymmetry.CompactAbelianLieTorus
import Mathlib.Topology.Algebra.Group.Basic

/-! The closure of a connected abelian subgroup of a compact real Lie group
is an actual torus. The only external premise is the existing closed-subgroup
Lie-atlas theorem. -/
namespace QuaternionicSymmetry.CompactAbelianSubgroupTorus
open CompactLieTorusInputs GeneralClosedSubgroupLieSource
open scoped Manifold ContDiff
noncomputable section
variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup 𝓘(ℝ,E) ∞ G] [CompactSpace G] [T2Space G] [SecondCountableTopology G]

include E in
theorem closure_isTorus (hClosed : LeeClosedEmbeddingTheorem)
    (S : Subgroup G) (hc : IsConnected (S : Set G))
    (hab : ∀ x y : S, x*y = y*x) :
    letI := topologicalGroup_of_lieGroup 𝓘(ℝ,E) ∞ (G := G)
    IsTorusSubgroup G S.topologicalClosure := by
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ,E) ∞
  let K := S.topologicalClosure
  letI : CommGroup K := S.commGroupTopologicalClosure hab
  letI : CompactSpace K := isCompact_iff_compactSpace.mp S.isClosed_topologicalClosure.isCompact
  letI : ConnectedSpace K := Subtype.connectedSpace hc.closure
  obtain ⟨d,⟨B⟩⟩ := hClosed (E := E) K.subtype
    S.isClosed_topologicalClosure.isClosedEmbedding_subtypeVal
  letI := B.charts
  letI := B.manifold
  letI := B.lieGroup
  letI : SecondCountableTopology K :=
    ChartedSpace.secondCountable_of_sigmaCompact (Fin d → ℝ) _
  obtain ⟨r,T,hT⟩ := CompactAbelianLieTorus.isTorus_top (E := Fin d → ℝ) (G := K) hClosed
  let U : TorusEmbedding G r := {
    hom := K.subtype.comp T.hom
    continuous_hom := continuous_subtype_val.comp T.continuous_hom
    injective_hom := Subtype.val_injective.comp T.injective_hom }
  refine ⟨r,U,?_⟩
  ext g
  constructor
  · rintro ⟨t,rfl⟩
    exact (T.hom t).property
  · intro hg
    obtain ⟨t,ht⟩ := MonoidHom.range_eq_top.mp hT (⟨g,hg⟩ : K)
    exact ⟨t,congrArg Subtype.val ht⟩

end
end QuaternionicSymmetry.CompactAbelianSubgroupTorus
