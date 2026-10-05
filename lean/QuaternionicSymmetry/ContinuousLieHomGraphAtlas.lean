import QuaternionicSymmetry.GeneralClosedSubgroupLieSource
import QuaternionicSymmetry.GeneralSmoothMapSource
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-! First internal step toward automatic real smoothness of a continuous
homomorphism of finite-dimensional Lie groups: its literal graph is a
closed subgroup of the product and receives Lee's embedded Lie atlas.
No new automatic-smoothness literature source is postulated. -/

namespace QuaternionicSymmetry.ContinuousLieHomGraphAtlas

open GeneralClosedSubgroupLieSource Topology
open scoped Manifold ContDiff
noncomputable section

variable {E F G H : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [SecondCountableTopology G]
  [ChartedSpace E G] [IsManifold 𝓘(ℝ,E) ∞ G] [LieGroup 𝓘(ℝ,E) ∞ G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [T2Space H] [SecondCountableTopology H]
  [ChartedSpace F H] [IsManifold 𝓘(ℝ,F) ∞ H] [LieGroup 𝓘(ℝ,F) ∞ H]
  (f : G →* H)

def graphHom : G →* G × H where
  toFun g := (g, f g)
  map_one' := by simp
  map_mul' g h := by simp

theorem graphHom_isClosedEmbedding (hf : Continuous f) :
    IsClosedEmbedding (graphHom f) := by
  have he : IsEmbedding (fun g : G => (g, f g)) := isEmbedding_graph hf
  have hc : IsClosed {p : G × H | f p.1 = p.2} :=
    isClosed_eq (hf.comp continuous_fst) continuous_snd
  refine ⟨he, ?_⟩
  convert hc using 1
  ext p
  constructor
  · rintro ⟨g, rfl⟩
    rfl
  · intro hp
    exact ⟨p.1, Prod.ext rfl hp⟩

theorem exists_graphLieAtlas
    (hLee : LeeClosedEmbeddingTheorem) (hf : Continuous f) :
    letI : ChartedSpace (E × F) (G × H) := prodChartedSpace E G F H
    ∃ d : ℕ,
      Nonempty (EmbeddedRealLieAtlas (E × F) G (G × H)
        (graphHom f) d) := by
  letI : ChartedSpace (E × F) (G × H) := prodChartedSpace E G F H
  letI : IsManifold 𝓘(ℝ,E × F) ∞ (G × H) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod G H
  letI : LieGroup 𝓘(ℝ,E × F) ∞ (G × H) := by
    rw [modelWithCornersSelf_prod]
    exact Prod.instLieGroup
  exact hLee (graphHom f) (graphHom_isClosedEmbedding f hf)

end
end QuaternionicSymmetry.ContinuousLieHomGraphAtlas
