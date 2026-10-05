import QuaternionicSymmetry.CompactLieTorusInputs
import QuaternionicSymmetry.GeneralClosedSubgroupLieSource
import QuaternionicSymmetry.ManifoldImmersionSmooth

/-! The SAME selected compact torus embedding receives a genuine real Lie
atlas from the registered closed-subgroup theorem, and its given
parametrization is smooth in that atlas. The source dimension is
existential and no claim that it equals the written rank is made here. -/

namespace QuaternionicSymmetry.SelectedTorusEmbeddedLieAtlas

open CompactLieTorusInputs GeneralClosedSubgroupLieSource
open scoped Manifold ContDiff
noncomputable section

variable {V G : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [Group G] [TopologicalSpace G] [T2Space G]
  [SecondCountableTopology G]
  [ChartedSpace V G] [IsManifold 𝓘(ℝ,V) ∞ G]
  [LieGroup 𝓘(ℝ,V) ∞ G]
  {r : ℕ} (T : TorusEmbedding G r)

theorem exists_selected_embedded_atlas
    (hLee : LeeClosedEmbeddingTheorem) :
    ∃ d : ℕ,
      Nonempty (EmbeddedRealLieAtlas V (Fin r → Circle) G T.hom d) := by
  exact hLee T.hom T.isClosedEmbedding

theorem selected_hom_smooth
    {d : ℕ}
    (g : EmbeddedRealLieAtlas V (Fin r → Circle) G T.hom d) :
    letI : ChartedSpace (Fin d → ℝ) (Fin r → Circle) := g.charts
    ContMDiff 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,V) ∞ T.hom := by
  letI : ChartedSpace (Fin d → ℝ) (Fin r → Circle) := g.charts
  letI : IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Fin r → Circle) := g.manifold
  exact ManifoldImmersionSmooth.smoothEmbedding_contMDiff g.smoothEmbedding

end
end QuaternionicSymmetry.SelectedTorusEmbeddedLieAtlas
