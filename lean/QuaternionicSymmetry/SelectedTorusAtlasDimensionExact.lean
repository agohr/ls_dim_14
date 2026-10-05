import QuaternionicSymmetry.SelectedTorusAtlasDimensionLower

/-! The SAME BG-L3 selected compact torus atlas has exactly its written
rank. Both inequalities are internal: the compact inclusion's tangent
vectors are purely imaginary, and coordinate exponentials give every
imaginary direction. -/

namespace QuaternionicSymmetry.SelectedTorusAtlasDimensionExact

open CompactLieTorusInputs SelectedTorusEmbeddedLieAtlas
open SelectedTorusAtlasDimensionUpper SelectedTorusAtlasDimensionLower
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open scoped Manifold ContDiff
noncomputable section

variable {V G : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [Group G] [TopologicalSpace G] [T2Space G]
  [SecondCountableTopology G]
  [ChartedSpace V G] [IsManifold 𝓘(ℝ,V) ∞ G]
  [LieGroup 𝓘(ℝ,V) ∞ G]
  {r d : ℕ}

theorem selected_atlas_dimension_eq_rank
    (T : TorusEmbedding G r)
    (g : EmbeddedRealLieAtlas V (Fin r → Circle) G T.hom d)
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem) :
    d = r := by
  exact Nat.le_antisymm
    (selected_atlas_dim_le_rank T g hClosed hImm hLee)
    (selected_atlas_rank_le_dim T g hClosed hImm hLee)

end
end QuaternionicSymmetry.SelectedTorusAtlasDimensionExact
