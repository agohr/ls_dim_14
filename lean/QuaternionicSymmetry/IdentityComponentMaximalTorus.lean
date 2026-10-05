import QuaternionicSymmetry.CompactLieTorusMaximalTransfer

/-! The actual identity-component Lie atlas yields a maximal torus of
rank at least two in the full compact isometry group, not merely a
nonmaximal coordinate two-torus. -/

namespace QuaternionicSymmetry.IdentityComponentMaximalTorus

open CompactLieTorusInputs IdentityComponentLie
open CompactLieTorusMaximalTransfer
open scoped Manifold ContDiff
noncomputable section

variable (V G : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace V G]

/-- The existence input alone gives a positive-rank maximal torus in the
full group; any stronger rank bound can be checked after this choice. -/
theorem exists_full_maximal_torus_of_dimension_pos
    [FiniteDimensional ℝ V] [LieGroup 𝓘(ℝ,V) ∞ G]
    [CompactSpace G] [T2Space G] [SecondCountableTopology G]
    (hTorus : letI := IdentityComponentLie.charts V G
      MaximalTorusExistenceOnModel (V := V) (Component G))
    (hdim : 0 < Module.finrank ℝ V) :
    ∃ r : ℕ, 0 < r ∧ ∃ T : TorusEmbedding G r, T.IsMaximal G := by
  letI := IdentityComponentLie.charts V G
  letI := IdentityComponentLie.manifold V G
  letI := IdentityComponentLie.lieGroup V G
  letI := IdentityComponentLie.connected G
  letI := IdentityComponentLie.compact G
  letI : SecondCountableTopology (Component G) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  obtain ⟨r,hr,T,hMax⟩ := hTorus hdim
  let Tfull : TorusEmbedding G r := {
    hom := (Component G).subtype.comp T.hom
    continuous_hom := continuous_subtype_val.comp T.continuous_hom
    injective_hom := Subtype.val_injective.comp T.injective_hom }
  exact ⟨r,hr,Tfull,maximal_in_full_of_component G T hMax⟩

theorem exists_full_maximal_torus_of_dimension_gt_three
    [FiniteDimensional ℝ V] [LieGroup 𝓘(ℝ,V) ∞ G]
    [CompactSpace G] [T2Space G] [SecondCountableTopology G]
    (hTorus : letI := IdentityComponentLie.charts V G
      MaximalTorusExistenceOnModel (V := V) (Component G))
    (hRankOne : letI := IdentityComponentLie.charts V G
      CompactRankOneDimensionOnModel (V := V) (Component G))
    (hdim : 3 < Module.finrank ℝ V) :
    ∃ r : ℕ, 2 ≤ r ∧ ∃ T : TorusEmbedding G r, T.IsMaximal G := by
  letI := IdentityComponentLie.charts V G
  letI := IdentityComponentLie.manifold V G
  letI := IdentityComponentLie.lieGroup V G
  letI := IdentityComponentLie.connected G
  letI := IdentityComponentLie.compact G
  letI : SecondCountableTopology (Component G) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  obtain ⟨r,hr,T,hMax⟩ := hTorus (by omega)
  have hr2 : 2 ≤ r := by
    have hne : r ≠ 1 := by
      intro heq
      subst r
      have hBound := hRankOne T hMax
      omega
    omega
  let Tfull : TorusEmbedding G r := {
    hom := (Component G).subtype.comp T.hom
    continuous_hom := continuous_subtype_val.comp T.continuous_hom
    injective_hom := Subtype.val_injective.comp T.injective_hom }
  exact ⟨r,hr2,Tfull,maximal_in_full_of_component G T hMax⟩

end
end QuaternionicSymmetry.IdentityComponentMaximalTorus
