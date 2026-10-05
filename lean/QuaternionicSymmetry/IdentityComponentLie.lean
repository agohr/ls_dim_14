import QuaternionicSymmetry.OpenSubgroupLie
import QuaternionicSymmetry.CompactLieTorusInputs
import Mathlib.Analysis.Normed.Module.Connected

/-! The actual identity component inherits an open Lie atlas on the same
model vector space. General compact-Lie sources can therefore be applied
to it without assuming connectedness of the full group. -/

namespace QuaternionicSymmetry.IdentityComponentLie

open CompactLieTorusInputs
open scoped Manifold ContDiff
noncomputable section

abbrev Component (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] := Subgroup.connectedComponentOfOne G

variable (V G : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace V G]

include V in
theorem isOpen_component : IsOpen (Component G : Set G) := by
  letI : LocallyConnectedSpace G := ChartedSpace.locallyConnectedSpace V G
  exact isOpen_connectedComponent

def charts : ChartedSpace V (Component G) :=
  OpenSubgroupLie.charts (V := V) (Component G) (isOpen_component V G)

def manifold [IsManifold 𝓘(ℝ,V) ∞ G] :
    letI := charts V G
    IsManifold 𝓘(ℝ,V) ∞ (Component G) :=
  OpenSubgroupLie.manifold (V := V) (Component G) (isOpen_component V G)

def lieGroup [LieGroup 𝓘(ℝ,V) ∞ G] :
    letI := charts V G
    LieGroup 𝓘(ℝ,V) ∞ (Component G) :=
  OpenSubgroupLie.lieGroup (V := V) (Component G) (isOpen_component V G)

def connected : ConnectedSpace (Component G) :=
  isConnected_iff_connectedSpace.mp isConnected_connectedComponent

def compact [CompactSpace G] : CompactSpace (Component G) :=
  isCompact_iff_compactSpace.mp isClosed_connectedComponent.isCompact

theorem inclusion_smooth :
    letI := charts V G
    ContMDiff 𝓘(ℝ,V) 𝓘(ℝ,V) ∞ (Subtype.val : Component G → G) :=
  OpenSubgroupLie.inclusion_smooth (V := V) (Component G) (isOpen_component V G)

/-- The sourced maximal-torus and rank-one theorems apply to the actual
identity component; its rank-two torus is included into the original group.
The full group itself need not be connected. -/
theorem exists_two_torus_of_dimension_gt_three
    [FiniteDimensional ℝ V] [LieGroup 𝓘(ℝ,V) ∞ G]
    [CompactSpace G] [T2Space G] [SecondCountableTopology G]
    (hTorus : letI := charts V G
      MaximalTorusExistenceOnModel (V := V) (Component G))
    (hRankOne : letI := charts V G
      CompactRankOneDimensionOnModel (V := V) (Component G))
    (hdim : 3 < Module.finrank ℝ V) : Nonempty (TorusEmbedding G 2) := by
  letI := charts V G
  letI := manifold V G
  letI := lieGroup V G
  letI := connected G
  letI := compact G
  letI : SecondCountableTopology (Component G) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  obtain ⟨T⟩ := CompactLieTorusInputs.exists_two_torus_of_dimension_gt_three
    (Component G) hTorus hRankOne hdim
  exact ⟨{
    hom := (Component G).subtype.comp T.hom
    continuous_hom := continuous_subtype_val.comp T.continuous_hom
    injective_hom := Subtype.val_injective.comp T.injective_hom }⟩

end
end QuaternionicSymmetry.IdentityComponentLie
