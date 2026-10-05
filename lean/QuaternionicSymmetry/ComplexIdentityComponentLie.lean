import QuaternionicSymmetry.OpenSubgroupComplexLie
import QuaternionicSymmetry.IdentityComponentLie

/-! A finite-dimensional complex Lie group's actual identity component
inherits an open complex Lie atlas. No source or special automorphism-group
assumption is used here. -/

namespace QuaternionicSymmetry.ComplexIdentityComponentLie

open QuaternionicSymmetry.IdentityComponentLie
open scoped Manifold ContDiff
noncomputable section

variable (V G : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace V G]

include V in
theorem isOpen_component : IsOpen (Component G : Set G) := by
  letI : LocallyConnectedSpace G := ChartedSpace.locallyConnectedSpace V G
  exact isOpen_connectedComponent

def charts : ChartedSpace V (Component G) :=
  OpenSubgroupComplexLie.charts (V := V) (Component G)
    (isOpen_component V G)

def manifold [IsManifold 𝓘(ℂ,V) ∞ G] :
    letI := charts V G
    IsManifold 𝓘(ℂ,V) ∞ (Component G) :=
  OpenSubgroupComplexLie.manifold (V := V) (Component G)
    (isOpen_component V G)

def lieGroup [LieGroup 𝓘(ℂ,V) ∞ G] :
    letI := charts V G
    LieGroup 𝓘(ℂ,V) ∞ (Component G) :=
  OpenSubgroupComplexLie.lieGroup (V := V) (Component G)
    (isOpen_component V G)

theorem inclusion_holomorphic :
    letI := charts V G
    ContMDiff 𝓘(ℂ,V) 𝓘(ℂ,V) ∞ (Subtype.val : Component G → G) :=
  OpenSubgroupComplexLie.inclusion_holomorphic (V := V) (Component G)
    (isOpen_component V G)

end
end QuaternionicSymmetry.ComplexIdentityComponentLie
