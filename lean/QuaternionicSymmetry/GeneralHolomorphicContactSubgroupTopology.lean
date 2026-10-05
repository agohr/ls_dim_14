import QuaternionicSymmetry.GeneralHolomorphicFullAutomorphisms

/-! The subgroup preserving a holomorphic tangent distribution inherits
exactly the full biholomorphism group's compact-open topology. This is a
topological comparison only, not a complex Lie subgroup theorem. -/

namespace QuaternionicSymmetry.GeneralHolomorphicContactSubgroupTopology

open GeneralHolomorphicDistributionAutomorphisms
open GeneralHolomorphicDistributionAutomorphismTopology
open GeneralHolomorphicFullAutomorphisms
open Topology
open scoped Manifold ContDiff
noncomputable section

variable {V Z : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace Z] [ChartedSpace V Z] [IsManifold 𝓘(ℂ,V) ∞ Z]
  (D : Z → Submodule ℂ V)

/-- The actual contact-preserving automorphism carrier has the subspace
topology from the full automorphism group, not an unrelated group topology. -/
theorem forgetDistribution_isEmbedding :
    IsEmbedding (forgetDistribution D) := by
  let T := fullDistribution (V := V) (Z := Z)
  have hpair : (mapPair T) ∘ (forgetDistribution D) = mapPair D := rfl
  have hcomp : IsEmbedding ((mapPair T) ∘ (forgetDistribution D)) := by
    rw [hpair]
    exact mapPair_isEmbedding D
  exact IsEmbedding.of_comp (forgetDistribution_continuous D)
    (continuous_mapPair T) hcomp

end
end QuaternionicSymmetry.GeneralHolomorphicContactSubgroupTopology
