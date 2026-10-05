import QuaternionicSymmetry.GeneralHolomorphicDistributionAutomorphismTopology
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-! The actual compact-open forward/inverse topology on holomorphic
automorphisms is second countable when the underlying complex manifold is
locally compact and second countable. This is inherited from the compact-
open continuous-map space, not asserted by the BWW Lie atlas. -/

namespace QuaternionicSymmetry.GeneralHolomorphicAutomorphismSecondCountable

open GeneralHolomorphicDistributionAutomorphisms
open GeneralHolomorphicDistributionAutomorphismTopology
open Topology
open scoped Manifold ContDiff

variable {V Z : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace Z] [LocallyCompactSpace Z]
  [SecondCountableTopology Z]
  [ChartedSpace V Z] [IsManifold 𝓘(ℂ,V) ∞ Z]
  (D : Z → Submodule ℂ V)

instance : SecondCountableTopology (Automorphisms D) := by
  letI : SecondCountableTopology C(Z,Z) := inferInstance
  exact (mapPair_isEmbedding D).secondCountableTopology

end QuaternionicSymmetry.GeneralHolomorphicAutomorphismSecondCountable
