import QuaternionicSymmetry.GeneralHolomorphicContactSubgroupTopology
import Mathlib.Topology.Homeomorph.Lemmas

/-! When every biholomorphism preserves a specified distribution, the
contact and full automorphism groups are literally isomorphic, and the
isomorphism is a homeomorphism for their existing compact-open topologies.
Distribution uniqueness is kept as an explicit hypothesis. -/

namespace QuaternionicSymmetry.GeneralHolomorphicDistributionUniqueFull

open GeneralHolomorphicDistributionAutomorphisms
open GeneralHolomorphicDistributionAutomorphismTopology
open GeneralHolomorphicFullAutomorphisms
open GeneralHolomorphicContactSubgroupTopology Topology
open scoped Manifold ContDiff
noncomputable section

variable {V Z : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace Z] [ChartedSpace V Z] [IsManifold 𝓘(ℂ,V) ∞ Z]
  (D : Z → Submodule ℂ V)

/-- The mathematical content needed from uniqueness: every actual full
biholomorphism preserves the contact distribution in both directions. -/
def AllAutomorphismsPreserve : Prop :=
  ∀ f : HolomorphicAutomorphisms V Z, Preserves D f.1

def rememberDistribution (h : AllAutomorphismsPreserve D) :
    HolomorphicAutomorphisms V Z →* Automorphisms D where
  toFun f := ⟨f.1, h f⟩
  map_one' := by apply Subtype.ext; rfl
  map_mul' := by intro f g; apply Subtype.ext; rfl

/-- The same actual automorphisms, with and without the unique
distribution recorded in their types. -/
def distributionEquivFull (h : AllAutomorphismsPreserve D) :
    Automorphisms D ≃* HolomorphicAutomorphisms V Z where
  toFun := forgetDistribution D
  invFun := rememberDistribution D h
  left_inv f := by apply Subtype.ext; rfl
  right_inv f := by apply Subtype.ext; rfl
  map_mul' := (forgetDistribution D).map_mul

/-- The underlying group isomorphism is compatible with the *existing*
compact-open topologies; no new topology is supplied by uniqueness. -/
def distributionHomeomorphFull (h : AllAutomorphismsPreserve D) :
    Automorphisms D ≃ₜ HolomorphicAutomorphisms V Z :=
  (forgetDistribution_isEmbedding D).toHomeomorphOfSurjective
    (distributionEquivFull D h).surjective

theorem distributionHomeomorphFull_apply (h : AllAutomorphismsPreserve D)
    (f : Automorphisms D) :
    distributionHomeomorphFull D h f = forgetDistribution D f := rfl

end
end QuaternionicSymmetry.GeneralHolomorphicDistributionUniqueFull
