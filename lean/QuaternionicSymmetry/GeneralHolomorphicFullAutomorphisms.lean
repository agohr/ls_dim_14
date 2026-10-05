import QuaternionicSymmetry.GeneralHolomorphicDistributionAutomorphismTopology

/-! The full biholomorphism group in the same actual compact-open
forward/inverse framework as the contact subgroup. This is a group of
genuine complex-manifold maps, not an algebraic/Lie-group structure. -/

namespace QuaternionicSymmetry.GeneralHolomorphicFullAutomorphisms

open GeneralHolomorphicDistributionAutomorphisms
open GeneralHolomorphicDistributionAutomorphismTopology
open scoped Manifold ContDiff
noncomputable section

variable {V Z : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace Z] [ChartedSpace V Z] [IsManifold 𝓘(ℂ,V) ∞ Z]

def fullDistribution (_ : Z) : Submodule ℂ V := ⊤

abbrev HolomorphicAutomorphisms (V Z : Type*) [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace Z] [ChartedSpace V Z]
    [IsManifold 𝓘(ℂ,V) ∞ Z] :=
  Automorphisms (fullDistribution (V := V) (Z := Z))

def forgetDistribution (D : Z → Submodule ℂ V) :
    Automorphisms D →* HolomorphicAutomorphisms V Z where
  toFun f := ⟨f.1, by
    constructor <;> intro z v hv <;> trivial⟩
  map_one' := by
    apply Subtype.ext
    rfl
  map_mul' := by
    intro f g
    apply Subtype.ext
    rfl

theorem forgetDistribution_injective (D : Z → Submodule ℂ V) :
    Function.Injective (forgetDistribution D) := by
  intro f g h
  apply Subtype.ext
  exact congrArg (fun q : HolomorphicAutomorphisms V Z => q.1) h

theorem forgetDistribution_continuous (D : Z → Submodule ℂ V) :
    Continuous (forgetDistribution D) := by
  apply (mapPair_isEmbedding (fullDistribution (V := V) (Z := Z))).isInducing.continuous_iff.mpr
  exact continuous_mapPair D

end
end QuaternionicSymmetry.GeneralHolomorphicFullAutomorphisms
