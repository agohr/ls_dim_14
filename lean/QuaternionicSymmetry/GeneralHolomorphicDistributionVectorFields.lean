import QuaternionicSymmetry.HolomorphicVectorFieldPushforward
import QuaternionicSymmetry.GeneralHolomorphicDistributionAutomorphisms

/-! The actual distribution-preserving biholomorphism group acts on
global holomorphic vector fields by derivative pushforward. -/

namespace QuaternionicSymmetry.GeneralHolomorphicDistributionVectorFields

open HolomorphicVectorFieldPushforward GeneralHolomorphicDistributionAutomorphisms
open scoped Manifold ContDiff
noncomputable section

variable {V Z : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace Z] [ChartedSpace V Z] [IsManifold 𝓘(ℂ, V) ∞ Z]

def representation (D : Z → Submodule ℂ V) :
    Automorphisms D →* Module.End ℂ (Fields (V := V) (Z := Z)) where
  toFun f := pushForwardLinear f.1
  map_one' := pushForwardLinear_refl
  map_mul' f g := pushForwardLinear_trans g.1 f.1

end
end QuaternionicSymmetry.GeneralHolomorphicDistributionVectorFields
