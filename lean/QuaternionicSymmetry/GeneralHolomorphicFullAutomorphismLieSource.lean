import QuaternionicSymmetry.GeneralHolomorphicFullAutomorphisms
import QuaternionicSymmetry.GeneralHolomorphicAutomorphismSecondCountable
import QuaternionicSymmetry.GeneralCompactHomeomorphismForwardTopology
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-! A precisely scoped general compact-complex transformation-group input.
Kobayashi, *Transformation Groups in Differential Geometry*, Chapter III,
§1, Theorem 1.1, states that the automorphism group of a compact complex
manifold is a complex Lie transformation group. Its topology is the
compact-open transformation-group topology. This contract uses the actual
full biholomorphism group and its already constructed compact-open topology;
it includes joint holomorphic evaluation in the *same* resulting atlas.
It is a literature input, not a Lean proof or a conclusion about any
specific twistor. It is not attributed to BWW 6.6 or NT 1.6. -/

namespace QuaternionicSymmetry.GeneralHolomorphicFullAutomorphismLieSource

open GeneralHolomorphicFullAutomorphisms
open GeneralHolomorphicDistributionAutomorphisms
open GeneralCompactHomeomorphismForwardTopology
open scoped Manifold ContDiff

/-- Kobayashi's compact complex automorphism *transformation* theorem,
expressed on the concrete compact-open full biholomorphism group. -/
def KobayashiCompactAutomorphismTransformation : Prop :=
  ∀ {W Z : Type}
    [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    [TopologicalSpace Z] [T2Space Z] [SecondCountableTopology Z]
    [CompactSpace Z] [PreconnectedSpace Z] [Nonempty Z]
    [ChartedSpace W Z] [IsManifold 𝓘(ℂ,W) ∞ Z],
    ∃ (U : Type) (hNorm : NormedAddCommGroup U),
      letI : NormedAddCommGroup U := hNorm
      ∃ (hSpace : NormedSpace ℂ U) (hFinite : FiniteDimensional ℂ U)
        (hChart : ChartedSpace U (HolomorphicAutomorphisms W Z)),
        letI : NormedSpace ℂ U := hSpace
        letI : FiniteDimensional ℂ U := hFinite
        letI : ChartedSpace U (HolomorphicAutomorphisms W Z) := hChart
        ∃ hManifold : IsManifold 𝓘(ℂ,U) ∞
            (HolomorphicAutomorphisms W Z),
          letI : IsManifold 𝓘(ℂ,U) ∞
            (HolomorphicAutomorphisms W Z) := hManifold
          ∃ hLie : LieGroup 𝓘(ℂ,U) ∞
              (HolomorphicAutomorphisms W Z),
            letI : LieGroup 𝓘(ℂ,U) ∞
              (HolomorphicAutomorphisms W Z) := hLie
            ContMDiff (𝓘(ℂ,U).prod 𝓘(ℂ,W)) 𝓘(ℂ,W) ∞
              (fun p : HolomorphicAutomorphisms W Z × Z => p.1.1 p.2)

/-- The project's forward/inverse pair topology on the literal full
biholomorphism group equals Kobayashi's ordinary forward compact-open
topology when the underlying complex manifold is compact Hausdorff. -/
theorem fullAut_pairTopology_eq_forwardTopology
    {W Z : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [TopologicalSpace Z] [T2Space Z] [CompactSpace Z]
    [ChartedSpace W Z] [IsManifold 𝓘(ℂ,W) ∞ Z] :
    (inferInstance : TopologicalSpace (HolomorphicAutomorphisms W Z)) =
      forwardTopology (fullDistribution (V := W) (Z := Z)) :=
  pairTopology_eq_forwardTopology
    (fullDistribution (V := W) (Z := Z))

end QuaternionicSymmetry.GeneralHolomorphicFullAutomorphismLieSource
